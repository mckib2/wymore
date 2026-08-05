#!/venvs/wymore/bin/python
"""Decide conformance to a compiled dynamics-encoding fragment with a SAT solver.

The bi-implication proved in Lean (`partialDynamicsHom_iff_hom`) says that an
implementation satisfies the fragment compiled from a reference exactly when a
*surjective* triple of maps (h_S, h_I, h_O) satisfies the readout, transition and
autonomous laws of Definition 4.3.  Over finite systems that is a propositional
satisfiability question, so the engineering workflow is:

    reference table + candidate build  ->  CNF  ->  SAT solver
        SAT   : the model *is* the conformance map, discovered not maintained
        UNSAT : the candidate does not realise the reference, and this is a proof

The encoding is one-hot, so what the solver sees is honest CNF that can be written
out as DIMACS; the four clause families of the paper appear one-for-one:

    exactly-one      h_S, h_I, h_O are functions
    readout          ~S[x][s] | O[rho_impl(x)][rho_spec(s)]     (unit if incompatible)
    transition       ~S[x][s] | ~I[i][j] | S[delta_impl(x,i)][delta_spec(s,j)]
    autonomous       ~S[x][s] | S[delta_impl(x,none)][delta_spec(s,none)]
    surjectivity     one clause per reference state, input and output

Scope, stated plainly: the tape is bounded to a fixed window here, so the machine
below is a linear bounded automaton and *not* a Turing machine.  Universality
belongs to the unbounded construction in `Mbse/TuringCoupling.lean`; this is a
finite reference in its own right, sharing the shape of the table but not related
to the unbounded one by a homomorphism.  Deciding existence of a surjective
homomorphism is NP-hard in general (it subsumes surjective graph homomorphism), so
the timings below are feasibility evidence and not a scalability claim.

Usage:
  /venvs/wymore/bin/python scripts/phi_dyn_solver.py
  /venvs/wymore/bin/python scripts/phi_dyn_solver.py --dimacs-dir build/cnf
  /venvs/wymore/bin/python scripts/phi_dyn_solver.py --tex papers/ltl_paper/generated/solver-results.tex
  /venvs/wymore/bin/python scripts/phi_dyn_solver.py --show-clauses tape-vs-instrumented
"""

from __future__ import annotations

import argparse
import itertools
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Hashable, Iterable, Optional

from z3 import Bool, Not, Or, Solver, sat, unsat

State = Hashable
Symbol = Hashable

BLANK = 0
ALPHABET = (0, 1)
CELLS = 2
LABELS = ("q0", "q1")

# ---------------------------------------------------------------------------
# Finite systems
# ---------------------------------------------------------------------------


@dataclass
class System:
    """A finite Wymore discrete system (Definition 2.4) as explicit tables.

    `delta` is total on `states x (inputs + {None})`, mirroring `NZ : SZ -> Option IZ -> SZ`;
    `rho` maps a state to an output or to `None`, mirroring `RZ : SZ -> Option OZ`.
    """

    name: str
    states: tuple[State, ...]
    inputs: tuple[Symbol, ...]
    outputs: tuple[Symbol, ...]
    delta: Callable[[State, Optional[Symbol]], State]
    rho: Callable[[State], Optional[Symbol]]

    def step(self, s: State, i: Optional[Symbol]) -> State:
        return self.delta(s, i)

    def out(self, s: State) -> Optional[Symbol]:
        return self.rho(s)


def reachable(sys: System, start: Iterable[State]) -> tuple[State, ...]:
    """States reachable from `start`; used only to keep generated tables small."""
    seen = list(dict.fromkeys(start))
    frontier = list(seen)
    while frontier:
        s = frontier.pop()
        for i in (None, *sys.inputs):
            t = sys.step(s, i)
            if t not in seen:
                seen.append(t)
                frontier.append(t)
    return tuple(seen)


# ---------------------------------------------------------------------------
# The bounded-window machine: zones, wiring, resultant, reference
# ---------------------------------------------------------------------------

TABLE: dict[tuple[str, Symbol], Optional[tuple[str, Symbol, str]]] = {
    ("q0", 0): ("q1", 1, "R"),
    ("q0", 1): ("q1", 0, "R"),
    ("q1", 0): None,
    ("q1", 1): None,
}
"""The machine table: invert the scanned bit, move right, then halt."""


def _commands() -> tuple[Symbol, ...]:
    """The tape's command port value set: `hold` plus the actions the table can select.

    Declaring the port value set to be exactly the reachable command set is part of
    defining this finite instance; it keeps the encoding small without weakening
    anything, since no other command can ever appear on the wire.
    """
    acts = {("act", w, m) for (_, w, m) in (e for e in TABLE.values() if e is not None)}
    return ("hold",) + tuple(sorted(acts, key=repr))


COMMANDS: tuple[Symbol, ...] = _commands()


def tape_states() -> tuple[State, ...]:
    """Bounded tape: cell contents plus a head index."""
    return tuple(
        (cells, head)
        for cells in itertools.product(ALPHABET, repeat=CELLS)
        for head in range(CELLS)
    )


def tape_apply(t: State, cmd: Symbol) -> State:
    cells, head = t
    if cmd == "hold":
        return t
    _, write, move = cmd
    cells = tuple(write if k == head else c for k, c in enumerate(cells))
    if move == "L":
        head = max(0, head - 1)
    elif move == "R":
        head = min(CELLS - 1, head + 1)
    return (cells, head)


def tape_head(t: State) -> Symbol:
    cells, head = t
    return cells[head]


def ctl_states() -> tuple[State, ...]:
    """Control phases: sense, act (carrying the latched command), halted."""
    return (
        tuple(("sense", q) for q in LABELS)
        + tuple(("act", q, c) for q in LABELS for c in COMMANDS)
        + (("halted",),)
    )


def ctl_cmd(s: State) -> Symbol:
    if s[0] == "act":
        return s[2]
    return "hold"


def ctl_halted(s: State) -> bool:
    return s[0] == "halted"


def ctl_step(s: State, sym: Symbol, load: Optional[str]) -> State:
    if load is not None:
        return ("sense", load)
    if s[0] == "sense":
        entry = TABLE[(s[1], sym)]
        if entry is None:
            return ("halted",)
        q2, write, move = entry
        return ("act", q2, ("act", write, move))
    if s[0] == "act":
        return ("sense", s[1])
    return ("halted",)


LOADS: tuple[Optional[str], ...] = (None,) + LABELS
"""Values on the control's unconnected `load` port: no load, or a label to jump to."""


def tape_zone(name: str = "tape") -> System:
    return System(
        name=name,
        states=tape_states(),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda t, c: t if c is None else tape_apply(t, c),
        rho=tape_head,
    )


def instrumented_tape_zone(modulus: int = 2) -> System:
    """The tape carrying an internal actuation count (bounded to stay finite)."""
    return System(
        name="instrumented-tape",
        states=tuple((t, n) for t in tape_states() for n in range(modulus)),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda tn, c: tn if c is None else (tape_apply(tn[0], c), (tn[1] + 1) % modulus),
        rho=lambda tn: tape_head(tn[0]),
    )


def frozen_tape_zone() -> System:
    """Rejected: accepts commands, never actuates them."""
    return System(
        name="frozen-tape",
        states=tape_states(),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda t, _c: t,
        rho=tape_head,
    )


def blind_tape_zone() -> System:
    """Rejected: actuates correctly, reports a blank window."""
    return System(
        name="blind-tape",
        states=tape_states(),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda t, c: t if c is None else tape_apply(t, c),
        rho=lambda _t: BLANK,
    )


def quiet_tape_zone() -> System:
    """A reference whose window is undefined until the head has moved off the left end.

    This is the only reference in the suite with a closed readout, so it is what exercises
    the fragment's `noOutput` clause family.
    """
    return System(
        name="quiet-tape",
        states=tape_states(),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda t, c: t if c is None else tape_apply(t, c),
        rho=lambda t: None if t[1] == 0 else tape_head(t),
    )


def instrumented_quiet_tape_zone(modulus: int = 2) -> System:
    return System(
        name="instrumented-quiet-tape",
        states=tuple((t, n) for t in tape_states() for n in range(modulus)),
        inputs=COMMANDS,
        outputs=ALPHABET,
        delta=lambda tn, c: tn if c is None else (tape_apply(tn[0], c), (tn[1] + 1) % modulus),
        rho=lambda tn: None if tn[0][1] == 0 else tape_head(tn[0]),
    )


def ctl_zone() -> System:
    return System(
        name="control",
        states=ctl_states(),
        inputs=tuple((sym, load) for sym in ALPHABET for load in LOADS),
        outputs=tuple((c, h) for c in COMMANDS for h in (False, True)),
        delta=lambda s, i: s if i is None else ctl_step(s, i[0], i[1]),
        rho=lambda s: (ctl_cmd(s), ctl_halted(s)),
    )


def alt_ctl_zone() -> System:
    """The control under a different state encoding: a tagged sum instead of a record."""

    def encode(s: State) -> State:
        if s[0] == "sense":
            return ("L", s[1])
        if s[0] == "act":
            return ("R", (s[1], s[2]))
        return ("U",)

    decode = {encode(s): s for s in ctl_states()}
    return System(
        name="alt-control",
        states=tuple(decode.keys()),
        inputs=tuple((sym, load) for sym in ALPHABET for load in LOADS),
        outputs=tuple((c, h) for c in COMMANDS for h in (False, True)),
        delta=lambda e, i: e if i is None else encode(ctl_step(decode[e], i[0], i[1])),
        rho=lambda e: (ctl_cmd(decode[e]), ctl_halted(decode[e])),
    )


def coupled_machine(name: str, tape: System, ctl: System, *, decode_ctl=None) -> System:
    """The resultant of the two-zone recipe, wired exactly as `rsy` wires it.

    The control's command port drives the tape's command port, the tape's scan port
    drives the control's symbol port; the control's `load` input and `halted` output
    and the tape's `window` output are the boundary.
    """
    ctl_view = (lambda s: s) if decode_ctl is None else decode_ctl
    tape_view = tape_head if tape.name != "instrumented-tape" else (lambda t: tape_head(t[0]))

    def step(x: State, load: Optional[Symbol]) -> State:
        t, s = x
        if load is None:
            return x
        cmd = ctl_cmd(ctl_view(s))
        return (tape.step(t, cmd), ctl.step(s, (tape_view(t), load[0])))

    def out(x: State) -> Symbol:
        t, s = x
        return (tape_view(t), ctl_halted(ctl_view(s)))

    return System(
        name=name,
        states=tuple((t, s) for t in tape.states for s in ctl.states),
        # A driven tick supplies a load value; the tuple keeps the port structure visible.
        inputs=tuple((load,) for load in LOADS),
        outputs=tuple((a, h) for a in ALPHABET for h in (False, True)),
        delta=step,
        rho=out,
    )


def machine_reference() -> System:
    """The monolithic reference: one table over configurations, no ports, no zones."""

    def step(x: State, load: Optional[Symbol]) -> State:
        t, s = x
        if load is None:
            return x
        return (tape_apply(t, ctl_cmd(s)), ctl_step(s, tape_head(t), load[0]))

    return System(
        name="machine-reference",
        states=tuple((t, s) for t in tape_states() for s in ctl_states()),
        inputs=tuple((load,) for load in LOADS),
        outputs=tuple((a, h) for a in ALPHABET for h in (False, True)),
        delta=step,
        rho=lambda x: (tape_head(x[0]), ctl_halted(x[1])),
    )


# ---------------------------------------------------------------------------
# The tick-granularity pair
# ---------------------------------------------------------------------------


def flip_reference() -> System:
    return System(
        name="flip-reference",
        states=(False, True),
        inputs=("tick",),
        outputs=(False, True),
        delta=lambda s, i: s if i is None else (not s),
        rho=lambda s: s,
    )


def flip_build() -> System:
    """The same register, but it needs a sense tick and an act tick to flip."""

    def step(vp: State, i: Optional[Symbol]) -> State:
        if i is None:
            return vp
        v, phase = vp
        return (v, "act") if phase == "sense" else (not v, "sense")

    return System(
        name="flip-build",
        states=tuple((v, p) for v in (False, True) for p in ("sense", "act")),
        inputs=("tick",),
        outputs=(False, True),
        delta=step,
        rho=lambda vp: vp[0],
    )


def stretched_flip_reference() -> System:
    """The reference restated at the build's granularity: two ticks per logical flip."""
    build = flip_build()
    return System(
        name="stretched-reference",
        states=build.states,
        inputs=build.inputs,
        outputs=build.outputs,
        delta=build.delta,
        rho=build.rho,
    )


# ---------------------------------------------------------------------------
# Compiling the fragment
# ---------------------------------------------------------------------------


def compile_phi_dyn(spec: System) -> list[str]:
    """The dynamics-encoding clauses of `spec`, as the paper writes them."""
    clauses: list[str] = []
    for s in spec.states:
        o = spec.out(s)
        if o is None:
            clauses.append(f"G( state({s!r}) -> noOutput )")
        else:
            clauses.append(f"G( state({s!r}) -> out({o!r}) )")
    for s in spec.states:
        for i in spec.inputs:
            clauses.append(
                f"G( state({s!r}) & in({i!r}) -> X state({spec.step(s, i)!r}) )"
            )
    for s in spec.states:
        clauses.append(f"G( state({s!r}) & noInput -> X state({spec.step(s, None)!r}) )")
    return clauses


# ---------------------------------------------------------------------------
# The conformance query as CNF
# ---------------------------------------------------------------------------


@dataclass
class Cnf:
    """A CNF instance over named atoms, with a DIMACS view."""

    atoms: dict[str, int] = field(default_factory=dict)
    clauses: list[list[int]] = field(default_factory=list)

    def atom(self, name: str) -> int:
        if name not in self.atoms:
            self.atoms[name] = len(self.atoms) + 1
        return self.atoms[name]

    def add(self, literals: list[int]) -> None:
        self.clauses.append(literals)

    @property
    def num_vars(self) -> int:
        return len(self.atoms)

    @property
    def num_clauses(self) -> int:
        return len(self.clauses)

    def dimacs(self) -> str:
        lines = [f"p cnf {self.num_vars} {self.num_clauses}"]
        lines += [" ".join(str(v) for v in clause) + " 0" for clause in self.clauses]
        return "\n".join(lines) + "\n"


def build_cnf(spec: System, impl: System) -> tuple[Cnf, dict[str, list]]:
    """Encode "a surjective conformance triple exists" as CNF.

    Atoms `S[x][s]`, `I[i][j]`, `O[o][p]` assert that the corresponding map sends the
    implementation element to the reference element.
    """
    cnf = Cnf()
    index = {
        "spec_states": list(spec.states),
        "impl_states": list(impl.states),
        "spec_inputs": list(spec.inputs),
        "impl_inputs": list(impl.inputs),
        "spec_outputs": list(spec.outputs),
        "impl_outputs": list(impl.outputs),
    }

    def S(x, s) -> int:
        return cnf.atom(f"S[{x!r}][{s!r}]")

    def I(i, j) -> int:  # noqa: E743 - matches the paper's h_I
        return cnf.atom(f"I[{i!r}][{j!r}]")

    def O(o, p) -> int:  # noqa: E743 - matches the paper's h_O
        return cnf.atom(f"O[{o!r}][{p!r}]")

    def exactly_one(tag: str, pairs: list[int]) -> None:
        """At-least-one plus Sinz's sequential at-most-one, so the encoding stays linear."""
        cnf.add(list(pairs))
        if len(pairs) < 2:
            return
        guard = [cnf.atom(f"amo[{tag}][{k}]") for k in range(len(pairs) - 1)]
        cnf.add([-pairs[0], guard[0]])
        cnf.add([-pairs[-1], -guard[-1]])
        for k in range(1, len(pairs) - 1):
            cnf.add([-pairs[k], guard[k]])
            cnf.add([-pairs[k], -guard[k - 1]])
            cnf.add([-guard[k - 1], guard[k]])

    # h_S, h_I, h_O are functions.
    for x in impl.states:
        exactly_one(f"S{x!r}", [S(x, s) for s in spec.states])
    for i in impl.inputs:
        exactly_one(f"I{i!r}", [I(i, j) for j in spec.inputs])
    for o in impl.outputs:
        exactly_one(f"O{o!r}", [O(o, p) for p in spec.outputs])

    # Readout law: (RZ_impl x).map h_O = RZ_spec (h_S x).
    for x in impl.states:
        ox = impl.out(x)
        for s in spec.states:
            os_ = spec.out(s)
            if ox is None and os_ is None:
                continue
            if ox is None or os_ is None:
                cnf.add([-S(x, s)])
            else:
                cnf.add([-S(x, s), O(ox, os_)])

    # Transition law on driven ticks.
    for x in impl.states:
        for i in impl.inputs:
            xi = impl.step(x, i)
            for s in spec.states:
                for j in spec.inputs:
                    cnf.add([-S(x, s), -I(i, j), S(xi, spec.step(s, j))])

    # Transition law on autonomous ticks.
    for x in impl.states:
        xn = impl.step(x, None)
        for s in spec.states:
            cnf.add([-S(x, s), S(xn, spec.step(s, None))])

    # Surjectivity: every reference element is covered.
    for s in spec.states:
        cnf.add([S(x, s) for x in impl.states])
    for j in spec.inputs:
        cnf.add([I(i, j) for i in impl.inputs])
    for p in spec.outputs:
        cnf.add([O(o, p) for o in impl.outputs])

    return cnf, index


@dataclass
class Verdict:
    name: str
    spec: str
    impl: str
    spec_size: int
    impl_size: int
    conforms: bool
    num_vars: int
    num_clauses: int
    seconds: float
    witness: Optional[dict[str, dict]] = None
    lean_ref: Optional[str] = None
    note: str = ""


def solve(name: str, spec: System, impl: System, *, lean_ref=None, note="") -> tuple[Verdict, Cnf]:
    cnf, index = build_cnf(spec, impl)
    lookup = {v: k for k, v in cnf.atoms.items()}
    z3_atoms = {v: Bool(lookup[v]) for v in cnf.atoms.values()}

    solver = Solver()
    for clause in cnf.clauses:
        solver.add(Or(*[z3_atoms[abs(l)] if l > 0 else Not(z3_atoms[-l]) for l in clause]))

    start = time.perf_counter()
    result = solver.check()
    elapsed = time.perf_counter() - start
    if result not in (sat, unsat):
        raise RuntimeError(f"solver returned {result} on {name}")

    witness = None
    if result == sat:
        model = solver.model()
        witness = {"h_S": {}, "h_I": {}, "h_O": {}}
        for key, (dom, cod, tag) in {
            "h_S": ("impl_states", "spec_states", "S"),
            "h_I": ("impl_inputs", "spec_inputs", "I"),
            "h_O": ("impl_outputs", "spec_outputs", "O"),
        }.items():
            for a in index[dom]:
                for b in index[cod]:
                    atom = z3_atoms[cnf.atoms[f"{tag}[{a!r}][{b!r}]"]]
                    if model.eval(atom, model_completion=True):
                        witness[key][repr(a)] = repr(b)
                        break

    verdict = Verdict(
        name=name,
        spec=spec.name,
        impl=impl.name,
        spec_size=len(spec.states),
        impl_size=len(impl.states),
        conforms=(result == sat),
        num_vars=cnf.num_vars,
        num_clauses=cnf.num_clauses,
        seconds=elapsed,
        witness=witness,
        lean_ref=lean_ref,
        note=note,
    )
    return verdict, cnf


def check_given_map(spec: System, impl: System, witness: dict[str, dict]) -> bool:
    """Re-check a witness directly, in time linear in the clause count.

    The contrast with `solve` is the point: *finding* a conformance map is a search,
    *checking* one is a scan, and the fragment is what makes the second possible.
    """
    hS = {k: v for k, v in witness["h_S"].items()}
    hI = {k: v for k, v in witness["h_I"].items()}
    hO = {k: v for k, v in witness["h_O"].items()}
    for x in impl.states:
        s = hS[repr(x)]
        ox, os_ = impl.out(x), None
        for cand in spec.states:
            if repr(cand) == s:
                os_ = spec.out(cand)
                spec_state = cand
                break
        if (ox is None) != (os_ is None):
            return False
        if ox is not None and hO[repr(ox)] != repr(os_):
            return False
        if hS[repr(impl.step(x, None))] != repr(spec.step(spec_state, None)):
            return False
        for i in impl.inputs:
            j = next(c for c in spec.inputs if repr(c) == hI[repr(i)])
            if hS[repr(impl.step(x, i))] != repr(spec.step(spec_state, j)):
                return False
    covered = set(hS.values())
    return all(repr(s) in covered for s in spec.states)


# ---------------------------------------------------------------------------
# The instance suite
# ---------------------------------------------------------------------------


def instances() -> list[tuple[str, System, System, Optional[bool], Optional[str], str]]:
    """Name, reference, candidate, expected verdict, Lean theorem, note.

    `expected` is taken from a machine-checked theorem wherever one exists; those rows
    are the cross-check.  Rows with no Lean theorem are questions the solver settles on
    its own and are marked as such.
    """
    tape = tape_zone()
    ctl = ctl_zone()
    ref = machine_reference()
    coupled = coupled_machine("coupled-machine", tape, ctl)
    elaborated = coupled_machine(
        "rebuilt-machine",
        instrumented_tape_zone(),
        alt_ctl_zone(),
        decode_ctl=lambda e: {("L", q): ("sense", q) for q in LABELS}.get(
            e, ("act", e[1][0], e[1][1]) if e[0] == "R" else ("halted",)
        ),
    )
    broken = coupled_machine("frozen-tape-machine", frozen_tape_zone(), ctl)

    return [
        (
            "machine-vs-coupling",
            ref,
            coupled,
            True,
            "TuringCoupling.tmResultant_satisfies_reference_fragment",
            "the coupling realises the monolithic reference",
        ),
        (
            "machine-vs-rebuilt",
            ref,
            elaborated,
            True,
            "TuringCoupling.tmElaboratedResultant_satisfies_reference_fragment",
            "both zones swapped; the map is discovered, not supplied",
        ),
        (
            "machine-vs-frozen-tape",
            ref,
            broken,
            None,
            None,
            "a zone bug rejected at machine level; solver-only",
        ),
        (
            "tape-vs-instrumented",
            tape,
            instrumented_tape_zone(),
            True,
            "TuringCoupling.instrTapeHom",
            "extra internal state projects away",
        ),
        (
            "control-vs-reencoded",
            ctl,
            alt_ctl_zone(),
            True,
            "TuringCoupling.altCtlIso",
            "same behaviour, different state encoding",
        ),
        (
            "tape-vs-frozen",
            tape,
            frozen_tape_zone(),
            False,
            "TuringCoupling.no_hom_frozenTape",
            "never actuates its commands",
        ),
        (
            "tape-vs-blind",
            tape,
            blind_tape_zone(),
            False,
            "TuringCoupling.no_hom_blindTape",
            "reports a blank window",
        ),
        (
            "quiet-vs-instrumented",
            quiet_tape_zone(),
            instrumented_quiet_tape_zone(),
            True,
            "TuringCoupling.instrQuietTape_realises",
            "reference with a silent mode; instrumentation is not a readout",
        ),
        (
            "quiet-vs-talkative",
            quiet_tape_zone(),
            tape_zone("talkative-tape"),
            False,
            "TuringCoupling.no_hom_quietTape_from_tape",
            "rejected for reporting where the reference is silent",
        ),
        (
            "flip-one-tick",
            flip_reference(),
            flip_build(),
            False,
            "TickGranularity.flip_fragment_fails",
            "build needs two ticks per logical step",
        ),
        (
            "flip-matched-ticks",
            stretched_flip_reference(),
            flip_build(),
            True,
            "TickGranularity.stretchedRef_fragment_holds",
            "same build, reference restated at matched granularity",
        ),
    ]


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def tex_table(verdicts: list[Verdict]) -> str:
    """Rows of the results table: reference size, candidate size, CNF size, verdict, time."""
    rows = [
        "% Generated by scripts/phi_dyn_solver.py -- do not edit by hand.",
        "% Columns: instance, |S_spec|, |S_impl|, vars, clauses, verdict, ms, Lean-checked",
    ]
    for v in verdicts:
        checked = r"\checkmark" if v.lean_ref else "--"
        rows.append(
            f"\\texttt{{{v.name}}} & {v.spec_size} & {v.impl_size} & "
            f"{v.num_vars} & {v.num_clauses} & "
            f"{'SAT' if v.conforms else 'UNSAT'} & {v.seconds * 1000:.1f} & {checked} \\\\"
        )
    return "\n".join(rows) + "\n"


LEAN_TEMPLATE = '''import Mbse.PartialDynamicsHomFragment

/-!
# A solver-discovered conformance map, machine-checked

Generated by `scripts/phi_dyn_solver.py --emit-lean` for the `{instance}` instance; do not edit by
hand.  The two systems are the reference and the candidate of that instance, re-indexed by `Fin`, and
`hS`, `hI`, `hO` are the maps the SAT solver returned.  Every law of Definition 4.3 is then checked
by the kernel with `decide`, so the solver is not being trusted: it proposes, Lean verifies.
-/

namespace SolverWitness

open Homomorphism PartialDynamicsHomFragment

/-! ## The reference, as a table over `Fin {n_spec}` -/

def specNext : Fin {n_spec} → Fin {n_spec_in1} → Fin {n_spec} :=
  {spec_next}

def specOut : Fin {n_spec} → Option (Fin {n_spec_out}) :=
  {spec_out}

/-! ## The candidate, as a table over `Fin {n_impl}` -/

def implNext : Fin {n_impl} → Fin {n_impl_in1} → Fin {n_impl} :=
  {impl_next}

def implOut : Fin {n_impl} → Option (Fin {n_impl_out}) :=
  {impl_out}

/-- Index a driven or autonomous tick: `0` is the autonomous tick, `i+1` is input `i`. -/
def tick {{k : Nat}} : Option (Fin k) → Fin (k + 1)
  | none => 0
  | some i => i.succ

def specSys : DiscreteSystem (Fin {n_spec}) (Fin {n_spec_in}) (Fin {n_spec_out}) where
  sz_nonempty := ⟨0⟩
  NZ x oi := specNext x (tick oi)
  RZ := specOut

def implSys : DiscreteSystem (Fin {n_impl}) (Fin {n_impl_in}) (Fin {n_impl_out}) where
  sz_nonempty := ⟨0⟩
  NZ x oi := implNext x (tick oi)
  RZ := implOut

/-! ## The maps the solver returned -/

def hS : Fin {n_impl} → Fin {n_spec} :=
  {h_s}

def hI : Fin {n_impl_in} → Fin {n_spec_in} :=
  {h_i}

def hO : Fin {n_impl_out} → Fin {n_spec_out} :=
  {h_o}

/-! ## Kernel-checked conformance -/

theorem hS_surjective : Function.Surjective hS := by decide
theorem hI_surjective : Function.Surjective hI := by decide
theorem hO_surjective : Function.Surjective hO := by decide

theorem preserves_transition :
    ∀ x oi, hS (implSys.NZ x oi) = specSys.NZ (hS x) (oi.map hI) := by decide

theorem preserves_readout : ∀ x, (implSys.RZ x).map hO = specSys.RZ (hS x) := by decide

/-- The solver's model, assembled into a Definition 4.3 witness. -/
def witness : HomomorphicImageWitness specSys implSys where
  HS := hS
  HI := hI
  HO := hO
  HS_surjective := hS_surjective
  HI_surjective := hI_surjective
  HO_surjective := hO_surjective
  preserves_transition := preserves_transition
  preserves_readout := preserves_readout

/--
The verdict the solver reported, now a theorem: the candidate satisfies the fragment compiled from
the reference.
-/
theorem solver_verdict_confirmed :
    SystemSatisfiesPartialDynamicsHom specSys implSys :=
  partialDynamicsHom_of_hom ⟨witness⟩

end SolverWitness
'''


def _lean_vec(values: list[str], per_line: int = 8, default: str = "0") -> str:
    """A dependency-free lookup table: a list literal indexed by `Fin.val`."""
    chunks = [
        ", ".join(values[start : start + per_line])
        for start in range(0, len(values), per_line)
    ]
    body = ",\n    ".join(chunks)
    return f"fun i => [\n    {body}\n  ].getD i.val {default}"


def emit_lean(path: Path, name: str, spec: System, impl: System, witness: dict[str, dict]) -> None:
    """Write a Lean file re-checking a solver-found map with `decide`."""
    spec_state_ix = {repr(s): k for k, s in enumerate(spec.states)}
    impl_state_ix = {repr(s): k for k, s in enumerate(impl.states)}
    spec_in_ix = {repr(i): k for k, i in enumerate(spec.inputs)}
    spec_out_ix = {repr(o): k for k, o in enumerate(spec.outputs)}
    impl_out_ix = {repr(o): k for k, o in enumerate(impl.outputs)}

    def next_table(sys: System, state_ix, in_list) -> str:
        rows = []
        for s in sys.states:
            row = [state_ix[repr(sys.step(s, None))]]
            row += [state_ix[repr(sys.step(s, i))] for i in in_list]
            rows.append(row)
        flat = [str(v) for row in rows for v in row]
        width = len(in_list) + 1
        return (
            "fun x t => [\n    "
            + ",\n    ".join(
                ", ".join(flat[k * width : (k + 1) * width]) for k in range(len(rows))
            )
            + f"\n  ].getD (x.val * {width} + t.val) 0"
        )

    def out_table(sys: System, out_ix) -> str:
        entries = [
            "none" if sys.out(s) is None else f"some {out_ix[repr(sys.out(s))]}"
            for s in sys.states
        ]
        return _lean_vec(entries, per_line=6, default="none")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        LEAN_TEMPLATE.format(
            instance=name,
            n_spec=len(spec.states),
            n_impl=len(impl.states),
            n_spec_in=len(spec.inputs),
            n_impl_in=len(impl.inputs),
            n_spec_in1=len(spec.inputs) + 1,
            n_impl_in1=len(impl.inputs) + 1,
            n_spec_out=len(spec.outputs),
            n_impl_out=len(impl.outputs),
            spec_next=next_table(spec, spec_state_ix, list(spec.inputs)),
            impl_next=next_table(impl, impl_state_ix, list(impl.inputs)),
            spec_out=out_table(spec, spec_out_ix),
            impl_out=out_table(impl, impl_out_ix),
            h_s=_lean_vec(
                [str(spec_state_ix[witness["h_S"][repr(x)]]) for x in impl.states]
            ),
            h_i=_lean_vec([str(spec_in_ix[witness["h_I"][repr(i)]]) for i in impl.inputs]),
            h_o=_lean_vec([str(spec_out_ix[witness["h_O"][repr(o)]]) for o in impl.outputs]),
        )
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimacs-dir", type=Path, help="write each instance as DIMACS CNF")
    parser.add_argument("--tex", type=Path, help="write the results table for the paper")
    parser.add_argument("--show-clauses", metavar="INSTANCE", help="print the compiled fragment")
    parser.add_argument(
        "--emit-lean",
        type=Path,
        metavar="PATH",
        help="write a solver-found map to a Lean file that re-checks it with decide",
    )
    parser.add_argument(
        "--emit-lean-instance",
        default="tape-vs-instrumented",
        help="which instance to emit for --emit-lean",
    )
    args = parser.parse_args()

    suite = instances()

    if args.show_clauses:
        for name, spec, _impl, _exp, _ref, _note in suite:
            if name == args.show_clauses:
                clauses = compile_phi_dyn(spec)
                print(f"# compiled fragment of {spec.name}: {len(clauses)} clauses")
                for c in clauses:
                    print(c)
                return 0
        print(f"unknown instance {args.show_clauses}")
        return 2

    verdicts: list[Verdict] = []
    disagreements: list[str] = []

    for name, spec, impl, expected, lean_ref, note in suite:
        verdict, cnf = solve(name, spec, impl, lean_ref=lean_ref, note=note)
        verdicts.append(verdict)

        if args.dimacs_dir:
            args.dimacs_dir.mkdir(parents=True, exist_ok=True)
            (args.dimacs_dir / f"{name}.cnf").write_text(cnf.dimacs())

        status = "SAT" if verdict.conforms else "UNSAT"
        mark = ""
        if expected is not None and verdict.conforms != expected:
            mark = "  <-- DISAGREES WITH LEAN"
            disagreements.append(f"{name}: solver {status}, Lean says {expected}")
        print(
            f"{name:24s} {verdict.spec:20s} {verdict.impl:22s} "
            f"{status:5s} vars={verdict.num_vars:5d} clauses={verdict.num_clauses:7d} "
            f"{verdict.seconds * 1000:7.1f} ms{mark}"
        )
        print(f"{'':24s} {note}")

        if verdict.conforms and not check_given_map(spec, impl, verdict.witness):
            disagreements.append(f"{name}: recovered witness failed the linear re-check")

        if args.emit_lean and name == args.emit_lean_instance:
            if not verdict.conforms:
                disagreements.append(f"{name}: cannot emit a Lean witness for an UNSAT instance")
            else:
                emit_lean(args.emit_lean, name, spec, impl, verdict.witness)
                print(f"{'':24s} wrote Lean witness to {args.emit_lean}")

    if args.tex:
        args.tex.parent.mkdir(parents=True, exist_ok=True)
        args.tex.write_text(tex_table(verdicts))
        print(f"\nwrote {args.tex}")

    checked = sum(1 for v in verdicts if v.lean_ref)
    print(
        f"\n{len(verdicts)} instances, {checked} cross-checked against Lean theorems, "
        f"{len(verdicts) - checked} solver-only"
    )
    if disagreements:
        print("\nFAILURES:")
        for d in disagreements:
            print(f"  {d}")
        return 1
    print("OK: every solver verdict agrees with its machine-checked counterpart.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
