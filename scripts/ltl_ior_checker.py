#!/usr/bin/env python3
"""Automated LTL model checker and dynamics-fragment verifier for the finite-tape
Streaming Run-Length Encoder (RLE) case study in T3SD.

Demonstrates the paper's core workflow:
1. The idealized infinite-tape/count RLE coupling recipe is refined to a finite
   buildable technology TYR_fin with count cap N in {2, 3, 4}.
2. The coupled 4-component resultant Z_b = RSY(SCR_fin) (tape, sense/act head,
   state register, instruction table) operates under its natural System Mode
   Z_m in SYSMO(Z_b).
3. Direct LTL model checking tests Z_m |= Phi_IOR (propositional LTL clauses
   for initial pipeline fill, first symbol acquisition, act-tick output hold,
   run continuation/saturation up to N, and run reset on symbol change).
   By Theorem 2, Z_m |= Phi_IOR iff Z_m maps homomorphically into CTL(IOR_fin),
   certifying membership in the Implementability Cotyledon CTL(IOR_fin, TYR_fin)
   without manually constructing a state homomorphism.
"""

from __future__ import annotations

import argparse
import time
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional

Bit = int  # 0 or 1
Pair = tuple[Bit, int]  # (bit, count)


@dataclass(frozen=True)
class RleCellState:
    bit: Bit
    count: int
    phase: int  # 0 = sense, 1 = act


INIT_CELL = RleCellState(0, 0, 0)


def rle_step_cap(s: RleCellState, b: Bit, cap: int, *, broken_reset: bool = False) -> RleCellState:
    """Instruction table transition with count capped at `cap`."""
    if s.phase == 1:
        return RleCellState(s.bit, s.count, 0)
    if s.count != 0 and (b == s.bit or broken_reset):
        nxt_count = min(s.count + 1, cap)
    else:
        nxt_count = 1
    return RleCellState(b, nxt_count, 1)


@dataclass(frozen=True)
class CoupledState:
    tape_bit: Bit
    head_phase: int
    reg_bit: Bit
    reg_count: int
    table: RleCellState
    aux_tag: int = 0


def make_resultant_step(
    cap: int,
    *,
    flip_table_phase: bool = False,
    instrument_reg: bool = False,
    stuck_head: bool = False,
    frozen_tape: bool = False,
    broken_reset: bool = False,
) -> tuple[CoupledState, Callable[[CoupledState, Bit], CoupledState], Callable[[CoupledState], Pair]]:
    """Construct the 4-component coupled RLE resultant in CTL(TYR_fin)."""
    table_init_phase = 0 if flip_table_phase else 1
    init_state = CoupledState(
        tape_bit=0,
        head_phase=1,
        reg_bit=0,
        reg_count=0,
        table=RleCellState(0, 0, table_init_phase),
        aux_tag=0,
    )

    def step(x: CoupledState, ext_bit: Bit) -> CoupledState:
        # Component 0: Tape latches external input bit
        new_tape_bit = x.tape_bit if frozen_tape else ext_bit
        # Component 1: Sense/act head flips phase (unless stuck)
        new_head_phase = x.head_phase if stuck_head else (1 - x.head_phase)
        # Component 2: Register latches previous table readout
        new_reg_bit = x.table.bit
        new_reg_count = x.table.count
        new_aux = (x.aux_tag ^ ext_bit) if instrument_reg else 0
        # Component 3: Instruction table steps on previous tape readout
        if flip_table_phase:
            unflipped = RleCellState(x.table.bit, x.table.count, 1 - x.table.phase)
            stepped = rle_step_cap(unflipped, x.tape_bit, cap, broken_reset=broken_reset)
            new_table = RleCellState(stepped.bit, stepped.count, 1 - stepped.phase)
        else:
            new_table = rle_step_cap(x.table, x.tape_bit, cap, broken_reset=broken_reset)

        return CoupledState(
            tape_bit=new_tape_bit,
            head_phase=new_head_phase,
            reg_bit=new_reg_bit,
            reg_count=new_reg_count,
            table=new_table,
            aux_tag=new_aux,
        )

    def readout(x: CoupledState) -> Pair:
        return (x.reg_bit, x.reg_count)

    return init_state, step, readout


@dataclass
class LTLVerificationResult:
    name: str
    cap: int
    total_states: int
    reachable_mode_states: int
    ltl_clauses: int
    verdict: str
    failed_clause: Optional[str]
    elapsed_ms: float


def verify_ltl_ior(
    name: str,
    cap: int,
    *,
    flip_table_phase: bool = False,
    instrument_reg: bool = False,
    stuck_head: bool = False,
    frozen_tape: bool = False,
    broken_reset: bool = False,
    mismatched_one_tick: bool = False,
) -> LTLVerificationResult:
    """Model-check the propositional LTL specification Phi_IOR over the finite
    System Mode Kripke structure of the coupled 4-component resultant.
    """
    t0 = time.perf_counter()
    init_state, step, readout = make_resultant_step(
        cap,
        flip_table_phase=flip_table_phase,
        instrument_reg=instrument_reg,
        stuck_head=stuck_head,
        frozen_tape=frozen_tape,
        broken_reset=broken_reset,
    )

    # Component state space size: 2 (tape) * 2 (head) * 2*(cap+1)*(1 or 2) (reg) * 2*(cap+1)*2 (table)
    reg_mult = 2 if instrument_reg else 1
    total_states = 2 * 2 * (2 * (cap + 1) * reg_mult) * (2 * (cap + 1) * 2)

    # Explore reachable System Mode states (coupled state + clock phase parity)
    seen: set[tuple[CoupledState, int]] = {(init_state, 0)}
    sense_states: list[CoupledState] = []
    queue: deque[tuple[CoupledState, int]] = deque([(init_state, 0)])

    while queue:
        st, parity = queue.popleft()
        if parity == 0:
            sense_states.append(st)
        for b in (0, 1):
            nxt = step(st, b)
            nxt_pair = (nxt, 1 - parity)
            if nxt_pair not in seen:
                seen.add(nxt_pair)
                queue.append(nxt_pair)

    # Count propositional LTL clauses in Phi_IOR_fin:
    # - 2 initial pipeline fill clauses: y(0)=(0,0) and X(y=(0,0))
    # - 2 first-symbol clauses: x=b -> X^3(y=(b,1)) for b in {0,1}
    # - 2*cap hold clauses: G(sense & X^3(y=(b,c)) -> X^4(y=(b,c)))
    # - 2*cap continuation clauses: G(sense & x=b & X^2(x=b) & X^3(y=(b,c)) -> X^5(y=(b,min(c+1,N))))
    # - 2*cap reset clauses: G(sense & x=b & X^2(x=1-b) & X^3(y=(b,c)) -> X^5(y=(1-b,1)))
    ltl_clauses = 2 + 2 + 6 * cap

    failed: Optional[str] = None

    # 1. Check initial pipeline fill: y(0) == (0,0) and X y(0) == (0,0)
    if readout(init_state) != (0, 0):
        failed = r"$\varphi_{\mathrm{init}}$"
    for b0 in (0, 1):
        s1 = step(init_state, b0)
        if readout(s1) != (0, 0):
            failed = r"$\varphi_{\mathrm{init}}$"

    # 2. Check first symbol acquisition: x(0)=b0 -> y(3)=(b0, 1)
    if failed is None:
        for b0 in (0, 1):
            for b1 in (0, 1):
                for b2 in (0, 1):
                    s1 = step(init_state, b0)
                    s2 = step(s1, b1)
                    s3 = step(s2, b2)
                    if readout(s3) != (b0, 1):
                        failed = r"$\varphi_{\mathrm{start}}$"
                        break

    # 3. Check global temporal clauses G(...) over all reachable sense-tick states
    if failed is None:
        check_states = [st for (st, _) in seen] if mismatched_one_tick else sense_states
        for s in check_states:
            # Verify head phase coherence with System Mode sense clock
            if not mismatched_one_tick and s.head_phase != 1:
                failed = r"$\varphi_{\mathrm{mode}}$"
                break
            for b0 in (0, 1):
                s1 = step(s, b0)
                if not mismatched_one_tick and s1.head_phase != 0:
                    failed = r"$\varphi_{\mathrm{mode}}$"
                    break
                for b1 in (0, 1):
                    s2 = step(s1, b1)
                    for b2 in (0, 1):
                        s3 = step(s2, b2)
                        y3 = readout(s3)
                        for b3 in (0, 1):
                            s4 = step(s3, b3)
                            y4 = readout(s4)
                            # Clause family 3: Act-tick output hold X^3(y) == X^4(y)
                            if y4 != y3:
                                failed = r"$\varphi_{\mathrm{hold}}$"
                                break
                            for b4 in (0, 1):
                                s5 = step(s4, b4)
                                y5 = readout(s5)
                                # If s was past initial fill (y3[1] >= 1) and symbol at s was b0:
                                if y3[1] >= 1 and y3[0] == b0:
                                    if b2 == b0:
                                        expected = (b0, min(y3[1] + 1, cap))
                                        if y5 != expected:
                                            failed = r"$\varphi_{\mathrm{inc}}$"
                                            break
                                    else:
                                        expected = (b2, 1)
                                        if y5 != expected:
                                            failed = r"$\varphi_{\mathrm{reset}}$"
                                            break
                            if failed:
                                break
                        if failed:
                            break
                    if failed:
                        break
                if failed:
                    break
            if failed:
                break

    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    verdict = "PASS" if failed is None else "FAIL"
    return LTLVerificationResult(
        name=name,
        cap=cap,
        total_states=total_states,
        reachable_mode_states=len(seen),
        ltl_clauses=ltl_clauses,
        verdict=verdict,
        failed_clause=failed,
        elapsed_ms=elapsed_ms,
    )


def run_suite() -> list[LTLVerificationResult]:
    return [
        verify_ltl_ior("rle-coupled-cap2", cap=2),
        verify_ltl_ior("rle-coupled-cap3", cap=3),
        verify_ltl_ior("rle-coupled-cap4", cap=4),
        verify_ltl_ior("rle-reencoded-table", cap=3, flip_table_phase=True),
        verify_ltl_ior("rle-instrumented-reg", cap=3, instrument_reg=True),
        verify_ltl_ior("rle-stuck-head", cap=3, stuck_head=True),
        verify_ltl_ior("rle-frozen-tape", cap=3, frozen_tape=True),
        verify_ltl_ior("rle-no-reset-table", cap=3, broken_reset=True),
        verify_ltl_ior("rle-mismatched-1tick", cap=3, mismatched_one_tick=True),
    ]


def write_tex_table(results: list[LTLVerificationResult], out_path: Path) -> None:
    lines = [
        "% Generated by scripts/ltl_ior_checker.py -- do not edit by hand.",
        "% Columns: Candidate Design, Cap N, |S_resultant|, |S_mode|, LTL Clauses, Verdict, Violated Property, Time (ms)",
    ]
    for r in results:
        violated = "--" if r.failed_clause is None else r.failed_clause
        lines.append(
            f"\\texttt{{{r.name}}} & {r.cap} & {r.total_states} & {r.reachable_mode_states} "
            f"& {r.ltl_clauses} & {r.verdict} & {violated} & {r.elapsed_ms:.2f} \\\\"
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tex",
        type=Path,
        default=Path("papers/ltl_paper/generated/solver-results.tex"),
        help="Output path for generated LaTeX table rows.",
    )
    args = parser.parse_args()
    results = run_suite()
    write_tex_table(results, args.tex)
    for r in results:
        print(
            f"{r.name:22s} | N={r.cap} | |S|={r.total_states:4d} | |S_m|={r.reachable_mode_states:3d} "
            f"| clauses={r.ltl_clauses:2d} | {r.verdict:4s} | {r.failed_clause or '-':18s} | {r.elapsed_ms:.2f} ms"
        )


if __name__ == "__main__":
    main()
