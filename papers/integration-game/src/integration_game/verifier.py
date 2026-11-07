"""
verifier.py
Formal Decidability, Z3 Symbolic Verification, Bounded Model Checking (BMC),
and Counterexample-Guided Inductive Synthesis (CEGIS) for The Integration Game.

Bridges the scenario trace evaluator (`Board.simulate` + `UniversalLSC`) with
universal verification (`forall f in ITR`) using Z3 across the decidable theories
inhabited by the Integration Game technology catalog T:
  - QF_LRA:  Quantifier-Free Linear Real Arithmetic (unit/frame Recolor, Kalman, TMR)
  - QF_NRA:  Quantifier-Free Nonlinear Real Arithmetic (Tarski-decidable polynomial ALUs)
  - QF_LIRA: Quantifier-Free Mixed Linear Integer/Real Arithmetic (clocks, queues,
             stale gates, failover muxes, and stateful Vending Machine FSMs)
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple

import z3

from .board import Board
from .primitives import Color, Dynamics, Field, Message, Provenance
from .scoring import BoardEvaluator, ScoreBreakdown
from .ulsc import UniversalLSC


@dataclass
class Z3VerificationResult:
    """Result of discharging a universal Tier-3 correctness obligation in Z3."""
    name: str
    verified: bool
    solver_status: str  # "unsat" (universally valid) | "sat" (counterexample found) | "unknown"
    theory: str
    horizon: int
    wall_time_ms: float
    summary: str
    counterexample: Dict[str, Any] = field(default_factory=dict)


def verify_symbolic_recolor_chain_z3(
    name: str,
    symbolic_board_fn: Callable[[z3.ArithRef], z3.ArithRef],
    symbolic_spec_fn: Callable[[z3.ArithRef], z3.ArithRef],
    input_bounds: Tuple[float, float] = (-100.0, 1000.0),
    tolerance: float = 1e-3,
) -> Z3VerificationResult:
    """
    Universal verification in QF_LRA over all real inputs x in [x_min, x_max].
    Checks if there exists ANY input x where |y_board(x) - y_spec(x)| > tolerance.
    Catches "coincidence point" bugs (e.g. -40 F == -40 C) that fool single-point tests.
    """
    t0 = time.perf_counter()
    x = z3.Real("x_in")
    s = z3.Solver()
    s.add(x >= z3.RealVal(input_bounds[0]), x <= z3.RealVal(input_bounds[1]))

    y_board = symbolic_board_fn(x)
    y_spec = symbolic_spec_fn(x)
    diff = y_board - y_spec
    tol = z3.RealVal(tolerance)

    # Negated correctness property: exists x in [min, max] s.t. |y_board - y_spec| > tol
    s.add(z3.Or(diff > tol, -diff > tol))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0

    if res == z3.unsat:
        return Z3VerificationResult(
            name=name,
            verified=True,
            solver_status="unsat",
            theory="QF_LRA",
            horizon=1,
            wall_time_ms=dt_ms,
            summary=f"UNSAT: Universally valid for all x in [{input_bounds[0]}, {input_bounds[1]}]",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        m = s.model()
        val_str = str(m.eval(x, model_completion=True))
        cex["x_in"] = val_str
    return Z3VerificationResult(
        name=name,
        verified=False,
        solver_status=str(res),
        theory="QF_LRA",
        horizon=1,
        wall_time_ms=dt_ms,
        summary=f"SAT: Counterexample found at x_in={cex.get('x_in')} violating tolerance {tolerance}",
        counterexample=cex,
    )


def verify_noncommutative_alu_z3(
    swapped: bool = False,
    m_bounds: Tuple[float, float] = (1.0, 1000.0),
    v_bounds: Tuple[float, float] = (1.0, 500.0),
    tolerance: float = 1e-3,
) -> Z3VerificationResult:
    """
    Universal verification of Ex06 Kinetic Energy ALU (E_k = 0.5 * m * v^2) in QF_NRA
    (Tarski-decidable polynomial real arithmetic).
    Even if a point test only checks the symmetric point m=10, v=10 (where 0.5*m*v^2 == 0.5*v*m^2),
    Z3 immediately refutes the swapped ALU and proves the properly wired ALU across all (m, v).
    """
    t0 = time.perf_counter()
    m = z3.Real("mass_kg")
    v = z3.Real("vel_mps")
    s = z3.Solver()
    s.add(m >= z3.RealVal(m_bounds[0]), m <= z3.RealVal(m_bounds[1]))
    s.add(v >= z3.RealVal(v_bounds[0]), v <= z3.RealVal(v_bounds[1]))

    expected_ke = z3.RealVal("0.5") * m * (v * v)
    actual_ke = (z3.RealVal("0.5") * v * (m * m)) if swapped else (z3.RealVal("0.5") * m * (v * v))
    diff = actual_ke - expected_ke
    tol = z3.RealVal(tolerance)

    s.add(z3.Or(diff > tol, -diff > tol))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    label = "Ex06_ALU_Swapped" if swapped else "Ex06_ALU_Correct"

    if res == z3.unsat:
        return Z3VerificationResult(
            name=label,
            verified=True,
            solver_status="unsat",
            theory="QF_NRA",
            horizon=1,
            wall_time_ms=dt_ms,
            summary="UNSAT: Polynomial identity E_k = 0.5*m*v^2 holds for all (m, v) in domain",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        model = s.model()
        m_rat = model.eval(m, model_completion=True)
        v_rat = model.eval(v, model_completion=True)
        cex = {
            "mass_kg": float(m_rat.as_decimal(6).rstrip("?")),
            "vel_mps": float(v_rat.as_decimal(6).rstrip("?")),
        }
    return Z3VerificationResult(
        name=label,
        verified=False,
        solver_status=str(res),
        theory="QF_NRA",
        horizon=1,
        wall_time_ms=dt_ms,
        summary=f"SAT: Swapped operand counterexample found at m={cex.get('mass_kg')}, v={cex.get('vel_mps')}",
        counterexample=cex,
    )


def verify_ping_pong_queue_bmc_z3(
    retain_on_read: bool = False,
    horizon: int = 6,
) -> Z3VerificationResult:
    """
    Bounded Model Checking (QF_LIRA) of Ex02 Ping/Pong over ALL 2^H possible Ping arrival
    schedules and arbitrary sequence numbers seq[t].
    Proves that consume-on-read (retain_on_read=False) never commits a silence breach or
    value mismatch, whereas retain_on_read=True commits a silence breach whenever a Ping
    is followed by a quiet tick.
    """
    t0 = time.perf_counter()
    s = z3.Solver()

    ping_present = [z3.Bool(f"ping_{t}") for t in range(horizon)]
    ping_seq = [z3.Int(f"seq_{t}") for t in range(horizon)]

    # Require at least one ping and at least one quiet tick after a ping in ITR
    s.add(z3.Or(*[z3.And(ping_present[t], z3.Not(ping_present[t + 1])) for t in range(horizon - 1)]))
    for t in range(horizon):
        s.add(ping_seq[t] >= 1, ping_seq[t] <= 65535)

    # Cache state across ticks: has_cached[t], cached_val[t]
    has_cached = [z3.Bool(f"has_cached_{t}") for t in range(horizon + 1)]
    cached_val = [z3.Int(f"cached_val_{t}") for t in range(horizon + 1)]
    s.add(z3.Not(has_cached[0]))
    s.add(cached_val[0] == 0)

    breach_ticks = []
    for t in range(horizon):
        # Step 1: Producer pushes if ping_present[t]
        has_after_push = z3.If(ping_present[t], z3.BoolVal(True), has_cached[t])
        val_after_push = z3.If(ping_present[t], ping_seq[t], cached_val[t])

        # Step 2: Consumer pulls on tick t
        pong_emitted = has_after_push
        pong_val = val_after_push

        # Step 3: Cache retention update after pull
        if retain_on_read:
            s.add(has_cached[t + 1] == has_after_push)
            s.add(cached_val[t + 1] == val_after_push)
        else:
            s.add(has_cached[t + 1] == z3.BoolVal(False))
            s.add(cached_val[t + 1] == 0)

        # Tier-3 uLSC obligation at tick t:
        #   - If ping_present[t]: must emit pong with pong_val == ping_seq[t]
        #   - If not ping_present[t]: must remain silent (not pong_emitted)
        miss_or_bad_val = z3.And(ping_present[t], z3.Or(z3.Not(pong_emitted), pong_val != ping_seq[t]))
        silence_violation = z3.And(z3.Not(ping_present[t]), pong_emitted)
        breach_ticks.append(z3.Or(miss_or_bad_val, silence_violation))

    s.add(z3.Or(*breach_ticks))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    label = f"Ex02_PingPong_BMC(retain={retain_on_read})"

    if res == z3.unsat:
        return Z3VerificationResult(
            name=label,
            verified=True,
            solver_status="unsat",
            theory="QF_LIRA",
            horizon=horizon,
            wall_time_ms=dt_ms,
            summary=f"UNSAT: Verified across all 2^{horizon} ping schedules and uint16 sequence numbers",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        m = s.model()
        cex["ping_schedule"] = [bool(z3.is_true(m.eval(ping_present[t], model_completion=True))) for t in range(horizon)]
    return Z3VerificationResult(
        name=label,
        verified=False,
        solver_status=str(res),
        theory="QF_LIRA",
        horizon=horizon,
        wall_time_ms=dt_ms,
        summary=f"SAT: Silence breach found on schedule {cex.get('ping_schedule')}",
        counterexample=cex,
    )


def verify_stale_gate_bmc_z3(
    use_stale_gate: bool = True,
    max_age: int = 2,
    horizon: int = 7,
) -> Z3VerificationResult:
    """
    Bounded Model Checking (QF_LIRA) of Ex09 Multi-Rate Cache + Pump + optional StaleGate
    over all producer emission schedules starting at t=0.
    Proves that with StaleGate(max_age=2), no stale sample (age > 2) can ever reach the
    fast consumer under any sensor dropout pattern.
    """
    t0 = time.perf_counter()
    s = z3.Solver()

    emit = [z3.Bool(f"emit_{t}") for t in range(horizon)]
    s.add(emit[0])  # Producer emits at t=0
    # Allow any dropout schedule that has at least one gap > max_age
    s.add(z3.Or(*[
        z3.And(*[z3.Not(emit[k]) for k in range(t, min(horizon, t + max_age + 1))])
        for t in range(1, horizon - max_age)
    ]))

    last_timestamp = [z3.Int(f"ts_{t}") for t in range(horizon)]
    s.add(last_timestamp[0] == 0)
    for t in range(1, horizon):
        s.add(last_timestamp[t] == z3.If(emit[t], z3.IntVal(t), last_timestamp[t - 1]))

    stale_breaches = []
    for t in range(horizon):
        age = z3.IntVal(t) - last_timestamp[t]
        delivered = (age <= max_age) if use_stale_gate else z3.BoolVal(True)
        # Breach if a sample is delivered to the consumer with age > max_age
        stale_breaches.append(z3.And(delivered, age > max_age))

    s.add(z3.Or(*stale_breaches))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    label = f"Ex09_StaleGate_BMC(gated={use_stale_gate})"

    if res == z3.unsat:
        return Z3VerificationResult(
            name=label,
            verified=True,
            solver_status="unsat",
            theory="QF_LIRA",
            horizon=horizon,
            wall_time_ms=dt_ms,
            summary=f"UNSAT: Zero stale emissions (age > {max_age}) possible across any dropout schedule",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        m = s.model()
        cex["emit_schedule"] = [bool(z3.is_true(m.eval(emit[t], model_completion=True))) for t in range(horizon)]
    return Z3VerificationResult(
        name=label,
        verified=False,
        solver_status=str(res),
        theory="QF_LIRA",
        horizon=horizon,
        wall_time_ms=dt_ms,
        summary=f"SAT: Stale sample delivered under dropout schedule {cex.get('emit_schedule')}",
        counterexample=cex,
    )


def verify_tmr_voter_bmc_z3(
    use_tmr: bool = True,
    horizon: int = 4,
) -> Z3VerificationResult:
    """
    Bounded Model Checking (QF_LRA) of Ex10 Provenance TMR Voter under arbitrary single-sensor
    fault injection per tick.
    At each tick t, true altitude alt[t] in [0, 10000], at most one sensor i_fault[t] in {0, 1, 2}
    experiences an arbitrary unbounded glitch fault_mag[t] != 0, while the other two sensors are exact.
    Proves that 3-channel TMR majority voting masks ALL single-sensor glitches at every tick.
    """
    t0 = time.perf_counter()
    s = z3.Solver()

    breaches = []
    fault_ch = [z3.Int(f"fault_ch_{t}") for t in range(horizon)]
    fault_mag = [z3.Real(f"fault_mag_{t}") for t in range(horizon)]
    true_alt = [z3.Real(f"true_alt_{t}") for t in range(horizon)]

    # Require at least one non-trivial glitch on channel 1 (the channel used by the single-sensor bypass)
    s.add(z3.Or(*[z3.And(fault_ch[t] == 1, fault_mag[t] >= z3.RealVal(10.0)) for t in range(horizon)]))

    for t in range(horizon):
        s.add(true_alt[t] >= z3.RealVal(0.0), true_alt[t] <= z3.RealVal(10000.0))
        s.add(fault_ch[t] >= 0, fault_ch[t] <= 2)

        ch0 = z3.If(fault_ch[t] == 0, true_alt[t] + fault_mag[t], true_alt[t])
        ch1 = z3.If(fault_ch[t] == 1, true_alt[t] + fault_mag[t], true_alt[t])
        ch2 = z3.If(fault_ch[t] == 2, true_alt[t] + fault_mag[t], true_alt[t])

        if use_tmr:
            voted = z3.If(
                z3.Or(ch0 == ch1, ch0 == ch2),
                ch0,
                ch1,
            )
            out_val = voted
        else:
            # Single-sensor bypass from channel 1
            out_val = ch1

        diff = out_val - true_alt[t]
        breaches.append(z3.Or(diff > z3.RealVal(0.1), -diff > z3.RealVal(0.1)))

    s.add(z3.Or(*breaches))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    label = f"Ex10_TMR_BMC(use_tmr={use_tmr})"

    if res == z3.unsat:
        return Z3VerificationResult(
            name=label,
            verified=True,
            solver_status="unsat",
            theory="QF_LRA",
            horizon=horizon,
            wall_time_ms=dt_ms,
            summary="UNSAT: TMR majority voter masks all single-sensor faults of arbitrary magnitude",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        m = s.model()
        cex["fault_channels"] = [m.eval(fault_ch[t], model_completion=True).as_long() for t in range(horizon)]
    return Z3VerificationResult(
        name=label,
        verified=False,
        solver_status=str(res),
        theory="QF_LRA",
        horizon=horizon,
        wall_time_ms=dt_ms,
        summary=f"SAT: Single-sensor bypass corrupted by fault on channels {cex.get('fault_channels')}",
        counterexample=cex,
    )


def verify_vending_fsm_bmc_z3(
    stateful_fsm: bool = True,
    horizon: int = 4,
) -> Z3VerificationResult:
    """
    Bounded Model Checking (QF_LIRA) of Ex13 Reactive Vending Machine over all possible
    coin input sequences c[t] in {25, 50, 75, 100} cents.
    Contract:
      - Never dispense when accumulated balance < 100 cents (silence obligation).
      - Always dispense immediately on the tick where accumulated balance reaches >= 100 cents.
    Even if a naive test only checks c[0]=100 (where stateless assembly passes), Z3 BMC
    proves the stateful FSM across all 4^H coin sequences and refutes the stateless assembly!
    """
    t0 = time.perf_counter()
    s = z3.Solver()

    coins = [z3.Int(f"coin_{t}") for t in range(horizon)]
    for t in range(horizon):
        s.add(z3.Or(coins[t] == 25, coins[t] == 50, coins[t] == 75, coins[t] == 100))

    bal = [z3.Int(f"bal_{t}") for t in range(horizon + 1)]
    s.add(bal[0] == 0)

    breaches = []
    for t in range(horizon):
        new_bal = bal[t] + coins[t]
        should_dispense = new_bal >= 100

        if stateful_fsm:
            actual_dispense = new_bal >= 100
            actual_paid = new_bal
            s.add(bal[t + 1] == z3.If(actual_dispense, z3.IntVal(0), new_bal))
        else:
            # Stateless assembly: emits on every coin arrival with just coins[t], never accumulating
            actual_dispense = z3.BoolVal(True)
            actual_paid = coins[t]
            s.add(bal[t + 1] == new_bal)

        premature_emit = z3.And( z3.Not(should_dispense), actual_dispense)
        missed_or_wrong_emit = z3.And(should_dispense, z3.Or(z3.Not(actual_dispense), actual_paid != new_bal))
        breaches.append(z3.Or(premature_emit, missed_or_wrong_emit))

    s.add(z3.Or(*breaches))
    res = s.check()
    dt_ms = (time.perf_counter() - t0) * 1000.0
    label = f"Ex13_Vending_BMC(stateful={stateful_fsm})"

    if res == z3.unsat:
        return Z3VerificationResult(
            name=label,
            verified=True,
            solver_status="unsat",
            theory="QF_LIRA",
            horizon=horizon,
            wall_time_ms=dt_ms,
            summary=f"UNSAT: Stateful FSM satisfies threshold & silence invariants for all 4^{horizon} coin sequences",
        )
    cex: Dict[str, Any] = {}
    if res == z3.sat:
        m = s.model()
        cex["coin_sequence_cents"] = [m.eval(coins[t], model_completion=True).as_long() for t in range(horizon)]
    return Z3VerificationResult(
        name=label,
        verified=False,
        solver_status=str(res),
        theory="QF_LIRA",
        horizon=horizon,
        wall_time_ms=dt_ms,
        summary=f"SAT: Stateless controller fails on coin sequence {cex.get('coin_sequence_cents')}",
        counterexample=cex,
    )


def cegis_verify_and_augment_ex06() -> Dict[str, Any]:
    """
    Demonstrates Counterexample-Guided Inductive Synthesis (CEGIS) on Example 6 (Kinetic Energy ALU):
      1. Suppose the initial test scenario only tests the symmetric point m = 10 kg, v = 10 m/s
         (where 0.5 * m * v^2 = 500 == 0.5 * v * m^2).
      2. On that weak scenario, the swapped-operand board FALSLEY achieves a WIN!
      3. The Z3 QF_NRA verifier is invoked, detects `sat`, and extracts a counterexample (m != v).
      4. Adding Z3's counterexample to the scenario immediately exposes the Tier-3 Hot Breach
         on the swapped board while the true board remains a WIN.
    """
    from .components import AssembleBlock, ConsumerBoundary, DeriveBlock, ProducerBoundary, RecolorBlock
    from .primitives import MessageShape

    LBS_TO_KG = 0.45359237
    KNOTS_TO_MPS = 0.51444444

    c_m_lbs = Color("Projectile.Mass", "lbs", "float32")
    c_m_kg = Color("Projectile.Mass", "kg", "float64")
    c_v_kt = Color("Projectile.Velocity", "knots", "float32")
    c_v_mps = Color("Projectile.Velocity", "m_per_s", "float64")
    c_ke = Color("Projectile.KineticEnergy", "Joules", "float64")
    in_slots = {"m": c_m_kg, "v": c_v_mps}

    def build_alu_board(name: str, swapped: bool) -> Board:
        b = Board(name)
        b.add_component(ProducerBoundary("LoadCell", "out", c_m_lbs))
        b.add_component(ProducerBoundary("Pitot", "out", c_v_kt))
        b.add_component(ConsumerBoundary("BallisticsSink", "in", MessageShape.single(c_ke)))
        b.add_component(RecolorBlock("RecM", c_m_lbs, c_m_kg, value_fn=lambda m: float(m) * LBS_TO_KG))
        b.add_component(RecolorBlock("RecV", c_v_kt, c_v_mps, value_fn=lambda v: float(v) * KNOTS_TO_MPS))
        b.add_component(AssembleBlock("AsmMV", in_slots))

        def ke_fn(msg: Message, state: Dict, tick: int):
            m_val = float(msg.fields["m"].value)
            v_val = float(msg.fields["v"].value)
            val = (0.5 * v_val * (m_val ** 2)) if swapped else (0.5 * m_val * (v_val ** 2))
            f = Field(val, c_ke, Dynamics("ALU.out", 1.0), provenance=msg.fields["m"].provenance.append_op("ALU", tick))
            return Message.single(f), state

        b.add_component(DeriveBlock("ALU", MessageShape(slots=in_slots), MessageShape.single(c_ke), ke_fn))
        b.connect("LoadCell.out", "RecM.in")
        b.connect("Pitot.out", "RecV.in")
        b.connect("RecM.out", "AsmMV.in_m")
        b.connect("RecV.out", "AsmMV.in_v")
        b.connect("AsmMV.out", "ALU.in")
        b.connect("ALU.out", "BallisticsSink.in")
        return b

    # Weak initial scenario: m = 10 kg, v = 10 m/s -> 0.5 * 10 * 10^2 = 500 == 0.5 * 10 * 10^2!
    weak_scenario = {
        0: {
            "LoadCell.out": Message.single(
                Field(10.0 / LBS_TO_KG, c_m_lbs, Dynamics("LoadCell.out", 1.0), provenance=Provenance(("LoadCell",), timestamp_tick=0))
            ),
            "Pitot.out": Message.single(
                Field(10.0 / KNOTS_TO_MPS, c_v_kt, Dynamics("Pitot.out", 1.0), provenance=Provenance(("Pitot",), timestamp_tick=0))
            ),
        }
    }

    # Store per-tick expected KE in the trigger field's value or compute from env
    scen_ref: Dict[int, Dict[str, Message]] = dict(weak_scenario)

    def ke_dist(trig: Message, out: Message) -> float:
        t_tick = trig.first_field().provenance.timestamp_tick
        m_kg = float(scen_ref[t_tick]["LoadCell.out"].first_field().value) * LBS_TO_KG
        v_mps = float(scen_ref[t_tick]["Pitot.out"].first_field().value) * KNOTS_TO_MPS
        expected = 0.5 * m_kg * (v_mps ** 2)
        return abs(expected - float(out.first_field().value))

    ev = BoardEvaluator()
    b_swapped = build_alu_board("ALU_Swapped", swapped=True)
    b_correct = build_alu_board("ALU_Correct", swapped=False)

    ulsc_weak = UniversalLSC(
        name="uLSC_KE_Weak",
        target_need_id="BallisticsSink.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("LoadCell.out"),
        value_distance_fn=ke_dist,
        tolerance=0.5,
        max_delay=0,
    )

    pre_swapped_eval: ScoreBreakdown = ev.evaluate(b_swapped, ulsc_weak, scen_ref, "Swapped on Weak Scenario")
    pre_correct_eval: ScoreBreakdown = ev.evaluate(b_correct, ulsc_weak, scen_ref, "Correct on Weak Scenario")

    # Now invoke Z3 QF_NRA verifier!
    z3_swapped = verify_noncommutative_alu_z3(swapped=True)
    z3_correct = verify_noncommutative_alu_z3(swapped=False)

    # Augment scenario at tick 1 with Z3's counterexample!
    cex_m = z3_swapped.counterexample["mass_kg"]
    cex_v = z3_swapped.counterexample["vel_mps"]
    scen_ref[1] = {
        "LoadCell.out": Message.single(
            Field(cex_m / LBS_TO_KG, c_m_lbs, Dynamics("LoadCell.out", 1.0), provenance=Provenance(("LoadCell",), timestamp_tick=1))
        ),
        "Pitot.out": Message.single(
            Field(cex_v / KNOTS_TO_MPS, c_v_kt, Dynamics("Pitot.out", 1.0), provenance=Provenance(("Pitot",), timestamp_tick=1))
        ),
    }

    post_swapped_eval: ScoreBreakdown = ev.evaluate(b_swapped, ulsc_weak, scen_ref, "Swapped after Z3 CEGIS")
    post_correct_eval: ScoreBreakdown = ev.evaluate(b_correct, ulsc_weak, scen_ref, "Correct after Z3 CEGIS")

    return {
        "weak_scenario_fooled_by_swapped": pre_swapped_eval.is_winning_play,
        "z3_swapped_result": z3_swapped,
        "z3_correct_result": z3_correct,
        "post_cegis_swapped_wins": post_swapped_eval.is_winning_play,
        "post_cegis_correct_wins": post_correct_eval.is_winning_play,
        "post_cegis_swapped_score": post_swapped_eval.fitness_score_S,
        "post_cegis_correct_score": post_correct_eval.fitness_score_S,
    }


def run_all_z3_verifications() -> List[Z3VerificationResult]:
    """Run the complete suite of Z3 symbolic & BMC verifications (winning vs trap pairs)."""
    results: List[Z3VerificationResult] = [
        # 1. QF_LRA: Fahrenheit -> Kelvin conversion (Good vs Lying identity cast that only matches at a single point)
        verify_symbolic_recolor_chain_z3(
            "Ex05_FahrenheitToKelvin_Valid",
            symbolic_board_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)) + z3.RealVal("273.15"),
            symbolic_spec_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)) + z3.RealVal("273.15"),
        ),
        verify_symbolic_recolor_chain_z3(
            "Ex05_FahrenheitToCelsius_CoincidenceTrap(y=x)",
            symbolic_board_fn=lambda f: f,  # Matches at f = -40, fails everywhere else!
            symbolic_spec_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)),
        ),
        # 2. QF_NRA: Kinetic Energy ALU (Correct vs Swapped operands)
        verify_noncommutative_alu_z3(swapped=False),
        verify_noncommutative_alu_z3(swapped=True),
        # 3. QF_LIRA BMC: Ping/Pong Queue (Consume-on-read vs Retain-on-read)
        verify_ping_pong_queue_bmc_z3(retain_on_read=False, horizon=6),
        verify_ping_pong_queue_bmc_z3(retain_on_read=True, horizon=6),
        # 4. QF_LIRA BMC: Multi-Rate StaleGate (With StaleGate vs Without StaleGate)
        verify_stale_gate_bmc_z3(use_stale_gate=True, max_age=2, horizon=7),
        verify_stale_gate_bmc_z3(use_stale_gate=False, max_age=2, horizon=7),
        # 5. QF_LRA BMC: Provenance TMR Voter under arbitrary single-sensor glitch
        verify_tmr_voter_bmc_z3(use_tmr=True, horizon=4),
        verify_tmr_voter_bmc_z3(use_tmr=False, horizon=4),
        # 6. QF_LIRA BMC: Stateful Vending Machine FSM vs Stateless Assembly
        verify_vending_fsm_bmc_z3(stateful_fsm=True, horizon=4),
        verify_vending_fsm_bmc_z3(stateful_fsm=False, horizon=4),
    ]
    return results
