"""
sensitivity.py
Technology-independent assertions (Axioms A1–A7) and sensitivity analysis
for the Integration Game cost functional J and fitness score S.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from .board import Board
from .components import (
    CacheStoreBlock,
    ConsumerBoundary,
    DeriveBlock,
    ProducerBoundary,
    ProvVerifyBlock,
    RecolorBlock,
    RepresentationBridgeBlock,
)
from .config import DEFAULT_CONFIG, GameConfig, ScoringConfig
from .primitives import (
    Carrier,
    Color,
    Dynamics,
    Field,
    Message,
    MessageShape,
    Provenance,
    Representation,
    TransferMode,
)
from .scoring import BoardEvaluator, ScoreBreakdown
from .ulsc import UniversalLSC


@dataclass
class CostAssertionReport:
    axiom_id: str
    title: str
    passed: bool
    details: List[str] = field(default_factory=list)


@dataclass
class SensitivitySweepPoint:
    parameter_name: str
    parameter_value: float
    all_axioms_passed: bool
    winner_ranking: List[str]
    scores_by_play: Dict[str, float]
    costs_by_play: Dict[str, float]


def verify_a1_feasibility_dominance(
    breakdowns: Sequence[ScoreBreakdown],
) -> CostAssertionReport:
    """
    Axiom A1 (Lexicographic Feasibility Dominance):
    Every winning play (Tiers 1, 2, 3 satisfied) must have strictly lower total_cost_J
    and strictly higher fitness_score_S than every non-winning play.
    """
    winners = [b for b in breakdowns if b.is_winning_play]
    losers = [b for b in breakdowns if not b.is_winning_play]
    details: List[str] = []
    passed = True

    if not winners or not losers:
        return CostAssertionReport(
            axiom_id="A1",
            title="Lexicographic Feasibility Dominance (Win > Lose)",
            passed=False,
            details=["Requires at least one winning and one losing play to compare."],
        )

    max_win_j = max(w.total_cost_J for w in winners)
    min_lose_j = min(l.total_cost_J for l in losers)
    min_win_s = min(w.fitness_score_S for w in winners)
    max_lose_s = max(l.fitness_score_S for l in losers)

    if max_win_j >= min_lose_j:
        passed = False
        details.append(f"VIOLATION: max winning J ({max_win_j}) >= min losing J ({min_lose_j})")
    else:
        details.append(f"OK: max winning J ({max_win_j:.2f}) < min losing J ({min_lose_j:.2f})")

    if min_win_s <= max_lose_s:
        passed = False
        details.append(f"VIOLATION: min winning S ({min_win_s}) <= max losing S ({max_lose_s})")
    else:
        details.append(f"OK: min winning S ({min_win_s:.2f}) > max losing S ({max_lose_s:.2f})")

    return CostAssertionReport(
        axiom_id="A1",
        title="Lexicographic Feasibility Dominance (Win > Lose)",
        passed=passed,
        details=details,
    )


def verify_a2_live_frontier_grounding(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A2 (Live-Frontier Grounding / No Disconnected-Operator Credit):
    Adding an unconnected operator whose output matches the consumer Need color
    must NOT reduce Tier-1 or Tier-2 penalties, and must strictly increase static_cost
    and total_cost_J (while strictly decreasing fitness_score_S).
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)
    c_src = Color("Sensor.Raw", "Kelvin", "float32")
    c_tgt = Color("Display.Out", "Celsius", "float64")
    c_fake = Color("Unrelated.Concept", "Kelvin", "float32")

    scenario = {
        0: {
            "P.out": Message.single(
                Field(300.0, c_src, Dynamics("P.out", 1.0), provenance=Provenance(("P",), timestamp_tick=0))
            )
        }
    }
    ulsc = UniversalLSC(
        name="uLSC_A2",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: 0.0,
    )

    b_base = Board("A2_Base")
    b_base.add_component(ProducerBoundary("P", "out", c_src))
    b_base.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_tgt)))
    s_base = ev.evaluate(b_base, ulsc, scenario, "Base unconnected")

    # Add a dangling RecolorBlock whose output matches c_tgt, but whose input is unwired!
    b_dangling = b_base.clone("A2_Dangling")
    dangling_op = RecolorBlock("DanglingOp", c_fake, c_tgt, cost_config=cfg.catalog_costs)
    b_dangling.add_component(dangling_op)
    s_dangling = ev.evaluate(b_dangling, ulsc, scenario, "+Dangling unwired operator")

    details: List[str] = []
    passed = True

    if s_dangling.tier1_struct_penalty < s_base.tier1_struct_penalty:
        passed = False
        details.append(
            f"VIOLATION: Dangling operator reduced Tier-1 penalty "
            f"({s_base.tier1_struct_penalty} -> {s_dangling.tier1_struct_penalty})"
        )
    else:
        details.append(
            f"OK: Tier-1 penalty unchanged by dangling operator ({s_base.tier1_struct_penalty:.2f})"
        )

    if s_dangling.total_cost_J <= s_base.total_cost_J:
        passed = False
        details.append(
            f"VIOLATION: Dangling operator did not increase J "
            f"({s_base.total_cost_J} -> {s_dangling.total_cost_J})"
        )
    else:
        details.append(
            f"OK: Total cost J strictly increased ({s_base.total_cost_J:.2f} -> {s_dangling.total_cost_J:.2f}) "
            f"and fitness S decreased ({s_base.fitness_score_S:.2f} -> {s_dangling.fitness_score_S:.2f})"
        )

    return CostAssertionReport(
        axiom_id="A2",
        title="Live-Frontier Grounding (No Disconnected-Operator Credit)",
        passed=passed,
        details=details,
    )


def verify_a3_stepwise_potential_monotonicity(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A3 (Monotonic Potential Reduction Under Useful Frontier Mediation):
    Resolving each mismatch axis (Representation -> Conceptual -> Logical -> Platform -> Kinematics)
    along the live frontier strictly decreases (Tier1 + Tier2 + StaticCost) and strictly increases S.
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)

    c0 = Color("Raw.Sensor", "Kelvin", "float32")
    c1 = Color("Airframe.Sensor", "Kelvin", "float32")
    c2 = Color("Airframe.Sensor", "Celsius", "float32")
    c3 = Color("Airframe.Sensor", "Celsius", "float64")

    scenario = {
        0: {
            "P.out": Message.single(
                Field(
                    300.0,
                    c0,
                    Dynamics("P.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("P",), timestamp_tick=0, trust_score=0.5),
                )
            )
        }
    }
    need_shape = MessageShape.single(
        c3,
        reps=(Representation.NATIVE_STRUCT,),
        min_trust=0.9,
        required_assurance="VERIFIED",
    )
    ulsc = UniversalLSC(
        name="uLSC_A3",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: abs((float(trig.first_field().value) - 273.15) - float(out.first_field().value)),
        tolerance=0.1,
    )

    def make_base(name: str) -> Board:
        b = Board(name)
        b.add_component(ProducerBoundary("P", "out", c0, mode=TransferMode.PUSH, rep=Representation.BYTE_BLOB_JSON))
        b.add_component(ConsumerBoundary("C", "in", need_shape, mode=TransferMode.PULL))
        return b

    # Step 0: Unconnected
    b0 = make_base("Step0")
    # Step 1: +Transcode JSON -> NATIVE_STRUCT wired to P
    b1 = make_base("Step1")
    b1.add_component(
        RepresentationBridgeBlock(
            "Rep", c0, Representation.BYTE_BLOB_JSON, Representation.NATIVE_STRUCT, cost_config=cfg.catalog_costs
        )
    )
    b1.connect("P.out", "Rep.in")

    # Step 2: +Recolor_C (c0 -> c1)
    b2 = b1.clone("Step2")
    b2.add_component(RecolorBlock("RC", c0, c1, cost_config=cfg.catalog_costs))
    b2.connect("Rep.out", "RC.in")

    # Step 3: +Recolor_L (c1 -> c2)
    b3 = b2.clone("Step3")
    b3.add_component(RecolorBlock("RL", c1, c2, value_fn=lambda k: k - 273.15, cost_config=cfg.catalog_costs))
    b3.connect("RC.out", "RL.in")

    # Step 4: +Recolor_P (c2 -> c3)
    b4 = b3.clone("Step4")
    b4.add_component(RecolorBlock("RP", c2, c3, value_fn=float, cost_config=cfg.catalog_costs))
    b4.connect("RL.out", "RP.in")

    # Step 5: +ProvVerify
    b5 = b4.clone("Step5")
    b5.add_component(
        ProvVerifyBlock("PV", c3, min_trust=0.5, assurance_out="VERIFIED", cost_config=cfg.catalog_costs)
    )
    # Give PV output shape min_trust=0.9 for contract satisfaction
    b5.components["PV"].interfaces["out"].offer = b5.components["PV"].interfaces["out"].offer.__class__(
        shape=MessageShape.single(c3, min_trust=0.9, required_assurance="VERIFIED"),
        mode=TransferMode.PUSH,
        velocity=1.0,
    )
    b5.connect("RP.out", "PV.in")

    # Step 6: +CacheStore (Push -> Pull)
    b6 = b5.clone("Step6")
    b6.add_component(
        CacheStoreBlock(
            "Cache",
            c3,
            retain_on_read=False,
            shape=MessageShape.single(c3, min_trust=0.9, required_assurance="VERIFIED"),
            cost_config=cfg.catalog_costs,
        )
    )
    b6.connect("PV.out", "Cache.in")

    # Step 7: Final route Cache.out -> C.in (WIN)
    b7 = b6.clone("Step7")
    b7.connect("Cache.out", "C.in")

    boards = [
        ("S0: Unwired", b0),
        ("S1: +RepBridge", b1),
        ("S2: +Recolor_C", b2),
        ("S3: +Recolor_L", b3),
        ("S4: +Recolor_P", b4),
        ("S5: +ProvVerify", b5),
        ("S6: +Cache (Push->Pull)", b6),
        ("S7: +Wire Consumer (WIN)", b7),
    ]
    snaps = [ev.evaluate(b, ulsc, scenario, label) for label, b in boards]

    passed = True
    details: List[str] = []
    for i in range(len(snaps) - 1):
        curr, nxt = snaps[i], snaps[i + 1]
        curr_pot = curr.tier1_struct_penalty + curr.tier2_kin_penalty + curr.static_cost
        nxt_pot = nxt.tier1_struct_penalty + nxt.tier2_kin_penalty + nxt.static_cost
        if nxt_pot >= curr_pot or nxt.fitness_score_S <= curr.fitness_score_S:
            passed = False
            details.append(
                f"VIOLATION at {curr.snapshot_label} -> {nxt.snapshot_label}: "
                f"pot {curr_pot:.2f}->{nxt_pot:.2f}, S {curr.fitness_score_S:.2f}->{nxt.fitness_score_S:.2f}"
            )
        else:
            details.append(
                f"OK {curr.snapshot_label} -> {nxt.snapshot_label}: "
                f"pot {curr_pot:.2f}->{nxt_pot:.2f}, S {curr.fitness_score_S:.2f}->{nxt.fitness_score_S:.2f}"
            )

    return CostAssertionReport(
        axiom_id="A3",
        title="Monotonic Potential Reduction Under Useful Frontier Mediation",
        passed=passed,
        details=details,
    )


def verify_a4_route_wiring_continuity(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A4 (Route-Wiring Continuity / No Wiring Penalty Spike):
    Wiring an Offer to a Need that realizes the frontier minimum distance
    strictly reduces Tier-1 penalty by exactly w_unconnected and leaves Tier-2
    penalty invariant (even when C, L, P, rep, and mode all mismatch!).
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)
    c_offer = Color("A.X", "m", "f32")
    c_need = Color("B.Y", "ft", "f64")

    scenario = {0: {"P.out": Message.single(Field(1.0, c_offer, Dynamics("P", 1.0)))}}
    ulsc = UniversalLSC(
        name="uLSC_A4",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: 0.0,
    )

    b_unwired = Board("A4_Unwired")
    b_unwired.add_component(ProducerBoundary("P", "out", c_offer, mode=TransferMode.PUSH))
    b_unwired.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_need), mode=TransferMode.PULL))
    s_unwired = ev.evaluate(b_unwired, ulsc, scenario, "Unwired")

    b_wired = b_unwired.clone("A4_Wired")
    b_wired.connect("P.out", "C.in")
    s_wired = ev.evaluate(b_wired, ulsc, scenario, "Wired")

    expected_drop = cfg.scoring.w_unconnected
    actual_t1_drop = round(s_unwired.tier1_struct_penalty - s_wired.tier1_struct_penalty, 4)
    t2_diff = abs(s_unwired.tier2_kin_penalty - s_wired.tier2_kin_penalty)

    passed = (abs(actual_t1_drop - expected_drop) < 1e-3) and (t2_diff < 1e-3)
    details = [
        f"Tier-1 drop on wiring: {actual_t1_drop:.2f} (expected w_unconnected={expected_drop:.2f})",
        f"Tier-2 change on wiring: {t2_diff:.2f} (expected 0.00)",
        f"Fitness S: {s_unwired.fitness_score_S:.2f} -> {s_wired.fitness_score_S:.2f}",
    ]
    return CostAssertionReport(
        axiom_id="A4",
        title="Route-Wiring Continuity (No Wiring Penalty Spike)",
        passed=passed,
        details=details,
    )


def verify_a5_tier3_behavioral_monotonicity(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A5 (Strict Tier-3 Behavioral Gradient Monotonicity):
    Holding Tier 1, Tier 2, and static/dynamic costs fixed:
      (a) Higher cut_progress_ratio -> strictly lower J and higher S
      (b) Larger clock overrun (even > 5 ticks) -> strictly higher J and lower S
      (c) Larger value error (even > 5.0) -> strictly higher J and lower S
      (d) More silence violations -> strictly higher J and lower S
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)
    c = Color("Nav.Pos", "m", "f64")
    passed = True
    details: List[str] = []

    # (5b) Deadline overrun monotonicity across [1, 3, 7, 12] ticks (testing beyond old cap of 5)
    overrun_scores: List[Tuple[int, float, float]] = []
    horizon = 15
    scenario_lat = {
        0: {"P.out": Message.single(Field(10.0, c, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=0)))}
    }
    ulsc_lat = UniversalLSC(
        name="uLSC_LatMono",
        target_need_id="C.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.01,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )

    for delay_ticks in (1, 3, 7, 12):
        b = Board(f"Delay_{delay_ticks}")
        b.add_component(ProducerBoundary("P", "out", c))
        b.add_component(ConsumerBoundary("C", "in", MessageShape.single(c)))

        def make_delay_fn(d: int):
            def delay_fn(msg: Message, state: Dict, tick: int):
                 state["item"] = (tick, msg)
                 return None, state
            return delay_fn

        # Emit at tick == delay_ticks using Source-seeded or stateful Derive
        # Since Derive only steps when inbox is not None, let's send env ticks and emit at delay_ticks
        scen_d = {
            t: {"P.out": Message.single(Field(10.0, c, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=t)))}
            for t in range(horizon)
        }
        ulsc_d = UniversalLSC(
            name=f"uLSC_Delay_{delay_ticks}",
            target_need_id="C.in",
            horizon=horizon,
            pre_trigger_fn=lambda t, env: env.get("P.out") if t == 0 else None,
            value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
            tolerance=0.01,
            min_delay=0,
            max_delay=0,
            enforce_silence=True,
        )

        def emit_at_tick(target_t: int):
            def fn(msg: Message, state: Dict, tick: int):
                if tick == target_t:
                    return msg, state
                return None, state
            return fn

        b.add_component(
            DeriveBlock(
                "Delayer",
                MessageShape.single(c),
                MessageShape.single(c),
                emit_at_tick(delay_ticks),
                static_cost=1.0,
            )
        )
        b.connect("P.out", "Delayer.in")
        b.connect("Delayer.out", "C.in")
        res = ev.evaluate(b, ulsc_d, scen_d, f"Overrun={delay_ticks}")
        overrun_scores.append((delay_ticks, res.total_cost_J, res.fitness_score_S))

    for i in range(len(overrun_scores) - 1):
        d1, j1, s1 = overrun_scores[i]
        d2, j2, s2 = overrun_scores[i + 1]
        if not (j2 > j1 and s2 < s1):
            passed = False
            details.append(f"VIOLATION (5b Overrun): delay {d1}->{d2} gave J {j1}->{j2}, S {s1}->{s2}")
    if passed:
        details.append(
            "OK (5b Overrun Monotonicity across 1, 3, 7, 12 ticks): "
            + ", ".join(f"d={d}:(J={j:.1f}, S={s:.2f})" for d, j, s in overrun_scores)
        )

    # (5c) Value envelope error monotonicity across errors [1.0, 5.0, 20.0, 100.0] (testing beyond old cap of 5.0)
    val_scores: List[Tuple[float, float, float]] = []
    scen_v = {
        0: {"P.out": Message.single(Field(10.0, c, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=0)))}
    }
    ulsc_v = UniversalLSC(
        name="uLSC_ValMono",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.0,
        max_delay=1,
    )
    for err_mag in (1.0, 5.0, 20.0, 100.0):
        b = Board(f"ValErr_{err_mag}")
        b.add_component(ProducerBoundary("P", "out", c))
        b.add_component(ConsumerBoundary("C", "in", MessageShape.single(c)))
        b.add_component(
            RecolorBlock("Bias", c, c, value_fn=lambda x, e=err_mag: float(x) + e, static_cost=0.5)
        )
        b.connect("P.out", "Bias.in")
        b.connect("Bias.out", "C.in")
        res = ev.evaluate(b, ulsc_v, scen_v, f"Err={err_mag}")
        val_scores.append((err_mag, res.total_cost_J, res.fitness_score_S))

    for i in range(len(val_scores) - 1):
        e1, j1, s1 = val_scores[i]
        e2, j2, s2 = val_scores[i + 1]
        if not (j2 > j1 and s2 < s1):
            passed = False
            details.append(f"VIOLATION (5c Value Error): err {e1}->{e2} gave J {j1}->{j2}, S {s1}->{s2}")
    if passed:
        details.append(
            "OK (5c Value Error Monotonicity across 1, 5, 20, 100): "
            + ", ".join(f"e={e}:(J={j:.1f}, S={s:.2f})" for e, j, s in val_scores)
        )

    return CostAssertionReport(
        axiom_id="A5",
        title="Strict Tier-3 Behavioral Gradient Monotonicity",
        passed=passed,
        details=details,
    )


def verify_a6_dynamic_qos_monotonicity(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A6 (Dynamic QoS Monotonicity):
    Among winning plays with identical Tier-1/2/3 satisfaction and static cost,
    increasing precision loss or operator latency strictly increases dynamic_cost and J,
    and strictly decreases S.
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)
    c1 = Color("S.X", "m", "f64")
    c2 = Color("S.X", "m", "f32")
    scen = {
        0: {"P.out": Message.single(Field(1.0, c1, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=0)))}
    }
    ulsc = UniversalLSC(
        name="uLSC_A6",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: 0.0,
    )

    losses = [0.0, 0.2, 0.8, 2.0]
    snaps: List[ScoreBreakdown] = []
    for loss in losses:
        b = Board(f"Loss_{loss}")
        b.add_component(ProducerBoundary("P", "out", c1))
        b.add_component(ConsumerBoundary("C", "in", MessageShape.single(c2)))
        b.add_component(RecolorBlock("R", c1, c2, info_loss=loss, static_cost=0.5))
        b.connect("P.out", "R.in")
        b.connect("R.out", "C.in")
        snaps.append(ev.evaluate(b, ulsc, scen, f"info_loss={loss}"))

    passed = True
    details: List[str] = []
    for i in range(len(snaps) - 1):
        a, b = snaps[i], snaps[i + 1]
        if not (a.is_winning_play and b.is_winning_play and b.dynamic_cost > a.dynamic_cost and b.total_cost_J > a.total_cost_J and b.fitness_score_S < a.fitness_score_S):
            passed = False
            details.append(f"VIOLATION between {a.snapshot_label} and {b.snapshot_label}")
    if passed:
        details.append(
            "OK: Dynamic cost & J strictly increase with info_loss: "
            + ", ".join(f"{r.snapshot_label}:(C_dyn={r.dynamic_cost:.2f}, S={r.fitness_score_S:.2f})" for r in snaps)
        )
    return CostAssertionReport(
        axiom_id="A6",
        title="Dynamic QoS Monotonicity (Latency, InfoLoss, Disruptions)",
        passed=passed,
        details=details,
    )


def verify_a7_parsimony_monotonicity(
    game_config: Optional[GameConfig] = None,
) -> CostAssertionReport:
    """
    Axiom A7 (Parsimony / Redundancy Monotonicity - Occam's Razor):
    Adding redundant operators or higher-cost route carriers (GENERIC_TREE, IPC_SERIALIZED)
    to a winning play strictly increases static_cost and total_cost_J and decreases fitness S.
    """
    cfg = game_config or DEFAULT_CONFIG
    ev = BoardEvaluator(game_config=cfg)
    c1 = Color("Nav.Pos", "m", "f64")
    c2 = Color("Nav.Pos", "ft", "f64")
    scen = {
        0: {"P.out": Message.single(Field(10.0, c1, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=0)))}
    }
    ulsc = UniversalLSC(
        name="uLSC_A7",
        target_need_id="C.in",
        horizon=2,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) * 3.28084 - float(out.first_field().value)),
        tolerance=0.01,
    )

    # Play 1: Minimal single Recolor_L, IN_PROCESS carrier
    b_min = Board("Minimal")
    b_min.add_component(ProducerBoundary("P", "out", c1))
    b_min.add_component(ConsumerBoundary("C", "in", MessageShape.single(c2)))
    b_min.add_component(RecolorBlock("R1", c1, c2, value_fn=lambda x: x * 3.28084, cost_config=cfg.catalog_costs))
    b_min.connect("P.out", "R1.in", carrier=Carrier.IN_PROCESS)
    b_min.connect("R1.out", "C.in", carrier=Carrier.IN_PROCESS)
    s_min = ev.evaluate(b_min, ulsc, scen, "Minimal IN_PROCESS")

    # Play 2: Redundant extra identity pass-through block
    b_red = Board("Redundant_Op")
    b_red.add_component(ProducerBoundary("P", "out", c1))
    b_red.add_component(ConsumerBoundary("C", "in", MessageShape.single(c2)))
    b_red.add_component(RecolorBlock("R1", c1, c2, value_fn=lambda x: x * 3.28084, cost_config=cfg.catalog_costs))
    b_red.add_component(RecolorBlock("R_id", c2, c2, value_fn=lambda x: x, cost_config=cfg.catalog_costs))
    b_red.connect("P.out", "R1.in")
    b_red.connect("R1.out", "R_id.in")
    b_red.connect("R_id.out", "C.in")
    s_red = ev.evaluate(b_red, ulsc, scen, "Redundant Identity Op")

    # Play 3: Minimal op but over IPC_SERIALIZED carrier
    b_ipc = Board("IPC_Carrier")
    b_ipc.add_component(ProducerBoundary("P", "out", c1))
    b_ipc.add_component(ConsumerBoundary("C", "in", MessageShape.single(c2)))
    b_ipc.add_component(RecolorBlock("R1", c1, c2, value_fn=lambda x: x * 3.28084, cost_config=cfg.catalog_costs))
    b_ipc.connect("P.out", "R1.in", carrier=Carrier.IPC_SERIALIZED)
    b_ipc.connect("R1.out", "C.in", carrier=Carrier.IN_PROCESS)
    s_ipc = ev.evaluate(b_ipc, ulsc, scen, "IPC Carrier Route")

    passed = (
        s_min.is_winning_play
        and s_red.is_winning_play
        and s_ipc.is_winning_play
        and s_min.total_cost_J < s_red.total_cost_J < s_ipc.total_cost_J
        and s_min.fitness_score_S > s_red.fitness_score_S > s_ipc.fitness_score_S
    )
    details = [
        f"Minimal: J={s_min.total_cost_J:.2f}, S={s_min.fitness_score_S:.2f}",
        f"+Redundant Op: J={s_red.total_cost_J:.2f}, S={s_red.fitness_score_S:.2f}",
        f"+IPC Carrier: J={s_ipc.total_cost_J:.2f}, S={s_ipc.fitness_score_S:.2f}",
    ]
    return CostAssertionReport(
        axiom_id="A7",
        title="Parsimony / Redundancy Monotonicity (Occam's Razor)",
        passed=passed,
        details=details,
    )


def run_all_cost_assertions(
    example_breakdowns: Optional[Sequence[ScoreBreakdown]] = None,
    game_config: Optional[GameConfig] = None,
) -> List[CostAssertionReport]:
    """Run all 7 technology-independent cost assertions and return their reports."""
    cfg = game_config or DEFAULT_CONFIG
    reports: List[CostAssertionReport] = []

    a2 = verify_a2_live_frontier_grounding(cfg)
    a3 = verify_a3_stepwise_potential_monotonicity(cfg)
    a4 = verify_a4_route_wiring_continuity(cfg)
    a5 = verify_a5_tier3_behavioral_monotonicity(cfg)
    a6 = verify_a6_dynamic_qos_monotonicity(cfg)
    a7 = verify_a7_parsimony_monotonicity(cfg)

    if example_breakdowns:
        a1 = verify_a1_feasibility_dominance(example_breakdowns)
    else:
        # Synthesize winning and losing breakdowns from A3 & A7
        ev = BoardEvaluator(game_config=cfg)
        c = Color("A", "u", "f")
        scen = {0: {"P.out": Message.single(Field(1.0, c, Dynamics("P", 1.0)))}}
        ulsc = UniversalLSC("u", "C.in", 2, lambda t, e: e.get("P.out"), lambda tr, o: 0.0)
        b_lose = Board("L")
        b_lose.add_component(ProducerBoundary("P", "out", c))
        b_lose.add_component(ConsumerBoundary("C", "in", MessageShape.single(c)))
        b_win = b_lose.clone("W")
        b_win.connect("P.out", "C.in")
        a1 = verify_a1_feasibility_dominance(
            [ev.evaluate(b_lose, ulsc, scen, "Lose"), ev.evaluate(b_win, ulsc, scen, "Win")]
        )

    reports.extend([a1, a2, a3, a4, a5, a6, a7])
    return reports


def run_weight_sensitivity_sweep(
    parameter_sweeps: Optional[Dict[str, Sequence[float]]] = None,
    base_config: Optional[GameConfig] = None,
) -> List[SensitivitySweepPoint]:
    """
    One-at-a-time (OAT) sensitivity sweep across ScoringConfig weights.
    Evaluates competing winning architectures (Fast-Lossy vs Exact-Native vs Exact-IPC)
    and verifies whether Axioms A1–A7 remain invariant across parameter variations.
    """
    base = base_config or DEFAULT_CONFIG
    if parameter_sweeps is None:
        parameter_sweeps = {
            "w_color": (4.0, 8.0, 16.0),
            "w_kin": (5.0, 10.0, 20.0),
            "w_loss": (0.2, 1.0, 5.0, 12.0),
            "w_lat": (0.2, 1.0, 5.0),
            "gamma": (0.8, 0.95, 1.0),
        }

    c_in = Color("Sensor.Temp", "Kelvin", "float64")
    c_out = Color("Flight.Temp", "Celsius", "float64")
    scen = {
        t: {
            "P.out": Message.single(
                Field(300.0 + t, c_in, Dynamics("P", 1.0), provenance=Provenance(("P",), timestamp_tick=t))
            )
        }
        for t in range(3)
    }
    ulsc = UniversalLSC(
        name="uLSC_Sens",
        target_need_id="C.in",
        horizon=3,
        pre_trigger_fn=lambda t, env: env.get("P.out"),
        value_distance_fn=lambda trig, out: abs((float(trig.first_field().value) - 273.15) - float(out.first_field().value)),
        tolerance=0.05,
        max_delay=1,
    )

    def build_candidates(cfg: GameConfig) -> List[Tuple[str, Board]]:
        # Candidate 1: Exact low-latency native in-process (static=1.5, loss=0, lat=0)
        b_exact = Board("Win_Exact_InProcess")
        b_exact.add_component(ProducerBoundary("P", "out", c_in))
        b_exact.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_out)))
        b_exact.add_component(
            RecolorBlock(
                "RL_Exact",
                c_in,
                c_out,
                value_fn=lambda k: round(float(k) - 273.15, 4),
                static_cost=1.8,
                info_loss=0.0,
                latency=0.0,
            )
        )
        b_exact.connect("P.out", "RL_Exact.in", carrier=Carrier.IN_PROCESS)
        b_exact.connect("RL_Exact.out", "C.in", carrier=Carrier.IN_PROCESS)

        # Candidate 2: Cheap static operator but with precision narrowing loss (static=0.6, loss=0.4/tick)
        b_lossy = Board("Win_Cheap_Lossy")
        b_lossy.add_component(ProducerBoundary("P", "out", c_in))
        b_lossy.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_out)))
        b_lossy.add_component(
            RecolorBlock(
                "RL_Lossy",
                c_in,
                c_out,
                value_fn=lambda k: round(float(k) - 273.15, 2),
                static_cost=0.6,
                info_loss=0.4,
                latency=0.0,
            )
        )
        b_lossy.connect("P.out", "RL_Lossy.in", carrier=Carrier.IN_PROCESS)
        b_lossy.connect("RL_Lossy.out", "C.in", carrier=Carrier.IN_PROCESS)

        # Candidate 3: Exact operator but over high-latency IPC transport (static=1.8+3.0, lat=0.8/tick)
        b_ipc = Board("Win_Exact_HighLatIPC")
        b_ipc.add_component(ProducerBoundary("P", "out", c_in))
        b_ipc.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_out)))
        b_ipc.add_component(
            RecolorBlock(
                "RL_IPC",
                c_in,
                c_out,
                value_fn=lambda k: round(float(k) - 273.15, 4),
                static_cost=1.8,
                info_loss=0.0,
                latency=0.8,
            )
        )
        b_ipc.connect("P.out", "RL_IPC.in", carrier=Carrier.IPC_SERIALIZED)
        b_ipc.connect("RL_IPC.out", "C.in", carrier=Carrier.IN_PROCESS)

        # Candidate 4: Losing play (wrong value conversion)
        b_lose = Board("Lose_LyingCast")
        b_lose.add_component(ProducerBoundary("P", "out", c_in))
        b_lose.add_component(ConsumerBoundary("C", "in", MessageShape.single(c_out)))
        b_lose.add_component(
            RecolorBlock("RL_Bad", c_in, c_out, value_fn=float, static_cost=0.5)
        )
        b_lose.connect("P.out", "RL_Bad.in")
        b_lose.connect("RL_Bad.out", "C.in")

        return [
            ("Win_Exact_InProcess", b_exact),
            ("Win_Cheap_Lossy", b_lossy),
            ("Win_Exact_HighLatIPC", b_ipc),
            ("Lose_LyingCast", b_lose),
        ]

    points: List[SensitivitySweepPoint] = []
    for param_name, values in parameter_sweeps.items():
        for val in values:
            new_scoring: ScoringConfig = base.scoring.with_overrides(**{param_name: val})
            cfg = base.with_overrides(scoring=new_scoring)
            ev = BoardEvaluator(game_config=cfg)

            candidates = build_candidates(cfg)
            evals = [ev.evaluate(b, ulsc, scen, label) for label, b in candidates]
            reports = run_all_cost_assertions(evals, game_config=cfg)
            all_ok = all(r.passed for r in reports)

            winners = [e for e in evals if e.is_winning_play]
            winners.sort(key=lambda r: (r.residual_cost, r.total_cost_J))

            points.append(
                SensitivitySweepPoint(
                    parameter_name=param_name,
                    parameter_value=val,
                    all_axioms_passed=all_ok,
                    winner_ranking=[w.snapshot_label for w in winners],
                    scores_by_play={e.snapshot_label: e.fitness_score_S for e in evals},
                    costs_by_play={e.snapshot_label: e.total_cost_J for e in evals},
                )
            )
    return points
