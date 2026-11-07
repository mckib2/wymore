"""
Example 6: Non-Commutative Kinetic Energy / Ballistics ALU (E_k = 0.5 * m * v^2).
Demonstrates:
  - Multi-input non-commutative behavioral contract: E_k = 0.5 * m * v^2
  - Unit & precision recoloring on both operands:
      * Mass sensor in pounds (lbs, float32) -> kilograms (kg, float64)
      * Airspeed sensor in knots (knots, float32) -> meters/sec (m_per_s, float64)
  - Swapped-operand trap: satisfies Tier 1 and Tier 2 when both operands are recolored
    and assembled, but computes 0.5 * v * m^2 instead of 0.5 * m * v^2, triggering a Tier-3 breach.
"""
from __future__ import annotations

from typing import Dict, List

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    Color,
    ConsumerBoundary,
    DeriveBlock,
    Dynamics,
    Field,
    Message,
    MessageShape,
    ProducerBoundary,
    Provenance,
    RecolorBlock,
    ScoreBreakdown,
    UniversalLSC,
)

LBS_TO_KG = 0.45359237
KNOTS_TO_MPS = 0.51444444


def example_06_calculator() -> List[ScoreBreakdown]:
    c_m_lbs = Color("Projectile.Mass", "lbs", "float32")
    c_m_kg = Color("Projectile.Mass", "kg", "float64")
    c_v_kt = Color("Projectile.Velocity", "knots", "float32")
    c_v_mps = Color("Projectile.Velocity", "m_per_s", "float64")
    c_ke = Color("Projectile.KineticEnergy", "Joules", "float64")

    in_slots = {"m": c_m_kg, "v": c_v_mps}

    # 10 kg (~22.0462 lbs) at 20 m/s (~38.8769 knots) -> E_k = 0.5 * 10 * 20^2 = 2000.0 J
    m_lbs_in = 10.0 / LBS_TO_KG
    v_kt_in = 20.0 / KNOTS_TO_MPS
    horizon = 4

    scenario = {
        t: {
            "LoadCell.out": Message.single(
                Field(m_lbs_in, c_m_lbs, Dynamics("LoadCell.out", 1.0), provenance=Provenance(("LoadCell",), timestamp_tick=t))
            ),
            "Pitot.out": Message.single(
                Field(v_kt_in, c_v_kt, Dynamics("Pitot.out", 1.0), provenance=Provenance(("Pitot",), timestamp_tick=t))
            ),
        }
        for t in (0, 2)
    }

    def ke_error(trig: Message, out: Message) -> float:
        m_kg = float(trig.first_field().value) * LBS_TO_KG
        v_mps = 20.0
        expected_ke = 0.5 * m_kg * (v_mps ** 2)
        return abs(expected_ke - float(out.first_field().value))

    ulsc = UniversalLSC(
        name="uLSC_KineticEnergy",
        target_need_id="BallisticsSink.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("LoadCell.out"),
        value_distance_fn=ke_error,
        tolerance=1.0,
        max_delay=1,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("LoadCell", "out", c_m_lbs))
        b.add_component(ProducerBoundary("Pitot", "out", c_v_kt))
        b.add_component(ConsumerBoundary("BallisticsSink", "in", MessageShape.single(c_ke)))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex6_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected operands"))

    # S1: Recolor Mass (lbs->kg, f32->f64) and Velocity (knots->m/s, f32->f64) + Assemble
    b1 = Board("Ex6_S1")
    bounds(b1)
    b1.add_component(
        RecolorBlock("RecM", c_m_lbs, c_m_kg, value_fn=lambda m: round(float(m) * LBS_TO_KG, 4))
    )
    b1.add_component(
        RecolorBlock("RecV", c_v_kt, c_v_mps, value_fn=lambda v: round(float(v) * KNOTS_TO_MPS, 4))
    )
    b1.add_component(AssembleBlock("AsmMV", in_slots))
    b1.connect("LoadCell.out", "RecM.in")
    b1.connect("Pitot.out", "RecV.in")
    b1.connect("RecM.out", "AsmMV.in_m")
    b1.connect("RecV.out", "AsmMV.in_v")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: +Recolor (kg, m/s) & Assemble"))

    # S2: Swapped-operand trap (computes 0.5 * v * m^2 = 1000 J instead of 0.5 * m * v^2 = 2000 J)
    def swapped_ke(msg: Message, state: Dict, tick: int):
        m = float(msg.fields["m"].value)
        v = float(msg.fields["v"].value)
        val = 0.5 * v * (m ** 2)  # Swapped m and v!
        f = Field(val, c_ke, Dynamics("ALU.out", 1.0), provenance=msg.fields["m"].provenance.append_op("ALU", tick))
        return Message.single(f), state

    b2 = b1.clone("Ex6_S2")
    b2.add_component(DeriveBlock("ALU", MessageShape(slots=in_slots), MessageShape.single(c_ke), swapped_ke))
    b2.connect("AsmMV.out", "ALU.in")
    b2.connect("ALU.out", "BallisticsSink.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Swapped operands 0.5*v*m^2 (Tier3 fail)"))

    # S3: Correct operand order 0.5 * m * v^2 = 2000 J (WIN)
    def correct_ke(msg: Message, state: Dict, tick: int):
        m = float(msg.fields["m"].value)
        v = float(msg.fields["v"].value)
        val = 0.5 * m * (v ** 2)
        f = Field(val, c_ke, Dynamics("ALU.out", 1.0), provenance=msg.fields["m"].provenance.append_op("ALU", tick))
        return Message.single(f), state

    b3 = b1.clone("Ex6_S3")
    b3.add_component(DeriveBlock("ALU", MessageShape(slots=in_slots), MessageShape.single(c_ke), correct_ke))
    b3.connect("AsmMV.out", "ALU.in")
    b3.connect("ALU.out", "BallisticsSink.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Correct 0.5*m*v^2 ALU (WIN)"))

    return snaps
