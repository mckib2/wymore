"""
Example 7: Hard Latency Threat Avoidance (Real-Time Deadline Enforcement).
Demonstrates:
  - Strict clock deadline enforcement via UniversalLSC (`max_delay=1`)
  - Uncapped clock overrun monotonicity (5-tick delay vs 3-tick delay vs 0-tick direct DCM)
  - Polar degrees -> NED radians coordinate transformation
"""
from __future__ import annotations

import math
from typing import Dict, List

from integration_game import (
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


def example_07_latency() -> List[ScoreBreakdown]:
    c_polar = Color("Threat.Bearing", "DegPolar", "float32")
    c_ned = Color("Evade.Vector", "RadNED", "float64")
    horizon = 8

    # Threat radar emits bearing at t=0; heartbeat pulses keep pipeline stepping
    scenario = {
        t: {
            "ThreatRadar.out": Message.single(
                Field(90.0, c_polar, Dynamics("ThreatRadar.out", 1.0), provenance=Provenance(("Radar",), timestamp_tick=t))
            )
        }
        for t in range(horizon)
    }

    ulsc = UniversalLSC(
        name="uLSC_ThreatDeadline",
        target_need_id="EvasionActuator.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("ThreatRadar.out") if t == 0 else None,
        value_distance_fn=lambda trig, out: abs(
            (float(trig.first_field().value) * math.pi / 180.0) - float(out.first_field().value)
        ),
        tolerance=0.01,
        min_delay=0,
        max_delay=1,
        enforce_silence=False,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("ThreatRadar", "out", c_polar))
        b.add_component(ConsumerBoundary("EvasionActuator", "in", MessageShape.single(c_ned)))

    def make_delayed_solver(delay_ticks: int):
        def fn(msg: Message, state: Dict, tick: int):
            q = state.setdefault("q", [])
            f_in = msg.first_field()
            rad = round(float(f_in.value) * math.pi / 180.0, 5)
            f_out = Field(rad, c_ned, Dynamics("Solver.out", 1.0), provenance=f_in.provenance.append_op("Solver", tick))
            q.append((tick, Message.single(f_out)))
            if q and (tick - q[0][0]) >= delay_ticks:
                _, ready_msg = q.pop(0)
                return ready_msg, state
            return None, state

        return fn

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex7_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected threat channel"))

    # S1: Heavy 5-tick solver (arrives at t=5, overrun = 4 ticks > max_delay=1)
    b1 = Board("Ex7_S1")
    bounds(b1)
    b1.add_component(
        DeriveBlock("HeavySolver5", MessageShape.single(c_polar), MessageShape.single(c_ned), make_delayed_solver(5))
    )
    b1.connect("ThreatRadar.out", "HeavySolver5.in")
    b1.connect("HeavySolver5.out", "EvasionActuator.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: 5-tick solver (4-tick overrun)"))

    # S2: Medium 3-tick solver (arrives at t=3, overrun = 2 ticks -> strictly lower cost J than S1)
    b2 = Board("Ex7_S2")
    bounds(b2)
    b2.add_component(
        DeriveBlock("MedSolver3", MessageShape.single(c_polar), MessageShape.single(c_ned), make_delayed_solver(3))
    )
    b2.connect("ThreatRadar.out", "MedSolver3.in")
    b2.connect("MedSolver3.out", "EvasionActuator.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: 3-tick solver (2-tick overrun)"))

    # S3: Fast 0-delay DCM Recolor chain (arrives at t=0 <= max_delay=1 -> WIN)
    b3 = Board("Ex7_S3")
    bounds(b3)
    b3.add_component(
        RecolorBlock(
            "FastDCM",
            c_polar,
            c_ned,
            value_fn=lambda deg: round(float(deg) * math.pi / 180.0, 5),
        )
    )
    b3.connect("ThreatRadar.out", "FastDCM.in")
    b3.connect("FastDCM.out", "EvasionActuator.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Fast 0-tick DCM Recolor (WIN)"))

    return snaps
