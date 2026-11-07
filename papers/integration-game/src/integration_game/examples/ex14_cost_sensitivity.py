"""
Example 14: Cost Sensitivity & Pareto Architecture Comparison.
Demonstrates how the cost functional J and fitness score S rank 5 competing architectures
for the same boundary problem:
  1. Arch 1 (LOSE - Deadline Breach): 2-tick latency violates max_delay=1
  2. Arch 2 (WIN - High IPC Carrier + Latency): IPC_SERIALIZED carrier + operator latency
  3. Arch 3 (WIN - Lossy Narrowing Cast): Intermediate float32 precision loss (info_loss > 0)
  4. Arch 4 (WIN - Redundant Identity Op): Extra no-op RecolorBlock (violates minimal parsimony)
  5. Arch 5 (WIN - Pareto Optimal): Single lossless RecolorBlock over IN_PROCESS carrier
"""
from __future__ import annotations

import math
from typing import Dict, List

from integration_game import (
    Board,
    BoardEvaluator,
    Carrier,
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

DEG_TO_RAD = math.pi / 180.0


def example_14_cost_sensitivity() -> List[ScoreBreakdown]:
    c_deg = Color("Gimbal.Angle", "deg", "float64")
    c_rad_f32 = Color("Gimbal.Angle", "rad", "float32")
    c_rad = Color("Gimbal.Angle", "rad", "float64")
    horizon = 4

    scenario = {
        t: {
            "Encoder.out": Message.single(
                Field(45.0, c_deg, Dynamics("Encoder.out", 1.0), provenance=Provenance(("Encoder",), timestamp_tick=t))
            )
        }
        for t in range(horizon)
    }

    ulsc = UniversalLSC(
        name="uLSC_PointingPareto",
        target_need_id="PointingLoop.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Encoder.out") if t == 0 else None,
        value_distance_fn=lambda trig, out: abs(45.0 * DEG_TO_RAD - float(out.first_field().value)),
        tolerance=0.01,
        min_delay=0,
        max_delay=1,
        enforce_silence=False,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("Encoder", "out", c_deg))
        b.add_component(ConsumerBoundary("PointingLoop", "in", MessageShape.single(c_rad)))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # Arch 1 (LOSE): 2-tick delayed solver violates max_delay=1
    def delayed_2tick(msg: Message, state: Dict, tick: int):
        if tick == 2:
            f = msg.first_field()
            rad = round(float(f.value) * DEG_TO_RAD, 5)
            return Message.single(Field(rad, c_rad, Dynamics("D.out", 1.0), provenance=f.provenance)), state
        return None, state

    b1 = Board("Ex14_Arch1")
    bounds(b1)
    b1.add_component(DeriveBlock("Slow2Tick", MessageShape.single(c_deg), MessageShape.single(c_rad), delayed_2tick))
    b1.connect("Encoder.out", "Slow2Tick.in")
    b1.connect("Slow2Tick.out", "PointingLoop.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "Arch 1 (LOSE): 2-tick deadline breach"))

    # Arch 2 (WIN - High IPC + Op Latency): IPC_SERIALIZED carrier + latency=0.5 per tick
    b2 = Board("Ex14_Arch2")
    bounds(b2)
    b2.add_component(
        RecolorBlock(
            "RecIPC",
            c_deg,
            c_rad,
            value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5),
            latency=0.5,
        )
    )
    b2.connect("Encoder.out", "RecIPC.in", carrier=Carrier.IPC_SERIALIZED)
    b2.connect("RecIPC.out", "PointingLoop.in", carrier=Carrier.IN_PROCESS)
    snaps.append(ev.evaluate(b2, ulsc, scenario, "Arch 2 (WIN): IPC carrier + 0.5 latency"))

    # Arch 3 (WIN - Lossy Narrowing): deg(f64) -> rad(f32) -> rad(f64) with info_loss=0.25/tick
    b3 = Board("Ex14_Arch3")
    bounds(b3)
    b3.add_component(
        RecolorBlock(
            "NarrowF32",
            c_deg,
            c_rad_f32,
            value_fn=lambda d: round(float(d) * DEG_TO_RAD, 4),
            info_loss=0.25,
        )
    )
    b3.add_component(RecolorBlock("WidenF64", c_rad_f32, c_rad, value_fn=float))
    b3.connect("Encoder.out", "NarrowF32.in")
    b3.connect("NarrowF32.out", "WidenF64.in")
    b3.connect("WidenF64.out", "PointingLoop.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "Arch 3 (WIN): Lossy f32 intermediate"))

    # Arch 4 (WIN - Redundant Identity Block): Lossless but includes an extra no-op RecolorBlock
    b4 = Board("Ex14_Arch4")
    bounds(b4)
    b4.add_component(
        RecolorBlock("RecLossless", c_deg, c_rad, value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5))
    )
    b4.add_component(RecolorBlock("NoOpPass", c_rad, c_rad, value_fn=float))
    b4.connect("Encoder.out", "RecLossless.in")
    b4.connect("RecLossless.out", "NoOpPass.in")
    b4.connect("NoOpPass.out", "PointingLoop.in")
    snaps.append(ev.evaluate(b4, ulsc, scenario, "Arch 4 (WIN): Redundant identity block"))

    # Arch 5 (WIN - Pareto Optimal): Single lossless RecolorBlock over IN_PROCESS carrier
    b5 = Board("Ex14_Arch5")
    bounds(b5)
    b5.add_component(
        RecolorBlock("RecOptimal", c_deg, c_rad, value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5))
    )
    b5.connect("Encoder.out", "RecOptimal.in", carrier=Carrier.IN_PROCESS)
    b5.connect("RecOptimal.out", "PointingLoop.in", carrier=Carrier.IN_PROCESS)
    snaps.append(ev.evaluate(b5, ulsc, scenario, "Arch 5 (WIN): Pareto-optimal minimal"))

    return snaps
