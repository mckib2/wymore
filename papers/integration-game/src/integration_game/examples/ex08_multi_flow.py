"""
Example 8: Multi-Producer / Multi-Consumer Fan-Out & Composite Assembly.
Demonstrates:
  - Dual producers: GPS (Nav.Pos, deg, float32, PUSH) and INS (Nav.Att, deg, float32, PUSH)
  - Dual consumers with distinct transfer modes and aggregation shapes:
      1. FlightLogger: expects Nav.Pos in radians (float64) via PULL
      2. GimbalStabilizer: expects a 2-slot RECORD {pos: Nav.Pos(rad), att: Nav.Att(rad)} via PUSH
  - Verified simultaneously across both consumers via CompositeLSC.
"""
from __future__ import annotations

import math
from typing import List

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    CacheStoreBlock,
    Color,
    CompositeLSC,
    ConsumerBoundary,
    Dynamics,
    FanOutBlock,
    Field,
    Message,
    MessageShape,
    ProducerBoundary,
    Provenance,
    RecolorBlock,
    ScoreBreakdown,
    TransferMode,
    UniversalLSC,
)

DEG_TO_RAD = math.pi / 180.0


def example_08_fanout() -> List[ScoreBreakdown]:
    c_pos_deg = Color("Nav.Pos", "deg", "float32")
    c_att_deg = Color("Nav.Att", "deg", "float32")
    c_pos_rad = Color("Nav.Pos", "rad", "float64")
    c_att_rad = Color("Nav.Att", "rad", "float64")

    gimbal_slots = {"pos": c_pos_rad, "att": c_att_rad}
    horizon = 4

    scenario = {
        t: {
            "GPS.out": Message.single(
                Field(100.0, c_pos_deg, Dynamics("GPS.out", 1.0), provenance=Provenance(("GPS",), timestamp_tick=t))
            ),
            "INS.out": Message.single(
                Field(20.0, c_att_deg, Dynamics("INS.out", 1.0), provenance=Provenance(("INS",), timestamp_tick=t))
            ),
        }
        for t in (0, 2)
    }

    ulsc_logger = UniversalLSC(
        name="uLSC_FlightLogger",
        target_need_id="FlightLogger.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("GPS.out"),
        value_distance_fn=lambda trig, out: abs(
            float(trig.first_field().value) * DEG_TO_RAD - float(out.first_field().value)
        ),
        tolerance=0.01,
        max_delay=1,
    )
    ulsc_gimbal = UniversalLSC(
        name="uLSC_GimbalStabilizer",
        target_need_id="GimbalStabilizer.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("INS.out"),
        value_distance_fn=lambda trig, out: (
            abs(100.0 * DEG_TO_RAD - float(out.fields["pos"].value))
            + abs(float(trig.first_field().value) * DEG_TO_RAD - float(out.fields["att"].value))
        ),
        tolerance=0.01,
        max_delay=1,
        enforce_silence=True,
    )
    comp_lsc = CompositeLSC("uLSC_DualConsumer", [ulsc_logger, ulsc_gimbal])

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("GPS", "out", c_pos_deg))
        b.add_component(ProducerBoundary("INS", "out", c_att_deg))
        b.add_component(
            ConsumerBoundary(
                "FlightLogger",
                "in",
                MessageShape.single(c_pos_rad),
                mode=TransferMode.PULL,
                pull_schedule=lambda t: t in (0, 2),
            )
        )
        b.add_component(
            ConsumerBoundary("GimbalStabilizer", "in", MessageShape(slots=gimbal_slots), mode=TransferMode.PUSH)
        )

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex8_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, comp_lsc, scenario, "S0: Unconnected dual topology"))

    # S1: Recolor GPS & INS to radians + FanOut GPS + Cache into FlightLogger (Gimbal still unwired)
    b1 = Board("Ex8_S1")
    bounds(b1)
    b1.add_component(
        RecolorBlock("GPS_Rad", c_pos_deg, c_pos_rad, value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5))
    )
    b1.add_component(
        RecolorBlock("INS_Rad", c_att_deg, c_att_rad, value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5))
    )
    b1.add_component(FanOutBlock("SplitGPS", c_pos_rad, n_outputs=2))
    b1.add_component(CacheStoreBlock("LogCache", c_pos_rad, retain_on_read=False))
    b1.connect("GPS.out", "GPS_Rad.in")
    b1.connect("INS.out", "INS_Rad.in")
    b1.connect("GPS_Rad.out", "SplitGPS.in")
    b1.connect("SplitGPS.out_0", "LogCache.in")
    b1.connect("LogCache.out", "FlightLogger.in")
    snaps.append(ev.evaluate(b1, comp_lsc, scenario, "S1: Logger branch wired (50% cut)"))

    # S2: Assemble GPS branch 1 + INS into GimbalStabilizer (WIN)
    b2 = b1.clone("Ex8_S2")
    b2.add_component(AssembleBlock("AsmGimbal", gimbal_slots))
    b2.connect("SplitGPS.out_1", "AsmGimbal.in_pos")
    b2.connect("INS_Rad.out", "AsmGimbal.in_att")
    b2.connect("AsmGimbal.out", "GimbalStabilizer.in")
    snaps.append(ev.evaluate(b2, comp_lsc, scenario, "S2: +Assemble Gimbal branch (WIN)"))

    return snaps
