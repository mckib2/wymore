"""
Example 11: Asynchronous Temporal-Window Join (Keyed EO/SAR Sensor Fusion).
Demonstrates:
  - Asynchronous keyed RECORD streams:
      * EO_Camera: emits {track_id, bearing} with bearing in (EO.Bearing, deg, float32)
      * SAR_Radar: emits {track_id, range} with range in (SAR.Range, km, float32)
  - Consumer TrackCorrelator expects {track_id, bearing(rad, float64), range(meters, float64)}
    joined on `track_id` within a 1-tick skew window (`window=1`).
  - Distractor tracks (T888, T999) and 1-tick skew between EO(T101 at t=1) and SAR(T101 at t=2).
"""
from __future__ import annotations

import math
from typing import Dict, List

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    Color,
    ConsumerBoundary,
    DisassembleBlock,
    Dynamics,
    Field,
    JoinBlock,
    Message,
    MessageShape,
    ProducerBoundary,
    Provenance,
    RecolorBlock,
    ScoreBreakdown,
    UniversalLSC,
)

DEG_TO_RAD = math.pi / 180.0


def example_11_temporal_join() -> List[ScoreBreakdown]:
    c_id = Color("Track.ID", "UUID", "string")
    c_eo_deg = Color("EO.Bearing", "deg", "float32")
    c_eo_rad = Color("EO.Bearing", "rad", "float64")
    c_sar_km = Color("SAR.Range", "km", "float32")
    c_sar_m = Color("SAR.Range", "meters", "float64")

    eo_raw_slots = {"track_id": c_id, "bearing": c_eo_deg}
    sar_raw_slots = {"track_id": c_id, "range": c_sar_km}
    eo_ned_slots = {"track_id": c_id, "bearing": c_eo_rad}
    sar_ned_slots = {"track_id": c_id, "range": c_sar_m}
    fused_slots = {"track_id": c_id, "bearing": c_eo_rad, "range": c_sar_m}

    horizon = 6
    # t=0: SAR distractor T888
    # t=1: EO target T101 (bearing = 10 deg -> 0.17453 rad)
    # t=2: SAR target T101 (range = 5.0 km -> 5000.0 m) -> within 1-tick window of EO T101!
    # t=4: EO distractor T999
    scenario: Dict[int, Dict[str, Message]] = {
        0: {
            "SAR.out": Message.record(
                {
                    "track_id": Field("T888", c_id, Dynamics("SAR.out", 1.0), provenance=Provenance(("SAR",), timestamp_tick=0)),
                    "range": Field(12.0, c_sar_km, Dynamics("SAR.out", 1.0), provenance=Provenance(("SAR",), timestamp_tick=0)),
                },
                key="T888",
            )
        },
        1: {
            "EO.out": Message.record(
                {
                    "track_id": Field("T101", c_id, Dynamics("EO.out", 1.0), provenance=Provenance(("EO",), timestamp_tick=1)),
                    "bearing": Field(10.0, c_eo_deg, Dynamics("EO.out", 1.0), provenance=Provenance(("EO",), timestamp_tick=1)),
                },
                key="T101",
            )
        },
        2: {
            "SAR.out": Message.record(
                {
                    "track_id": Field("T101", c_id, Dynamics("SAR.out", 1.0), provenance=Provenance(("SAR",), timestamp_tick=2)),
                    "range": Field(5.0, c_sar_km, Dynamics("SAR.out", 1.0), provenance=Provenance(("SAR",), timestamp_tick=2)),
                },
                key="T101",
            )
        },
        4: {
            "EO.out": Message.record(
                {
                    "track_id": Field("T999", c_id, Dynamics("EO.out", 1.0), provenance=Provenance(("EO",), timestamp_tick=4)),
                    "bearing": Field(45.0, c_eo_deg, Dynamics("EO.out", 1.0), provenance=Provenance(("EO",), timestamp_tick=4)),
                },
                key="T999",
            )
        },
    }

    def join_error(trig: Message, out: Message) -> float:
        tid = str(out.fields["track_id"].value)
        id_err = 0.0 if tid == "T101" else 100.0
        b_err = abs(10.0 * DEG_TO_RAD - float(out.fields["bearing"].value))
        r_err = abs(5000.0 - float(out.fields["range"].value))
        return id_err + b_err + r_err

    ulsc = UniversalLSC(
        name="uLSC_TemporalJoin",
        target_need_id="TrackCorrelator.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("SAR.out") if t == 2 else None,
        value_distance_fn=join_error,
        tolerance=0.5,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("EO", "out", c_id, shape=MessageShape(slots=eo_raw_slots)))
        b.add_component(ProducerBoundary("SAR", "out", c_id, shape=MessageShape(slots=sar_raw_slots)))
        b.add_component(ConsumerBoundary("TrackCorrelator", "in", MessageShape(slots=fused_slots)))

    def add_conditioning(b: Board) -> None:
        b.add_component(DisassembleBlock("SplitEO", eo_raw_slots, normalize_output_slot=True))
        b.add_component(
            RecolorBlock("RecEO", c_eo_deg, c_eo_rad, value_fn=lambda d: round(float(d) * DEG_TO_RAD, 5))
        )
        b.add_component(AssembleBlock("AsmEO", eo_ned_slots))
        b.connect("EO.out", "SplitEO.in")
        b.connect("SplitEO.out_track_id", "AsmEO.in_track_id")
        b.connect("SplitEO.out_bearing", "RecEO.in")
        b.connect("RecEO.out", "AsmEO.in_bearing")

        b.add_component(DisassembleBlock("SplitSAR", sar_raw_slots, normalize_output_slot=True))
        b.add_component(
            RecolorBlock("RecSAR", c_sar_km, c_sar_m, value_fn=lambda k: round(float(k) * 1000.0, 2))
        )
        b.add_component(AssembleBlock("AsmSAR", sar_ned_slots))
        b.connect("SAR.out", "SplitSAR.in")
        b.connect("SplitSAR.out_track_id", "AsmSAR.in_track_id")
        b.connect("SplitSAR.out_range", "RecSAR.in")
        b.connect("RecSAR.out", "AsmSAR.in_range")

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex11_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected EO/SAR streams"))

    # S1: Condition EO & SAR into target units, but Join window=0 (misses 1-tick skew between t=1 and t=2!)
    b1 = Board("Ex11_S1")
    bounds(b1)
    add_conditioning(b1)
    b1.add_component(
        JoinBlock("StrictJoin0", eo_ned_slots, sar_ned_slots, "track_id", "track_id", window=0)
    )
    b1.connect("AsmEO.out", "StrictJoin0.in_left")
    b1.connect("AsmSAR.out", "StrictJoin0.in_right")
    b1.connect("StrictJoin0.out", "TrackCorrelator.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Conditioned + Join(window=0) (skew miss)"))

    # S2: Condition EO & SAR + JoinBlock(window=1) correlates T101 across t=1..2 and rejects T888/T999 (WIN)
    b2 = Board("Ex11_S2")
    bounds(b2)
    add_conditioning(b2)
    b2.add_component(
        JoinBlock("WinJoin1", eo_ned_slots, sar_ned_slots, "track_id", "track_id", window=1)
    )
    b2.connect("AsmEO.out", "WinJoin1.in_left")
    b2.connect("AsmSAR.out", "WinJoin1.in_right")
    b2.connect("WinJoin1.out", "TrackCorrelator.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Conditioned + Join(window=1) (WIN)"))

    return snaps
