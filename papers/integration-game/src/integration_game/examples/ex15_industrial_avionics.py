"""
Example 15: Industrial-flavored FACE/SOSA-style multi-bus holdout.
MIL-STD-1553 aircraft status (JSON-wrapped on a legacy bus) must feed a
DDS/native guidance consumer needing airspeed in knots as float64.
Used as external-validity holdout for offline synthesis agents.
"""
from __future__ import annotations

import json
from typing import List

from integration_game import (
    Board,
    BoardEvaluator,
    CacheStoreBlock,
    Color,
    ConsumerBoundary,
    Dynamics,
    Field,
    Message,
    MessageShape,
    ProducerBoundary,
    Provenance,
    RecolorBlock,
    Representation,
    RepresentationBridgeBlock,
    ScoreBreakdown,
    TransferMode,
    UniversalLSC,
)


def example_15_industrial_avionics() -> List[ScoreBreakdown]:
    c_bus = Color("Aircraft.Status.IAS", "m_per_s", "float32")
    c_dds_ms = Color("Guidance.Airspeed", "m_per_s", "float32")
    c_dds_kt = Color("Guidance.Airspeed", "knots", "float32")
    c_dds_kt64 = Color("Guidance.Airspeed", "knots", "float64")

    horizon = 6
    samples = {0: 100.0, 2: 110.0, 4: 120.0}  # m/s
    scenario = {
        t: {
            "Bus1553.out": Message.single(
                Field(
                    json.dumps({"ias_mps": v}),
                    c_bus,
                    Dynamics("Bus1553.out", 1.0),
                    representation=Representation.MIL_STD_1553,
                    provenance=Provenance(("Bus1553",), timestamp_tick=t, trust_score=0.85),
                )
            )
        }
        for t, v in samples.items()
    }

    def err(trig: Message, out: Message) -> float:
        mps = float(json.loads(trig.first_field().value)["ias_mps"])
        expected_kt = mps * 1.94384
        return abs(expected_kt - float(out.first_field().value))

    ulsc = UniversalLSC(
        name="uLSC_IndustrialIAS",
        target_need_id="Guidance.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Bus1553.out"),
        value_distance_fn=err,
        tolerance=0.5,
        max_delay=1,
        enforce_silence=True,
    )
    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary(
                "Bus1553",
                "out",
                c_bus,
                rep=Representation.MIL_STD_1553,
            )
        )
        b.add_component(
            ConsumerBoundary(
                "Guidance",
                "in",
                MessageShape.single(c_dds_kt64, reps=(Representation.NATIVE_STRUCT,)),
                mode=TransferMode.PULL,
                pull_schedule=lambda t: True,
            )
        )

    b0 = Board("Ex15_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected avionics stub"))

    b1 = Board("Ex15_S1")
    bounds(b1)
    b1.connect("Bus1553.out", "Guidance.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct wire (rep+color+mode)"))

    def chain(b: Board) -> None:
        b.add_component(
            RepresentationBridgeBlock(
                "1553_Decode",
                c_bus,
                Representation.MIL_STD_1553,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: float(json.loads(s)["ias_mps"]),
            )
        )
        b.add_component(RecolorBlock("Recolor_C", c_bus, c_dds_ms, value_fn=float))
        b.add_component(
            RecolorBlock("Recolor_L", c_dds_ms, c_dds_kt, value_fn=lambda x: round(x * 1.94384, 4))
        )
        b.add_component(RecolorBlock("Recolor_P", c_dds_kt, c_dds_kt64, value_fn=float))
        b.connect("Bus1553.out", "1553_Decode.in")
        b.connect("1553_Decode.out", "Recolor_C.in")
        b.connect("Recolor_C.out", "Recolor_L.in")
        b.connect("Recolor_L.out", "Recolor_P.in")

    b2 = Board("Ex15_S2")
    bounds(b2)
    chain(b2)
    b2.connect("Recolor_P.out", "Guidance.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Recolor chain (mode clash)"))

    b3 = Board("Ex15_S3")
    bounds(b3)
    chain(b3)
    b3.add_component(CacheStoreBlock("Latch", c_dds_kt64, retain_on_read=False))
    b3.connect("Recolor_P.out", "Latch.in")
    b3.connect("Latch.out", "Guidance.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: +Consume latch (WIN)"))
    return snaps
