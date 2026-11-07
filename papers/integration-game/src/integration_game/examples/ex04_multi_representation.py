"""
Example 4: Multi-Representation Tactical Data Link Gateway.
Exercises:
  - Producer 1 (Legacy 1553 Bus): offers TrueAirspeed in (Knots, FixedPoint_Q12.4)
    packaged as MIL_STD_1553 word representation.
  - Producer 2 (Weather Service): offers WindSpeed in (Knots, float32)
    with multi-representation capability (XML_UTF8, BYTE_BLOB_JSON).
  - Consumer (Modern Mission Display): has two Needs (`tas_in` and `wind_in`),
    each accepting multiple modern binary representations {BYTE_BLOB_PROTO, CDR_DDS}
    in `float32`.
  - Requires two-stage transcode + platform widening on Stream 1
    (1553 -> NATIVE_STRUCT -> float32 -> CDR_DDS) and JSON -> PROTOBUF on Stream 2,
    monitored simultaneously by a CompositeLSC.
"""
from __future__ import annotations

import json
from typing import List

from integration_game import (
    Board,
    BoardEvaluator,
    Color,
    CompositeLSC,
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
    UniversalLSC,
)


def example_04_multi_rep() -> List[ScoreBreakdown]:
    c_tas_q = Color("Airframe.TrueAirspeed", "Knots", "FixedPoint_Q12.4")
    c_tas_f32 = Color("Airframe.TrueAirspeed", "Knots", "float32")
    c_wind = Color("Atmosphere.WindSpeed", "Knots", "float32")

    modern_reps = (Representation.BYTE_BLOB_PROTO, Representation.CDR_DDS)
    horizon = 4

    # Q12.4 fixed-point encoding: integer raw = int(round(knots * 16))
    scenario = {
        t: {
            "Bus1553.out": Message.single(
                Field(
                    int((250.0 + 5.0 * t) * 16),
                    c_tas_q,
                    Dynamics("Bus1553.out", 1.0),
                    representation=Representation.MIL_STD_1553,
                    provenance=Provenance(("Bus1553",), timestamp_tick=t),
                )
            ),
            "WeatherWeb.out": Message.single(
                Field(
                    json.dumps({"wind_kts": 35.0 + t}),
                    c_wind,
                    Dynamics("WeatherWeb.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("WeatherWeb",), timestamp_tick=t),
                )
            ),
        }
        for t in range(0, horizon, 2)
    }

    ulsc_tas = UniversalLSC(
        name="uLSC_TAS_Rep",
        target_need_id="DisplayTAS.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Bus1553.out"),
        value_distance_fn=lambda trig, out: abs(
            (float(trig.first_field().value) / 16.0) - float(out.first_field().value)
        ),
        tolerance=0.05,
        max_delay=1,
        enforce_silence=True,
    )
    ulsc_wind = UniversalLSC(
        name="uLSC_Wind_Rep",
        target_need_id="DisplayWind.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("WeatherWeb.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["wind_kts"]) - float(out.first_field().value)
        ),
        tolerance=0.05,
        max_delay=1,
        enforce_silence=True,
    )
    comp_lsc = CompositeLSC("uLSC_MultiRepGateway", [ulsc_tas, ulsc_wind])

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary(
                "Bus1553",
                "out",
                c_tas_q,
                rep=Representation.MIL_STD_1553,
            )
        )
        b.add_component(
            ProducerBoundary(
                "WeatherWeb",
                "out",
                c_wind,
                rep=Representation.BYTE_BLOB_JSON,
                reps=(Representation.XML_UTF8, Representation.BYTE_BLOB_JSON),
            )
        )
        b.add_component(
            ConsumerBoundary("DisplayTAS", "in", MessageShape.single(c_tas_f32, reps=modern_reps))
        )
        b.add_component(
            ConsumerBoundary("DisplayWind", "in", MessageShape.single(c_wind, reps=modern_reps))
        )

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex4_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, comp_lsc, scenario, "S0: Unconnected dual-stream"))

    # S1: Stream 2 mediated (JSON -> BYTE_BLOB_PROTO) and wired to DisplayWind
    b1 = Board("Ex4_S1")
    bounds(b1)
    b1.add_component(
        RepresentationBridgeBlock(
            "JSON2Proto",
            c_wind,
            Representation.BYTE_BLOB_JSON,
            Representation.BYTE_BLOB_PROTO,
            in_reps=(Representation.XML_UTF8, Representation.BYTE_BLOB_JSON),
            decode_fn=lambda s: float(json.loads(s)["wind_kts"]),
        )
    )
    b1.connect("WeatherWeb.out", "JSON2Proto.in")
    b1.connect("JSON2Proto.out", "DisplayWind.in")
    snaps.append(ev.evaluate(b1, comp_lsc, scenario, "S1: Wind JSON->Protobuf wired (50% cut)"))

    # S2: Stream 1 unpacked (1553 -> NATIVE_STRUCT) and widened (Q12.4 -> float32), but still NATIVE_STRUCT
    b2 = b1.clone("Ex4_S2")
    b2.add_component(
        RepresentationBridgeBlock(
            "Unpack1553",
            c_tas_q,
            Representation.MIL_STD_1553,
            Representation.NATIVE_STRUCT,
            decode_fn=int,
        )
    )
    b2.add_component(
        RecolorBlock(
            "WidenQ12_4",
            c_tas_q,
            c_tas_f32,
            value_fn=lambda raw: float(raw) / 16.0,
        )
    )
    b2.connect("Bus1553.out", "Unpack1553.in")
    b2.connect("Unpack1553.out", "WidenQ12_4.in")
    snaps.append(ev.evaluate(b2, comp_lsc, scenario, "S2: +1553 unpack & Q12.4->f32 (rep gap)"))

    # S3: Append NATIVE_STRUCT -> CDR_DDS serializer on Stream 1 and wire to DisplayTAS (WIN)
    b3 = b2.clone("Ex4_S3")
    b3.add_component(
        RepresentationBridgeBlock(
            "Nat2CDR",
            c_tas_f32,
            Representation.NATIVE_STRUCT,
            Representation.CDR_DDS,
            decode_fn=float,
        )
    )
    b3.connect("WidenQ12_4.out", "Nat2CDR.in")
    b3.connect("Nat2CDR.out", "DisplayTAS.in")
    snaps.append(ev.evaluate(b3, comp_lsc, scenario, "S3: +CDR_DDS encode & wire (WIN)"))

    return snaps


example_04_multi_representation = example_04_multi_rep
example_04_rest_db = example_04_multi_rep

