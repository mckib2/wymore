"""
Example 2: Ping / Pong Transponder Handshake.
Exercises:
  - Representation mediation (BYTE_BLOB_JSON -> NATIVE_STRUCT)
  - Conceptual & Platform Recoloring (Net.Ping uint16 -> Net.Pong uint32)
  - Kinematic Push -> Pull deceleration (CacheStoreBlock)
  - Tier-3 Silence Breach trap: retain_on_read=True causes repeated duplicate Pongs
    during quiet ticks, whereas retain_on_read=False (consume-on-read FIFO) wins.
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


def example_02_ping_pong() -> List[ScoreBreakdown]:
    c_ping = Color(C="Net.Ping", L="SeqNum", P="uint16")
    c_pong_u16 = Color(C="Net.Pong", L="SeqNum", P="uint16")
    c_pong = Color(C="Net.Pong", L="SeqNum", P="uint32")
    horizon = 8
    scenario = {
        1: {
            "PingGen.out": Message.single(
                Field(
                    json.dumps({"seq": 101}),
                    c_ping,
                    Dynamics("PingGen.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("PingGen",), timestamp_tick=1),
                )
            )
        },
        5: {
            "PingGen.out": Message.single(
                Field(
                    json.dumps({"seq": 202}),
                    c_ping,
                    Dynamics("PingGen.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("PingGen",), timestamp_tick=5),
                )
            )
        },
    }
    ulsc = UniversalLSC(
        name="uLSC_PingPong",
        target_need_id="PongSink.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("PingGen.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["seq"]) - float(out.first_field().value)
        ),
        tolerance=0.0,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )
    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary(
                "PingGen",
                "out",
                c_ping,
                mode=TransferMode.PUSH,
                rep=Representation.BYTE_BLOB_JSON,
            )
        )
        b.add_component(
            ConsumerBoundary(
                "PongSink",
                "in",
                MessageShape.single(c_pong, reps=(Representation.NATIVE_STRUCT,)),
                mode=TransferMode.PULL,
                pull_schedule=lambda t: True,
            )
        )

    # S0: Unconnected
    b0 = Board("Ex2_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    # S1: Direct wire (rep + color + mode clashes)
    b1 = Board("Ex2_S1")
    bounds(b1)
    b1.connect("PingGen.out", "PongSink.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct wire (rep+color+mode)"))

    # S2: +Transcode JSON->Native + Recolor C & P (Tier 1 satisfied, Tier 2 mode clash remains)
    def add_tier1_chain(b: Board) -> None:
        b.add_component(
            RepresentationBridgeBlock(
                "JSON2Nat",
                c_ping,
                Representation.BYTE_BLOB_JSON,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: int(json.loads(s)["seq"]),
            )
        )
        b.add_component(RecolorBlock("Recolor_C", c_ping, c_pong_u16, value_fn=int))
        b.add_component(RecolorBlock("Recolor_P", c_pong_u16, c_pong, value_fn=int))
        b.connect("PingGen.out", "JSON2Nat.in")
        b.connect("JSON2Nat.out", "Recolor_C.in")
        b.connect("Recolor_C.out", "Recolor_P.in")

    b2 = Board("Ex2_S2")
    bounds(b2)
    add_tier1_chain(b2)
    b2.connect("Recolor_P.out", "PongSink.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Transcode & Recolor (mode clash)"))

    # S3: +LVC retain-on-read (Tier 1 & Tier 2 satisfied, but triggers Hot Silence Breach!)
    b3 = Board("Ex2_S3")
    bounds(b3)
    add_tier1_chain(b3)
    b3.add_component(CacheStoreBlock("LVC", c_pong, retain_on_read=True))
    b3.connect("Recolor_P.out", "LVC.in")
    b3.connect("LVC.out", "PongSink.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: +LVC retain (silence breach)"))

    # S4: +Consume-on-read FIFO queue (Tier 1, 2, 3 all satisfied -> WIN)
    b4 = Board("Ex2_S4")
    bounds(b4)
    add_tier1_chain(b4)
    b4.add_component(CacheStoreBlock("Queue", c_pong, retain_on_read=False))
    b4.connect("Recolor_P.out", "Queue.in")
    b4.connect("Queue.out", "PongSink.in")
    snaps.append(ev.evaluate(b4, ulsc, scenario, "S4: +Consume queue (WIN)"))

    return snaps
