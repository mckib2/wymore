"""
Example 12: Dynamic Runtime Failover Multiplexer (MuxSwitchBlock with Online Policy).
Demonstrates:
  - Primary link offers (Nav.Airspeed, m_per_s, float64) in NATIVE_STRUCT on ticks 0..1,
    then suffers total link dropout on ticks 2..3.
  - Backup satellite link offers (Nav.Airspeed, knots, float32) in BYTE_BLOB_JSON on ticks 0..3.
  - Backup link requires RepresentationBridgeBlock (JSON -> NATIVE_STRUCT) + RecolorBlock (knots -> m/s).
  - Static MuxSwitchBlock (locked on index 0) fails when Primary drops out at t=2;
    dynamic `policy_fn` automatically switches to Backup (in_1) whenever Primary (in_0) is silent (WIN).
"""
from __future__ import annotations

import json
from typing import List

from integration_game import (
    Board,
    BoardEvaluator,
    Color,
    ConsumerBoundary,
    Dynamics,
    Field,
    Message,
    MessageShape,
    MuxSwitchBlock,
    ProducerBoundary,
    Provenance,
    RecolorBlock,
    Representation,
    RepresentationBridgeBlock,
    ScoreBreakdown,
    UniversalLSC,
)

KNOTS_TO_MPS = 0.51444444


def example_12_failover() -> List[ScoreBreakdown]:
    c_mps = Color("Nav.Airspeed", "m_per_s", "float64")
    c_kt = Color("Nav.Airspeed", "knots", "float32")
    val_mps = 50.0
    val_kt_json = json.dumps({"v_kt": round(val_mps / KNOTS_TO_MPS, 4)})
    horizon = 4

    scenario = {}
    for t in range(horizon):
        tick_env = {
            "BackupAir.out": Message.single(
                Field(
                    val_kt_json,
                    c_kt,
                    Dynamics("BackupAir.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("BackupAir",), timestamp_tick=t),
                )
            )
        }
        if t < 2:
            # Primary only alive on ticks 0 and 1!
            tick_env["PrimaryAir.out"] = Message.single(
                Field(
                    val_mps,
                    c_mps,
                    Dynamics("PrimaryAir.out", 1.0),
                    representation=Representation.NATIVE_STRUCT,
                    provenance=Provenance(("PrimaryAir",), timestamp_tick=t),
                )
            )
        scenario[t] = tick_env

    ulsc = UniversalLSC(
        name="uLSC_ContinuousAirspeed",
        target_need_id="FlightDirector.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("BackupAir.out"),
        value_distance_fn=lambda trig, out: abs(val_mps - float(out.first_field().value)),
        tolerance=0.1,
        max_delay=0,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("PrimaryAir", "out", c_mps, rep=Representation.NATIVE_STRUCT))
        b.add_component(ProducerBoundary("BackupAir", "out", c_kt, rep=Representation.BYTE_BLOB_JSON))
        b.add_component(ConsumerBoundary("FlightDirector", "in", MessageShape.single(c_mps)))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex12_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected primary/backup links"))

    # S1: Primary wired directly (fails on ticks 2 and 3 when Primary drops out)
    b1 = Board("Ex12_S1")
    bounds(b1)
    b1.connect("PrimaryAir.out", "FlightDirector.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Primary only (dropout breach at t=2,3)"))

    # S2: Backup conditioned (JSON->Native + knots->m/s) + Static Mux locked to index 0
    b2 = Board("Ex12_S2")
    bounds(b2)
    b2.add_component(
        RepresentationBridgeBlock(
            "JSONDecode",
            c_kt,
            Representation.BYTE_BLOB_JSON,
            Representation.NATIVE_STRUCT,
            decode_fn=lambda s: float(json.loads(s)["v_kt"]),
        )
    )
    b2.add_component(
        RecolorBlock("KtToMPS", c_kt, c_mps, value_fn=lambda kt: round(float(kt) * KNOTS_TO_MPS, 3))
    )
    b2.add_component(MuxSwitchBlock("StaticMux", c_mps, n_inputs=2, active_index=0))
    b2.connect("BackupAir.out", "JSONDecode.in")
    b2.connect("JSONDecode.out", "KtToMPS.in")
    b2.connect("PrimaryAir.out", "StaticMux.in_0")
    b2.connect("KtToMPS.out", "StaticMux.in_1")
    b2.connect("StaticMux.out", "FlightDirector.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Backup path & static Mux (idx=0)"))

    # S3: Dynamic Failover Policy switches to Backup (in_1) whenever Primary (in_0) is None (WIN)
    b3 = Board("Ex12_S3")
    bounds(b3)
    b3.add_component(
        RepresentationBridgeBlock(
            "JSONDecode",
            c_kt,
            Representation.BYTE_BLOB_JSON,
            Representation.NATIVE_STRUCT,
            decode_fn=lambda s: float(json.loads(s)["v_kt"]),
        )
    )
    b3.add_component(
        RecolorBlock("KtToMPS", c_kt, c_mps, value_fn=lambda kt: round(float(kt) * KNOTS_TO_MPS, 3))
    )
    b3.add_component(
        MuxSwitchBlock(
            "AutoFailoverMux",
            c_mps,
            n_inputs=2,
            active_index=0,
            policy_fn=lambda tick, inboxes, st: 0 if inboxes.get(0) is not None else 1,
        )
    )
    b3.connect("BackupAir.out", "JSONDecode.in")
    b3.connect("JSONDecode.out", "KtToMPS.in")
    b3.connect("PrimaryAir.out", "AutoFailoverMux.in_0")
    b3.connect("KtToMPS.out", "AutoFailoverMux.in_1")
    b3.connect("AutoFailoverMux.out", "FlightDirector.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Dynamic failover policy Mux (WIN)"))

    return snaps
