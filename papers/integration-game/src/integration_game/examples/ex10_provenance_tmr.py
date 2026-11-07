"""
Example 10: Provenance & Assurance Voting (TMR Fault Masking + Unit Recoloring).
Demonstrates:
  - Three redundant DAL-C radar altimeters offering (Flight.Altitude, feet, float32)
    with trust_score=0.60 and assurance_level="DAL_C".
  - Single-sensor transient glitch spike injected on Alt2 at tick 2 (5000 ft vs 328.084 ft nominal).
  - Consumer AutolandSink requires (Flight.Altitude, meters, float64) with
    min_trust=0.90 and required_assurance="TMR_VOTED".
  - Single-channel bypass fails both Tier-1 provenance contract and Tier-3 glitch tolerance;
    3-channel Recolor + ProvTMRVoteBlock masks the glitch and boosts trust to 0.95 (WIN).
"""
from __future__ import annotations

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
    ProducerBoundary,
    ProvTMRVoteBlock,
    Provenance,
    RecolorBlock,
    ScoreBreakdown,
    UniversalLSC,
)

FEET_TO_M = 0.3048


def example_10_provenance() -> List[ScoreBreakdown]:
    c_alt_ft = Color("Flight.Altitude", "feet", "float32")
    c_alt_m = Color("Flight.Altitude", "meters", "float64")
    nom_ft = 100.0 / FEET_TO_M  # 328.084 ft -> 100.0 m
    horizon = 4

    scenario = {}
    for t in range(horizon):
        alt2_val = 5000.0 if t == 2 else nom_ft  # Transient glitch on Alt2 at tick 2!
        scenario[t] = {
            "Alt1.out": Message.single(
                Field(
                    nom_ft,
                    c_alt_ft,
                    Dynamics("Alt1.out", 1.0),
                    provenance=Provenance(("Alt1",), timestamp_tick=t, trust_score=0.60, assurance_level="DAL_C"),
                )
            ),
            "Alt2.out": Message.single(
                Field(
                    alt2_val,
                    c_alt_ft,
                    Dynamics("Alt2.out", 1.0),
                    provenance=Provenance(("Alt2",), timestamp_tick=t, trust_score=0.60, assurance_level="DAL_C"),
                )
            ),
            "Alt3.out": Message.single(
                Field(
                    nom_ft,
                    c_alt_ft,
                    Dynamics("Alt3.out", 1.0),
                    provenance=Provenance(("Alt3",), timestamp_tick=t, trust_score=0.60, assurance_level="DAL_C"),
                )
            ),
        }

    ulsc = UniversalLSC(
        name="uLSC_AutolandTMR",
        target_need_id="AutolandSink.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Alt1.out"),
        value_distance_fn=lambda trig, out: abs(100.0 - float(out.first_field().value)),
        tolerance=0.1,
        max_delay=1,
        enforce_silence=True,
    )

    need_shape = MessageShape.single(c_alt_m, min_trust=0.90, required_assurance="TMR_VOTED")

    def bounds(b: Board) -> None:
        for cid in ("Alt1", "Alt2", "Alt3"):
            b.add_component(
                ProducerBoundary(
                    cid,
                    "out",
                    c_alt_ft,
                    shape=MessageShape.single(c_alt_ft, min_trust=0.60, required_assurance="DAL_C"),
                    trust_score=0.60,
                    assurance_level="DAL_C",
                )
            )
        b.add_component(ConsumerBoundary("AutolandSink", "in", need_shape))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex10_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected redundant altimeters"))

    # S1: Single-channel recolor from Alt2 (fails Tier-1 provenance contract AND Tier-3 glitch at t=2)
    b1 = Board("Ex10_S1")
    bounds(b1)
    b1.add_component(
        RecolorBlock("Rec2", c_alt_ft, c_alt_m, value_fn=lambda ft: round(float(ft) * FEET_TO_M, 3))
    )
    b1.connect("Alt2.out", "Rec2.in")
    b1.connect("Rec2.out", "AutolandSink.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Single-sensor bypass (prov+glitch fail)"))

    # S2: 3-channel Recolor + ProvTMRVoteBlock masks Alt2 glitch at t=2 and satisfies TMR_VOTED (WIN)
    b2 = Board("Ex10_S2")
    bounds(b2)
    for i, cid in enumerate(("Alt1", "Alt2", "Alt3")):
        rc_id = f"Rec_{i}"
        b2.add_component(
            RecolorBlock(rc_id, c_alt_ft, c_alt_m, value_fn=lambda ft: round(float(ft) * FEET_TO_M, 3))
        )
        b2.connect(f"{cid}.out", f"{rc_id}.in")
    b2.add_component(ProvTMRVoteBlock("TMRVoter", c_alt_m, vote_tolerance=0.05))
    b2.connect("Rec_0.out", "TMRVoter.in_0")
    b2.connect("Rec_1.out", "TMRVoter.in_1")
    b2.connect("Rec_2.out", "TMRVoter.in_2")
    b2.connect("TMRVoter.out", "AutolandSink.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: 3x Recolor + TMR Voter (WIN)"))

    return snaps
