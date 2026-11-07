"""
Example 9: Mismatched Component Clocks (Slow 10Hz Star Tracker -> Fast 50Hz Controller).
Demonstrates:
  - Strictly invariant boundary interfaces across all snapshots:
      * SlowStarTracker: emits PUSH messages on ticks 0 and 3 in (Attitude.StarAngle, arcsec, float32),
        then drops out on ticks 4..6.
      * FastController: expects PUSH messages in (Attitude.StarAngle, rad, float64) with freshness age <= 2 ticks.
  - Mediation via RecolorBlock + CacheStoreBlock + PumpBlock + StaleGateBlock.
"""
from __future__ import annotations

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
    PumpBlock,
    RecolorBlock,
    ScoreBreakdown,
    StaleGateBlock,
    TransferMode,
    UniversalLSC,
)

ARCSEC_TO_RAD = 4.8481368e-6


def example_09_ticks() -> List[ScoreBreakdown]:
    c_arcsec = Color("Attitude.StarAngle", "arcsec", "float32")
    c_rad = Color("Attitude.StarAngle", "rad", "float64")
    val_arcsec = 206264.806  # ~1.0 radian
    horizon = 7

    # Slow tracker emits at t=0 and t=3, then goes silent for ticks 4..6
    scenario = {
        t: {
            "SlowTracker.out": Message.single(
                Field(val_arcsec, c_arcsec, Dynamics("SlowTracker.out", 0.33), provenance=Provenance(("Tracker",), timestamp_tick=t))
            )
        }
        for t in (0, 3)
    }

    def freshness_and_val_error(trig: Message, out: Message) -> float:
        f = out.first_field()
        val_err = abs(1.0 - float(f.value))
        return val_err

    # Pre-trigger on ticks 0, 1, 2, 3, 4, 5 where fresh data (age <= 2) exists;
    # on tick 6, age would be 6 - 3 = 3 > 2, so FastController MUST be silent at t=6!
    def expected_active_trigger(t: int, env):
        if t in (0, 1, 2, 3, 4, 5):
            return Message.single(Field(1.0, c_rad))
        return None

    ulsc = UniversalLSC(
        name="uLSC_MultiRateFreshness",
        target_need_id="FastControl.in",
        horizon=horizon,
        pre_trigger_fn=expected_active_trigger,
        value_distance_fn=freshness_and_val_error,
        tolerance=0.01,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )

    def bounds(b: Board) -> None:
        # Invariant PUSH boundaries across every snapshot!
        b.add_component(ProducerBoundary("SlowTracker", "out", c_arcsec, mode=TransferMode.PUSH, velocity=0.33))
        b.add_component(ConsumerBoundary("FastControl", "in", MessageShape.single(c_rad), mode=TransferMode.PUSH))

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    # S0: Unconnected
    b0 = Board("Ex9_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected multi-rate"))

    # S1: Recolor (arcsec -> rad) wired directly to FastControl (misses held ticks 1, 2, 4, 5)
    b1 = Board("Ex9_S1")
    bounds(b1)
    b1.add_component(
        RecolorBlock("ArcToRad", c_arcsec, c_rad, value_fn=lambda a: round(float(a) * ARCSEC_TO_RAD, 5))
    )
    b1.connect("SlowTracker.out", "ArcToRad.in")
    b1.connect("ArcToRad.out", "FastControl.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct Recolor only (rate underflow)"))

    # S2: Recolor + Zero-Order-Hold Cache + 1Hz Pump WITHOUT StaleGate (emits stale sample at t=6 -> silence breach!)
    b2 = Board("Ex9_S2")
    bounds(b2)
    b2.add_component(
        RecolorBlock("ArcToRad", c_arcsec, c_rad, value_fn=lambda a: round(float(a) * ARCSEC_TO_RAD, 5))
    )
    b2.add_component(CacheStoreBlock("ZOHCache", c_rad, retain_on_read=True))
    b2.add_component(PumpBlock("FastPump", c_rad, period=1))
    b2.connect("SlowTracker.out", "ArcToRad.in")
    b2.connect("ArcToRad.out", "ZOHCache.in")
    b2.connect("ZOHCache.out", "FastPump.in")
    b2.connect("FastPump.out", "FastControl.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Cache & Pump, no StaleGate (stale at t=6)"))

    # S3: Recolor + Cache + Pump + StaleGate(max_age=2) suppresses stale emission at t=6 (WIN)
    b3 = Board("Ex9_S3")
    bounds(b3)
    b3.add_component(
        RecolorBlock("ArcToRad", c_arcsec, c_rad, value_fn=lambda a: round(float(a) * ARCSEC_TO_RAD, 5))
    )
    b3.add_component(CacheStoreBlock("ZOHCache", c_rad, retain_on_read=True))
    b3.add_component(PumpBlock("FastPump", c_rad, period=1))
    b3.add_component(StaleGateBlock("FreshGate", c_rad, max_age=2))
    b3.connect("SlowTracker.out", "ArcToRad.in")
    b3.connect("ArcToRad.out", "ZOHCache.in")
    b3.connect("ZOHCache.out", "FastPump.in")
    b3.connect("FastPump.out", "FreshGate.in")
    b3.connect("FreshGate.out", "FastControl.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: +StaleGate(max_age=2) (WIN)"))

    return snaps
