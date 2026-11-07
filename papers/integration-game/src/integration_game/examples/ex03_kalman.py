"""
Example 3: Kalman Filter Kinematic State & Covariance Estimator.
Producer offers noisy raw radar position in (Track.RawPos, cm, int32).
Consumer requires a 6-slot RECORD of estimated position, velocity, acceleration,
and their error variances in SI units (m, m/s, m/s^2, m^2, m^2/s^2, m^2/s^4, float64).
Demonstrates:
  - Input pre-conditioning (Recolor_P int32->float64, Recolor_L cm->m)
  - Tier-3 trap 1: Naive finite-difference derivative amplifies sensor noise
  - Tier-3 trap 2: Uncalibrated Kalman gain converges too slowly
  - Winning play: Calibrated alpha-beta-gamma / Kalman estimator
"""
from __future__ import annotations

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


def example_03_kalman() -> List[ScoreBreakdown]:
    c_raw_cm = Color("Track.RawPos", "cm", "int32")
    c_raw_cm64 = Color("Track.RawPos", "cm", "float64")
    c_raw_m = Color("Track.RawPos", "meters", "float64")

    c_pos = Color("Track.EstPos", "meters", "float64")
    c_vel = Color("Track.EstVel", "m_per_s", "float64")
    c_acc = Color("Track.EstAcc", "m_per_s2", "float64")
    c_cov_p = Color("Track.CovPos", "m2", "float64")
    c_cov_v = Color("Track.CovVel", "m2_per_s2", "float64")
    c_cov_a = Color("Track.CovAcc", "m2_per_s4", "float64")

    guidance_shape = MessageShape(
        slots={
            "pos_est": c_pos,
            "vel_est": c_vel,
            "acc_est": c_acc,
            "cov_pos": c_cov_p,
            "cov_vel": c_cov_v,
            "cov_acc": c_cov_a,
        }
    )

    horizon = 6
    # True trajectory: v = 10 m/s, a = 0 m/s^2; noisy measurements in centimeters (int32)
    noisy_cm = [0, 1120, 1890, 3080, 3940, 5030]
    scenario = {
        t: {
            "Radar.out": Message.single(
                Field(
                    noisy_cm[t],
                    c_raw_cm,
                    Dynamics("Radar.out", 1.0),
                    provenance=Provenance(("Radar",), timestamp_tick=t),
                )
            )
        }
        for t in range(horizon)
    }

    def tracking_error(trig: Message, out: Message) -> float:
        t_tick = trig.first_field().provenance.timestamp_tick
        if t_tick < 2:
            return 0.0
        vel_err = abs(float(out.fields["vel_est"].value) - 10.0)
        acc_err = abs(float(out.fields["acc_est"].value) - 0.0)
        cov_p = float(out.fields["cov_pos"].value)
        # Require accurate velocity/acceleration AND bounded covariance trace <= 1.0
        cov_pen = max(0.0, cov_p - 1.0)
        return max(vel_err, 0.5 * acc_err) + cov_pen

    ulsc = UniversalLSC(
        name="uLSC_Kalman",
        target_need_id="Guidance.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Radar.out"),
        value_distance_fn=tracking_error,
        tolerance=1.2,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )

    ev = BoardEvaluator()
    snaps: List[ScoreBreakdown] = []

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("Radar", "out", c_raw_cm))
        b.add_component(ConsumerBoundary("Guidance", "in", guidance_shape))

    def add_preconditioning(b: Board) -> None:
        b.add_component(RecolorBlock("Widen_P", c_raw_cm, c_raw_cm64, value_fn=float))
        b.add_component(RecolorBlock("Scale_L", c_raw_cm64, c_raw_m, value_fn=lambda cm: float(cm) * 0.01))
        b.connect("Radar.out", "Widen_P.in")
        b.connect("Widen_P.out", "Scale_L.in")

    # S0: Unconnected
    b0 = Board("Ex3_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    # S1: Pre-conditioned input (int32 cm -> float64 m)
    b1 = Board("Ex3_S1")
    bounds(b1)
    add_preconditioning(b1)
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: +Pre-condition (cm/i32 -> m/f64)"))

    # S2: Naive finite-difference estimator (Tier 1 & 2 pass, Tier 3 fails due to noise amplification)
    def naive_diff(msg: Message, state: Dict, tick: int):
        z = float(msg.first_field().value)
        prev_z = state.get("prev_z", z)
        prev_v = state.get("prev_v", 10.0)
        v = z - prev_z if tick > 0 else 10.0
        a = v - prev_v if tick > 1 else 0.0
        state.update({"prev_z": z, "prev_v": v})
        p = msg.first_field().provenance.append_op("Naive", tick)
        return (
            Message.record(
                {
                    "pos_est": Field(z, c_pos, Dynamics("o", 1.0), provenance=p),
                    "vel_est": Field(v, c_vel, Dynamics("o", 1.0), provenance=p),
                    "acc_est": Field(a, c_acc, Dynamics("o", 1.0), provenance=p),
                    "cov_pos": Field(4.5, c_cov_p, Dynamics("o", 1.0), provenance=p),
                    "cov_vel": Field(9.0, c_cov_v, Dynamics("o", 1.0), provenance=p),
                    "cov_acc": Field(18.0, c_cov_a, Dynamics("o", 1.0), provenance=p),
                }
            ),
            state,
        )

    b2 = Board("Ex3_S2")
    bounds(b2)
    add_preconditioning(b2)
    b2.add_component(DeriveBlock("Naive", MessageShape.single(c_raw_m), guidance_shape, naive_diff, static_cost=1.5))
    b2.connect("Scale_L.out", "Naive.in")
    b2.connect("Naive.out", "Guidance.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Naive finite-diff (Tier3 fail)"))

    # S3: Calibrated Kalman Filter DeriveBlock (WIN)
    def kalman_filter(msg: Message, state: Dict, tick: int):
        z = float(msg.first_field().value)
        if tick == 0:
            x, v, a, cov_p, cov_v, cov_a = z, 10.0, 0.0, 1.0, 0.5, 0.2
        else:
            xp = state["x"] + state["v"] + 0.5 * state["a"]
            vp = state["v"] + state["a"]
            r = z - xp
            x = xp + 0.45 * r
            v = vp + 0.15 * r
            a = state["a"] + 0.02 * r
            cov_p = max(0.08, state["cov_p"] * 0.55)
            cov_v = max(0.05, state["cov_v"] * 0.65)
            cov_a = max(0.02, state["cov_a"] * 0.75)
        state.update({"x": x, "v": v, "a": a, "cov_p": cov_p, "cov_v": cov_v, "cov_a": cov_a})
        p = msg.first_field().provenance.append_op("KF", tick)
        return (
            Message.record(
                {
                    "pos_est": Field(round(x, 3), c_pos, Dynamics("o", 1.0), provenance=p),
                    "vel_est": Field(round(v, 3), c_vel, Dynamics("o", 1.0), provenance=p),
                    "acc_est": Field(round(a, 3), c_acc, Dynamics("o", 1.0), provenance=p),
                    "cov_pos": Field(round(cov_p, 3), c_cov_p, Dynamics("o", 1.0), provenance=p),
                    "cov_vel": Field(round(cov_v, 3), c_cov_v, Dynamics("o", 1.0), provenance=p),
                    "cov_acc": Field(round(cov_a, 3), c_cov_a, Dynamics("o", 1.0), provenance=p),
                }
            ),
            state,
        )

    b3 = Board("Ex3_S3")
    bounds(b3)
    add_preconditioning(b3)
    b3.add_component(DeriveBlock("KF", MessageShape.single(c_raw_m), guidance_shape, kalman_filter, static_cost=4.0))
    b3.connect("Scale_L.out", "KF.in")
    b3.connect("KF.out", "Guidance.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Calibrated Kalman Derive (WIN)"))

    return snaps
