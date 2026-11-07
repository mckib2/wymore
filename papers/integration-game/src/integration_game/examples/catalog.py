"""
Progressive runnable demos for Integration Game Examples 1–12.
Each returns a list of ScoreBreakdown snapshots showing fitness toward a three-tier win.
"""
from __future__ import annotations

import json
from typing import Any, Callable, Dict, List, Optional, Tuple

from integration_game import (
    AssembleBlock,
    Board,
    BoardEvaluator,
    CacheStoreBlock,
    Color,
    ConsumerBoundary,
    DeriveBlock,
    Dynamics,
    FanOutBlock,
    Field,
    FilterBlock,
    JoinBlock,
    Message,
    MessageShape,
    MuxSwitchBlock,
    ProducerBoundary,
    Provenance,
    ProvTMRVoteBlock,
    PumpBlock,
    RateAdapterBlock,
    RecolorBlock,
    Representation,
    RepresentationBridgeBlock,
    ScoreBreakdown,
    SourceBlock,
    StaleGateBlock,
    TransferMode,
    UniversalLSC,
    print_progression_table,
)


EvalFn = Callable[[], List[ScoreBreakdown]]


def _eval() -> BoardEvaluator:
    return BoardEvaluator()


# ============================================================================
# Example 1: Autonomous closed loop (internal diagnostic need)
# ============================================================================
def example_01_autonomous() -> List[ScoreBreakdown]:
    """No external Env I/O; Source clock + Derive state invariant observed on diagnostic Need."""
    c_tick = Color("Sys.Clock", "tick", "int32")
    c_ok = Color("Sys.Health", "bool", "bool")
    horizon = 6
    scenario: Dict[int, Dict[str, Message]] = {}  # fully autonomous

    ulsc = UniversalLSC(
        name="uLSC_AutonomousHealth",
        target_need_id="Diag.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: Message.single(
            Field(t, c_tick, Dynamics("env", 1.0), provenance=Provenance(timestamp_tick=t))
        )
        if t % 2 == 0
        else None,
        value_distance_fn=lambda trig, out: 0.0 if out.first_field().value is True else 1.0,
        tolerance=0.0,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )

    def make_consumer(b: Board) -> None:
        b.add_component(
            ConsumerBoundary("Diag", "in", MessageShape.single(c_ok), mode=TransferMode.PUSH)
        )

    snaps: List[ScoreBreakdown] = []
    ev = _eval()

    b0 = Board("Ex1_S0")
    make_consumer(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Diagnostic Need only"))

    b1 = Board("Ex1_S1")
    make_consumer(b1)
    b1.add_component(SourceBlock("Clock", c_tick, value_fn=lambda t: t, period=2))
    b1.connect("Clock.out", "Diag.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Clock wired (color clash)"))

    def health_fn(msg: Message, state: Dict[str, Any], tick: int):
        v = int(msg.first_field().value)
        ok = v >= 0
        prov = msg.first_field().provenance.append_op("Health", tick)
        return Message.single(Field(ok, c_ok, Dynamics("Health.out", 1.0), provenance=prov)), state

    b2 = Board("Ex1_S2")
    make_consumer(b2)
    b2.add_component(SourceBlock("Clock", c_tick, value_fn=lambda t: t, period=2))
    b2.add_component(
        DeriveBlock(
            "Health",
            MessageShape.single(c_tick),
            MessageShape.single(c_ok),
            health_fn,
            static_cost=1.0,
        )
    )
    b2.connect("Clock.out", "Health.in")
    b2.connect("Health.out", "Diag.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Health Derive (WIN)"))
    return snaps


# ============================================================================
# Example 2: Ping/Pong
# ============================================================================
def example_02_ping_pong() -> List[ScoreBreakdown]:
    c_ping = Color(C="Net.Ping", L="SeqNum", P="uint16")
    c_pong = Color(C="Net.Pong", L="SeqNum", P="uint32")
    horizon = 8
    scenario = {
        1: {
            "PingGen.out": Message.single(
                Field(101, c_ping, Dynamics("PingGen.out", 1.0), provenance=Provenance(("PingGen",), timestamp_tick=1))
            )
        },
        5: {
            "PingGen.out": Message.single(
                Field(202, c_ping, Dynamics("PingGen.out", 1.0), provenance=Provenance(("PingGen",), timestamp_tick=5))
            )
        },
    }
    ulsc = UniversalLSC(
        name="uLSC_PingPong",
        target_need_id="PongSink.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("PingGen.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.0,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )
    ev = _eval()
    snaps: List[ScoreBreakdown] = []

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("PingGen", "out", c_ping, mode=TransferMode.PUSH))
        b.add_component(
            ConsumerBoundary(
                "PongSink", "in", MessageShape.single(c_pong), mode=TransferMode.PULL, pull_schedule=lambda t: True
            )
        )

    b0 = Board("Ex2_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex2_S1")
    bounds(b1)
    b1.connect("PingGen.out", "PongSink.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct wire (color+mode)"))

    b2 = Board("Ex2_S2")
    bounds(b2)
    b2.add_component(RecolorBlock("Recolor_CP", c_ping, c_pong, value_fn=lambda x: int(x)))
    b2.connect("PingGen.out", "Recolor_CP.in")
    b2.connect("Recolor_CP.out", "PongSink.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Recolor (mode clash)"))

    b3 = Board("Ex2_S3")
    bounds(b3)
    b3.add_component(RecolorBlock("Recolor_CP", c_ping, c_pong, value_fn=lambda x: int(x)))
    b3.add_component(CacheStoreBlock("LVC", c_pong, retain_on_read=True))
    b3.connect("PingGen.out", "Recolor_CP.in")
    b3.connect("Recolor_CP.out", "LVC.in")
    b3.connect("LVC.out", "PongSink.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: +LVC retain (silence breach)"))

    b4 = Board("Ex2_S4")
    bounds(b4)
    b4.add_component(RecolorBlock("Recolor_CP", c_ping, c_pong, value_fn=lambda x: int(x)))
    b4.add_component(CacheStoreBlock("Queue", c_pong, retain_on_read=False))
    b4.connect("PingGen.out", "Recolor_CP.in")
    b4.connect("Recolor_CP.out", "Queue.in")
    b4.connect("Queue.out", "PongSink.in")
    snaps.append(ev.evaluate(b4, ulsc, scenario, "S4: +Consume queue (WIN)"))
    return snaps


# ============================================================================
# Example 3: Kalman
# ============================================================================
def example_03_kalman() -> List[ScoreBreakdown]:
    c_raw = Color("Track.RawPos", "meters", "float64")
    c_pos = Color("Track.EstPos", "meters", "float64")
    c_vel = Color("Track.EstVel", "m_per_s", "float64")
    c_acc = Color("Track.EstAcc", "m_per_s2", "float64")
    c_cov = Color("Track.EstCov", "m2", "float64")
    guidance = MessageShape(slots={"pos_est": c_pos, "vel_est": c_vel, "acc_est": c_acc, "cov_trace": c_cov})
    horizon = 6
    noisy = [0.0, 11.2, 18.9, 30.8, 39.4, 50.3]
    scenario = {
        t: {
            "Radar.out": Message.single(
                Field(noisy[t], c_raw, Dynamics("Radar.out", 1.0), provenance=Provenance(("Radar",), timestamp_tick=t))
            )
        }
        for t in range(horizon)
    }

    def tracking_error(trig: Message, out: Message) -> float:
        t_tick = trig.first_field().provenance.timestamp_tick
        if t_tick < 2:
            return 0.0
        return abs(float(out.fields["vel_est"].value) - 10.0)

    ulsc = UniversalLSC(
        name="uLSC_Kalman",
        target_need_id="Guidance.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Radar.out"),
        value_distance_fn=tracking_error,
        tolerance=1.5,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )
    ev = _eval()
    snaps: List[ScoreBreakdown] = []

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("Radar", "out", c_raw))
        b.add_component(ConsumerBoundary("Guidance", "in", guidance))

    b0 = Board("Ex3_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    def naive(msg, state, tick):
        z = float(msg.first_field().value)
        prev_z = state.get("prev_z", z)
        prev_v = state.get("prev_v", 10.0)
        v = z - prev_z if tick > 0 else 10.0
        a = v - prev_v if tick > 1 else 0.0
        state.update({"prev_z": z, "prev_v": v})
        p = msg.first_field().provenance.append_op("Naive", tick)
        return (
            Message(
                fields={
                    "pos_est": Field(z, c_pos, Dynamics("o", 1.0), provenance=p),
                    "vel_est": Field(v, c_vel, Dynamics("o", 1.0), provenance=p),
                    "acc_est": Field(a, c_acc, Dynamics("o", 1.0), provenance=p),
                    "cov_trace": Field(9.9, c_cov, Dynamics("o", 1.0), provenance=p),
                }
            ),
            state,
        )

    b1 = Board("Ex3_S1")
    bounds(b1)
    b1.add_component(DeriveBlock("Naive", MessageShape.single(c_raw), guidance, naive, static_cost=1.5))
    b1.connect("Radar.out", "Naive.in")
    b1.connect("Naive.out", "Guidance.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Naive finite-diff (Tier3 fail)"))

    def kalman(msg, state, tick):
        z = float(msg.first_field().value)
        if tick == 0:
            x, v, a, cov = z, 10.0, 0.0, 1.0
        else:
            xp = state["x"] + state["v"] + 0.5 * state["a"]
            vp = state["v"] + state["a"]
            r = z - xp
            x = xp + 0.45 * r
            v = vp + 0.15 * r
            a = state["a"] + 0.02 * r
            cov = max(0.1, state["cov"] * 0.55)
        state.update({"x": x, "v": v, "a": a, "cov": cov})
        p = msg.first_field().provenance.append_op("KF", tick)
        return (
            Message(
                fields={
                    "pos_est": Field(round(x, 3), c_pos, Dynamics("o", 1.0), provenance=p),
                    "vel_est": Field(round(v, 3), c_vel, Dynamics("o", 1.0), provenance=p),
                    "acc_est": Field(round(a, 3), c_acc, Dynamics("o", 1.0), provenance=p),
                    "cov_trace": Field(round(cov, 3), c_cov, Dynamics("o", 1.0), provenance=p),
                }
            ),
            state,
        )

    b2 = Board("Ex3_S2")
    bounds(b2)
    b2.add_component(DeriveBlock("KF", MessageShape.single(c_raw), guidance, kalman, static_cost=4.0))
    b2.connect("Radar.out", "KF.in")
    b2.connect("KF.out", "Guidance.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Kalman Derive (WIN)"))
    return snaps


# ============================================================================
# Example 4: Multi-representation
# ============================================================================
def example_04_multi_rep() -> List[ScoreBreakdown]:
    c = Color("Sensor.Temp", "Celsius", "float32")
    horizon = 4
    scenario = {
        t: {
            "Sens.out": Message.single(
                Field(
                    json.dumps({"t": 20.0 + t}),
                    c,
                    Dynamics("Sens.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("Sens",), timestamp_tick=t),
                )
            )
        }
        for t in range(0, horizon, 2)
    }
    ulsc = UniversalLSC(
        name="uLSC_Rep",
        target_need_id="App.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Sens.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["t"]) - float(out.first_field().value)
        ),
        tolerance=0.01,
        max_delay=1,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary("Sens", "out", c, rep=Representation.BYTE_BLOB_JSON)
        )
        b.add_component(
            ConsumerBoundary(
                "App",
                "in",
                MessageShape.single(c, reps=(Representation.NATIVE_STRUCT,)),
            )
        )

    b0 = Board("Ex4_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex4_S1")
    bounds(b1)
    b1.connect("Sens.out", "App.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct (rep mismatch)"))

    b2 = Board("Ex4_S2")
    bounds(b2)
    b2.add_component(
        RepresentationBridgeBlock(
            "JSON2Native",
            c,
            Representation.BYTE_BLOB_JSON,
            Representation.NATIVE_STRUCT,
            decode_fn=lambda s: float(json.loads(s)["t"]),
        )
    )
    b2.connect("Sens.out", "JSON2Native.in")
    b2.connect("JSON2Native.out", "App.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: +Transcode (WIN)"))
    return snaps


# ============================================================================
# Example 5: Piston / Airframe hierarchical recolor
# ============================================================================
def example_05_piston() -> List[ScoreBreakdown]:
    c_piston_k = Color("Engine.Piston.Temp", "Kelvin", "float32")
    c_air_k = Color("Airframe.Propulsion.Temp", "Kelvin", "float32")
    c_air_c32 = Color("Airframe.Propulsion.Temp", "Celsius", "float32")
    c_air_c64 = Color("Airframe.Propulsion.Temp", "Celsius", "float64")
    horizon = 6
    samples = {0: 573.15, 2: 600.0, 4: 623.15}
    scenario = {
        t: {
            "PistonSensor.out": Message.single(
                Field(
                    json.dumps({"temp": val}),
                    c_piston_k,
                    Dynamics("PistonSensor.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("PistonSensor",), timestamp_tick=t),
                )
            )
        }
        for t, val in samples.items()
    }

    def err(trig, out):
        k = float(json.loads(trig.first_field().value)["temp"])
        return abs((k - 273.15) - float(out.first_field().value))

    ulsc = UniversalLSC(
        name="uLSC_Piston",
        target_need_id="FlightDeck.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("PistonSensor.out"),
        value_distance_fn=err,
        tolerance=0.05,
        max_delay=1,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    def bounds(b: Board) -> None:
        b.add_component(
            ProducerBoundary("PistonSensor", "out", c_piston_k, rep=Representation.BYTE_BLOB_JSON)
        )
        b.add_component(
            ConsumerBoundary(
                "FlightDeck",
                "in",
                MessageShape.single(c_air_c64, reps=(Representation.NATIVE_STRUCT,)),
            )
        )

    b0 = Board("Ex5_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    def add_json(b: Board) -> None:
        b.add_component(
            RepresentationBridgeBlock(
                "JSON_Decode",
                c_piston_k,
                Representation.BYTE_BLOB_JSON,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: float(json.loads(s)["temp"]),
            )
        )

    b1 = Board("Ex5_S1")
    bounds(b1)
    add_json(b1)
    b1.connect("PistonSensor.out", "JSON_Decode.in")
    b1.connect("JSON_Decode.out", "FlightDeck.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: +JSON (color gap)"))

    b3 = Board("Ex5_S3")
    bounds(b3)
    add_json(b3)
    b3.add_component(RecolorBlock("Recolor_C", c_piston_k, c_air_k))
    b3.add_component(RecolorBlock("Bad_LP", c_air_k, c_air_c64, value_fn=lambda k: float(k)))
    b3.connect("PistonSensor.out", "JSON_Decode.in")
    b3.connect("JSON_Decode.out", "Recolor_C.in")
    b3.connect("Recolor_C.out", "Bad_LP.in")
    b3.connect("Bad_LP.out", "FlightDeck.in")
    snaps.append(ev.evaluate(b3, ulsc, scenario, "S3: Lying L-cast (Tier3 fail)"))

    b4 = Board("Ex5_S4")
    bounds(b4)
    add_json(b4)
    b4.add_component(RecolorBlock("Recolor_C", c_piston_k, c_air_k))
    b4.add_component(RecolorBlock("Recolor_L", c_air_k, c_air_c32, value_fn=lambda k: round(k - 273.15, 4)))
    b4.add_component(RecolorBlock("Recolor_P", c_air_c32, c_air_c64, value_fn=float))
    b4.connect("PistonSensor.out", "JSON_Decode.in")
    b4.connect("JSON_Decode.out", "Recolor_C.in")
    b4.connect("Recolor_C.out", "Recolor_L.in")
    b4.connect("Recolor_L.out", "Recolor_P.in")
    b4.connect("Recolor_P.out", "FlightDeck.in")
    snaps.append(ev.evaluate(b4, ulsc, scenario, "S4: Proper C/L/P (WIN)"))
    return snaps


# ============================================================================
# Example 6: Calculator (wrong wiring trap) + brief vending silence
# ============================================================================
def example_06_calculator() -> List[ScoreBreakdown]:
    c_a = Color("ALU.A", "int", "int32")
    c_b = Color("ALU.B", "int", "int32")
    c_y = Color("ALU.Y", "int", "int32")
    horizon = 4
    scenario = {
        t: {
            "A.out": Message.single(Field(10, c_a, Dynamics("A", 1.0), provenance=Provenance(("A",), timestamp_tick=t))),
            "B.out": Message.single(Field(3, c_b, Dynamics("B", 1.0), provenance=Provenance(("B",), timestamp_tick=t))),
        }
        for t in range(horizon)
    }
    # Trigger on A; expect Y = A+B = 13
    ulsc = UniversalLSC(
        name="uLSC_ALU",
        target_need_id="Out.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("A.out"),
        value_distance_fn=lambda trig, out: abs(float(out.first_field().value) - 13.0),
        tolerance=0.0,
        max_delay=1,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []
    out_shape = MessageShape.single(c_y)

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("A", "out", c_a))
        b.add_component(ProducerBoundary("B", "out", c_b))
        b.add_component(ConsumerBoundary("Out", "in", out_shape))

    b0 = Board("Ex6_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    # Wrong: only wire A through identity recolor labeled as Y
    b1 = Board("Ex6_S1")
    bounds(b1)
    b1.add_component(RecolorBlock("Fake", c_a, c_y, value_fn=int))
    b1.connect("A.out", "Fake.in")
    b1.connect("Fake.out", "Out.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: A-only (value breach)"))

    def add_fn(msg, state, tick):
        # Expect assembled record
        a = int(msg.fields["a"].value)
        b = int(msg.fields["b"].value)
        p = msg.fields["a"].provenance.append_op("Add", tick)
        return Message.single(Field(a + b, c_y, Dynamics("Add.out", 1.0), provenance=p)), state

    in_shape = MessageShape(slots={"a": c_a, "b": c_b})
    b2 = Board("Ex6_S2")
    bounds(b2)
    b2.add_component(AssembleBlock("Asm", {"a": c_a, "b": c_b}))
    b2.add_component(DeriveBlock("Add", in_shape, out_shape, add_fn, static_cost=1.0))
    b2.connect("A.out", "Asm.in_a")
    b2.connect("B.out", "Asm.in_b")
    b2.connect("Asm.out", "Add.in")
    b2.connect("Add.out", "Out.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Assemble+Add (WIN)"))
    return snaps


# ============================================================================
# Example 7: Hard latency
# ============================================================================
def example_07_latency() -> List[ScoreBreakdown]:
    c = Color("Nav.Att", "quat", "f64")
    horizon = 5
    scenario = {
        t: {
            "IMU.out": Message.single(
                Field(1.0, c, Dynamics("IMU", 1.0), provenance=Provenance(("IMU",), timestamp_tick=t))
            )
        }
        for t in range(horizon)
    }
    # Must deliver within max_delay=0 (same tick)
    ulsc = UniversalLSC(
        name="uLSC_Lat",
        target_need_id="GNC.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("IMU.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.01,
        min_delay=0,
        max_delay=0,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("IMU", "out", c))
        b.add_component(ConsumerBoundary("GNC", "in", MessageShape.single(c)))

    b0 = Board("Ex7_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    # Heavy path: high-latency Derive misses same-tick deadline (max_delay=0)
    def slow_fn(msg, state, tick):
        # Simulate compute that only emits one tick late via internal buffer
        pending = state.get("pending")
        state["pending"] = msg
        if pending is None:
            return None, state
        f = pending.first_field()
        p = f.provenance.append_op("SlowDCM", tick)
        return Message.single(Field(f.value, c, Dynamics("SlowDCM.out", 1.0), provenance=p)), state

    b1 = Board("Ex7_S1")
    bounds(b1)
    b1.add_component(
        DeriveBlock(
            "SlowDCM",
            MessageShape.single(c),
            MessageShape.single(c),
            slow_fn,
            static_cost=10.0,
            latency=5.0,
        )
    )
    b1.connect("IMU.out", "SlowDCM.in")
    b1.connect("SlowDCM.out", "GNC.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Slow heavy Derive (deadline fail)"))

    b2 = Board("Ex7_S2")
    bounds(b2)
    b2.add_component(RecolorBlock("Fast", c, c, value_fn=float, static_cost=0.1))
    b2.connect("IMU.out", "Fast.in")
    b2.connect("Fast.out", "GNC.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Fast path (WIN)"))
    return snaps


# ============================================================================
# Example 8: Fan-out multi-flow
# ============================================================================
def example_08_fanout() -> List[ScoreBreakdown]:
    c = Color("GPS.Fix", "WGS84", "f64")
    horizon = 4
    scenario = {
        t: {
            "GPS.out": Message.single(
                Field(float(t), c, Dynamics("GPS", 1.0), provenance=Provenance(("GPS",), timestamp_tick=t))
            )
        }
        for t in range(horizon)
    }
    # Monitor primary consumer Logger
    ulsc = UniversalLSC(
        name="uLSC_Fan",
        target_need_id="Logger.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("GPS.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.0,
        max_delay=0,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    b0 = Board("Ex8_S0")
    b0.add_component(ProducerBoundary("GPS", "out", c))
    b0.add_component(ConsumerBoundary("Logger", "in", MessageShape.single(c)))
    b0.add_component(ConsumerBoundary("Gimbal", "in", MessageShape.single(c)))
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected dual needs"))

    b1 = Board("Ex8_S1")
    b1.add_component(ProducerBoundary("GPS", "out", c))
    b1.add_component(ConsumerBoundary("Logger", "in", MessageShape.single(c)))
    b1.add_component(ConsumerBoundary("Gimbal", "in", MessageShape.single(c)))
    b1.connect("GPS.out", "Logger.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Only Logger wired"))

    b2 = Board("Ex8_S2")
    b2.add_component(ProducerBoundary("GPS", "out", c))
    b2.add_component(ConsumerBoundary("Logger", "in", MessageShape.single(c)))
    b2.add_component(ConsumerBoundary("Gimbal", "in", MessageShape.single(c)))
    b2.add_component(FanOutBlock("Fan", c, n_outputs=2))
    b2.connect("GPS.out", "Fan.in")
    b2.connect("Fan.out_0", "Logger.in")
    b2.connect("Fan.out_1", "Gimbal.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: FanOut (WIN)"))
    return snaps


# ============================================================================
# Example 9: Mismatched ticks Cache+Pump
# ============================================================================
def example_09_ticks() -> List[ScoreBreakdown]:
    c = Color("Bus.Sample", "raw", "f32")
    horizon = 8
    # Producer emits only even ticks
    scenario = {
        t: {
            "Slow.out": Message.single(
                Field(float(t), c, Dynamics("Slow", 1.0), provenance=Provenance(("Slow",), timestamp_tick=t))
            )
        }
        for t in range(0, horizon, 2)
    }
    # Consumer pulls every tick — need cache+pump or silence breaches
    ulsc = UniversalLSC(
        name="uLSC_Ticks",
        target_need_id="Fast.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Slow.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.0,
        max_delay=1,
        enforce_silence=False,  # upsampling may repeat; focus on fulfilling triggers
    )
    ev = _eval()
    snaps = []

    def bounds(b: Board, pull: bool = True) -> None:
        b.add_component(ProducerBoundary("Slow", "out", c))
        b.add_component(
            ConsumerBoundary(
                "Fast",
                "in",
                MessageShape.single(c),
                mode=TransferMode.PULL if pull else TransferMode.PUSH,
                pull_schedule=lambda t: True,
            )
        )

    b0 = Board("Ex9_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex9_S1")
    bounds(b1)
    b1.connect("Slow.out", "Fast.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Direct PUSH→PULL"))

    b2 = Board("Ex9_S2")
    bounds(b2)
    b2.add_component(CacheStoreBlock("Cache", c, retain_on_read=True))
    b2.add_component(PumpBlock("Pump", c, period=1))
    # Consumer should be PUSH to match pump, or PULL from cache only
    # Rebuild with PUSH consumer for pump output
    b2 = Board("Ex9_S2")
    b2.add_component(ProducerBoundary("Slow", "out", c))
    b2.add_component(ConsumerBoundary("Fast", "in", MessageShape.single(c), mode=TransferMode.PUSH))
    b2.add_component(CacheStoreBlock("Cache", c, retain_on_read=True))
    b2.add_component(PumpBlock("Pump", c, period=1))
    b2.connect("Slow.out", "Cache.in")
    b2.connect("Cache.out", "Pump.in")
    b2.connect("Pump.out", "Fast.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Cache+Pump upsample (WIN)"))
    return snaps


# ============================================================================
# Example 10: Provenance TMR
# ============================================================================
def example_10_provenance() -> List[ScoreBreakdown]:
    c = Color("Air.Press", "Pa", "f32")
    horizon = 4
    scenario = {
        t: {
            f"S{i}.out": Message.single(
                Field(
                    101325.0,
                    c,
                    Dynamics(f"S{i}", 1.0),
                    provenance=Provenance((f"S{i}",), timestamp_tick=t, trust_score=0.7),
                )
            )
            for i in range(3)
        }
        for t in range(horizon)
    }
    need = MessageShape.single(c, min_trust=0.9, required_assurance="TMR_VOTED")
    ulsc = UniversalLSC(
        name="uLSC_TMR",
        target_need_id="FC.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("S0.out"),
        value_distance_fn=lambda trig, out: abs(float(trig.first_field().value) - float(out.first_field().value)),
        tolerance=0.1,
        max_delay=1,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    def sensors(b: Board) -> None:
        for i in range(3):
            b.add_component(ProducerBoundary(f"S{i}", "out", c))
        b.add_component(ConsumerBoundary("FC", "in", need))

    b0 = Board("Ex10_S0")
    sensors(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex10_S1")
    sensors(b1)
    b1.connect("S0.out", "FC.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Single sensor (prov gap)"))

    b2 = Board("Ex10_S2")
    sensors(b2)
    b2.add_component(ProvTMRVoteBlock("TMR", c))
    b2.connect("S0.out", "TMR.in_0")
    b2.connect("S1.out", "TMR.in_1")
    b2.connect("S2.out", "TMR.in_2")
    b2.connect("TMR.out", "FC.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: TMR vote (WIN)"))
    return snaps


# ============================================================================
# Example 11: Temporal window join
# ============================================================================
def example_11_temporal_join() -> List[ScoreBreakdown]:
    c_id = Color("Tgt.Id", "id", "int")
    c_eo = Color("Tgt.EO", "px", "f32")
    c_sar = Color("Tgt.SAR", "m", "f32")
    left = {"id": c_id, "eo": c_eo}
    right = {"id": c_id, "sar": c_sar}
    horizon = 5
    scenario = {
        1: {
            "EO.out": Message.record(
                {
                    "id": Field(7, c_id, Dynamics("EO", 1.0), provenance=Provenance(("EO",), timestamp_tick=1)),
                    "eo": Field(12.0, c_eo, Dynamics("EO", 1.0), provenance=Provenance(("EO",), timestamp_tick=1)),
                },
                key=7,
            )
        },
        2: {
            "SAR.out": Message.record(
                {
                    "id": Field(7, c_id, Dynamics("SAR", 1.0), provenance=Provenance(("SAR",), timestamp_tick=2)),
                    "sar": Field(3.5, c_sar, Dynamics("SAR", 1.0), provenance=Provenance(("SAR",), timestamp_tick=2)),
                },
                key=7,
            )
        },
    }
    out_slots = {"id": c_id, "eo": c_eo, "sar": c_sar}
    ulsc = UniversalLSC(
        name="uLSC_Join",
        target_need_id="Fuse.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("EO.out"),
        value_distance_fn=lambda trig, out: 0.0
        if ("eo" in out.fields and "sar" in out.fields)
        else 1.0,
        tolerance=0.0,
        min_delay=0,
        max_delay=2,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    def bounds(b: Board) -> None:
        b.add_component(ProducerBoundary("EO", "out", c_eo, shape=MessageShape(slots=left)))
        b.add_component(ProducerBoundary("SAR", "out", c_sar, shape=MessageShape(slots=right)))
        b.add_component(ConsumerBoundary("Fuse", "in", MessageShape(slots=out_slots)))

    b0 = Board("Ex11_S0")
    bounds(b0)
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex11_S1")
    bounds(b1)
    b1.connect("EO.out", "Fuse.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: EO only (shape clash)"))

    b2 = Board("Ex11_S2")
    bounds(b2)
    b2.add_component(JoinBlock("Join", left, right, "id", "id", window=2))
    b2.connect("EO.out", "Join.in_left")
    b2.connect("SAR.out", "Join.in_right")
    b2.connect("Join.out", "Fuse.in")
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Temporal Join (WIN)"))
    return snaps


# ============================================================================
# Example 12: Burst failover MuxSwitch
# ============================================================================
def example_12_failover() -> List[ScoreBreakdown]:
    c = Color("Link.Data", "bytes", "u8")
    horizon = 6
    scenario = {
        t: {
            "Primary.out": Message.single(
                Field(
                    1 if t < 3 else None,
                    c,
                    Dynamics("P", 1.0 if t < 3 else 0.0, acceleration=2.0 if t == 2 else 0.0),
                    provenance=Provenance(("Primary",), timestamp_tick=t),
                )
            )
            if t < 3
            else {},
            "Backup.out": Message.single(
                Field(99, c, Dynamics("B", 1.0), provenance=Provenance(("Backup",), timestamp_tick=t))
            ),
        }
        for t in range(horizon)
    }
    # Simplify scenario construction
    scenario = {}
    for t in range(horizon):
        scenario[t] = {
            "Backup.out": Message.single(
                Field(99, c, Dynamics("B", 1.0), provenance=Provenance(("Backup",), timestamp_tick=t))
            )
        }
        if t < 3:
            scenario[t]["Primary.out"] = Message.single(
                Field(1, c, Dynamics("P", 1.0), provenance=Provenance(("Primary",), timestamp_tick=t))
            )

    ulsc = UniversalLSC(
        name="uLSC_Fail",
        target_need_id="App.in",
        horizon=horizon,
        pre_trigger_fn=lambda t, env: env.get("Backup.out") if t >= 3 else env.get("Primary.out"),
        value_distance_fn=lambda trig, out: 0.0
        if out.first_field().value in (1, 99)
        else 1.0,
        tolerance=0.0,
        max_delay=0,
        enforce_silence=True,
    )
    ev = _eval()
    snaps = []

    b0 = Board("Ex12_S0")
    b0.add_component(ProducerBoundary("Primary", "out", c))
    b0.add_component(ProducerBoundary("Backup", "out", c))
    b0.add_component(ConsumerBoundary("App", "in", MessageShape.single(c)))
    snaps.append(ev.evaluate(b0, ulsc, scenario, "S0: Unconnected"))

    b1 = Board("Ex12_S1")
    b1.add_component(ProducerBoundary("Primary", "out", c))
    b1.add_component(ProducerBoundary("Backup", "out", c))
    b1.add_component(ConsumerBoundary("App", "in", MessageShape.single(c)))
    b1.connect("Primary.out", "App.in")
    snaps.append(ev.evaluate(b1, ulsc, scenario, "S1: Primary only (late unmet)"))

    b2 = Board("Ex12_S2")
    b2.add_component(ProducerBoundary("Primary", "out", c))
    b2.add_component(ProducerBoundary("Backup", "out", c))
    b2.add_component(ConsumerBoundary("App", "in", MessageShape.single(c)))
    mux = MuxSwitchBlock("Mux", c, n_inputs=2, active_index=0)
    b2.add_component(mux)
    b2.connect("Primary.out", "Mux.in_0")
    b2.connect("Backup.out", "Mux.in_1")
    b2.connect("Mux.out", "App.in")
    # Online adaptation: switch to backup at t>=3 by evaluating with active_index=1
    # For board-level demo, set active to 1 for whole run after "detecting" dropout —
    # progressive snapshot uses backup path.
    mux.set_active(1)
    snaps.append(ev.evaluate(b2, ulsc, scenario, "S2: Mux→Backup (WIN)"))
    return snaps


ALL_EXAMPLES: List[Tuple[str, EvalFn]] = [
    ("Example 1: Autonomous Health", example_01_autonomous),
    ("Example 2: Ping/Pong", example_02_ping_pong),
    ("Example 3: Kalman Tracker", example_03_kalman),
    ("Example 4: Multi-Representation", example_04_multi_rep),
    ("Example 5: Piston Telemetry Recolor", example_05_piston),
    ("Example 6: ALU Calculator", example_06_calculator),
    ("Example 7: Hard Latency", example_07_latency),
    ("Example 8: Fan-Out Multi-Flow", example_08_fanout),
    ("Example 9: Mismatched Ticks", example_09_ticks),
    ("Example 10: Provenance TMR", example_10_provenance),
    ("Example 11: Temporal Join", example_11_temporal_join),
    ("Example 12: Failover Mux", example_12_failover),
]


def run_all_examples(verbose: bool = True) -> Dict[str, List[ScoreBreakdown]]:
    results = {}
    for title, fn in ALL_EXAMPLES:
        if verbose:
            print(f"\n>>> {title}")
        snaps = fn()
        results[title] = snaps
        if verbose:
            print_progression_table(snaps)
            for r in snaps:
                if r.notes:
                    print(f"  [{r.snapshot_label}] {r.notes[:2]}{'...' if len(r.notes) > 2 else ''}")
    return results
