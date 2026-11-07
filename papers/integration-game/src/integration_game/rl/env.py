"""
Masked offline synthesis MDP for the Integration Game.
Provides:
  - SynthTask & multi-task benchmark suite (ex02..ex07 + holdout ex15)
  - IntegrationGameEnv with exact telescoping potential shaping (Ng et al., 1999)
    and uLSC Reward Machine pulse shaping
  - Ontology-grounded relational action features phi(s, a) for policy-gradient / PPO agents
"""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple, Union

from integration_game.board import Board
from integration_game.components import (
    AssembleBlock,
    CacheStoreBlock,
    ConsumerBoundary,
    DeriveBlock,
    ProducerBoundary,
    PumpBlock,
    RecolorBlock,
    RepresentationBridgeBlock,
    WymorianComponent,
)
from integration_game.config import DEFAULT_CONFIG, GameConfig
from integration_game.game import AddOperator, AddRoute, FinalizeBoard, IllegalMoveError, Play
from integration_game.primitives import (
    Color,
    Dynamics,
    Field,
    Message,
    MessageShape,
    Provenance,
    Representation,
    TransferMode,
)
from integration_game.scoring import BoardEvaluator, ScoreBreakdown
from integration_game.ulsc import CompositeLSC, RMState, UniversalLSC


ACTION_FEATURE_KEYS: Tuple[str, ...] = (
    "is_add",
    "is_connect",
    "is_finalize",
    "input_live_match",
    "need_progress",
    "completes_chain",
    "op_cost_norm",
    "chain_ready_to_connect",
    "finalize_ready",
)

OBS_KEYS: Tuple[str, ...] = (
    "n_unmet",
    "tier1",
    "tier2",
    "tier3",
    "static",
    "S",
    "rm_state",
    "moves",
    "n_components",
    "n_routes",
    "cut",
    "breaches",
)

# Named rebuild registry so SynthTask / env factories pickle for vector workers.
TASK_REBUILDERS: Dict[str, Callable[..., "SynthTask"]] = {}


def _rebuild_synth_task(fn_name: str, kwargs: Dict[str, Any]) -> "SynthTask":
    return TASK_REBUILDERS[fn_name](**kwargs)


def register_task_rebuilder(fn_name: str, fn: Callable[..., "SynthTask"]) -> None:
    TASK_REBUILDERS[fn_name] = fn


@dataclass
class SynthTask:
    """Frozen synthesis problem: boundaries + catalog factories + scenario + uLSC."""
    name: str
    make_initial_board: Callable[[], Board]
    catalog: List[Tuple[str, Callable[[], WymorianComponent]]]
    scenario: Dict[int, Dict[str, Message]]
    ulsc: Union[UniversalLSC, CompositeLSC]
    max_moves: int = 12
    scripted_moves: Optional[List[Tuple[str, Any]]] = None
    rebuild_fn: Optional[str] = None
    rebuild_kwargs: Dict[str, Any] = field(default_factory=dict)

    def __reduce__(self):
        if not self.rebuild_fn:
            raise TypeError(
                f"SynthTask {self.name!r} is not picklable (missing rebuild_fn)"
            )
        return (_rebuild_synth_task, (self.rebuild_fn, dict(self.rebuild_kwargs)))


def make_ping_pong_task(include_trap: bool = False) -> SynthTask:
    """Ex02: Ping/Pong Request/Response causality synthesis task."""
    c_ping = Color(C="Net.Ping", L="SeqNum", P="uint16")
    c_pong_u16 = Color(C="Net.Pong", L="SeqNum", P="uint16")
    c_pong = Color(C="Net.Pong", L="SeqNum", P="uint32")

    def initial() -> Board:
        b = Board("RL_PingPong")
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
        return b

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        (
            "json_bridge",
            lambda: RepresentationBridgeBlock(
                "JSON2Nat",
                c_ping,
                Representation.BYTE_BLOB_JSON,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: int(json.loads(s)["seq"]),
            ),
        ),
        (
            "recolor_c",
            lambda: RecolorBlock("Recolor_C", c_ping, c_pong_u16, value_fn=int),
        ),
        (
            "recolor_p",
            lambda: RecolorBlock("Recolor_P", c_pong_u16, c_pong, value_fn=int),
        ),
    ]
    if include_trap:
        # Cheap LVC retain-on-read store satisfies Tiers 1-2 with lower static cost
        # than consume-on-read FIFO, but violates Tier-3 hot silence on quiet ticks!
        catalog.append(
            (
                "cache_retain_trap",
                lambda: CacheStoreBlock(
                    "LVC_Trap", c_pong, retain_on_read=True, static_cost=0.2
                ),
            )
        )
    catalog.append(
        (
            "cache_consume",
            lambda: CacheStoreBlock("Queue", c_pong, retain_on_read=False, static_cost=0.5),
        )
    )

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
        name="uLSC_PingPong_RL",
        target_need_id="PongSink.in",
        horizon=8,
        pre_trigger_fn=lambda t, env: env.get("PingGen.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["seq"]) - float(out.first_field().value)
        ),
        tolerance=0.0,
        min_delay=0,
        max_delay=1,
        enforce_silence=True,
    )
    scripted = [
        ("add", "json_bridge"),
        ("connect", ("PingGen.out", "JSON2Nat.in")),
        ("add", "recolor_c"),
        ("connect", ("JSON2Nat.out", "Recolor_C.in")),
        ("add", "recolor_p"),
        ("connect", ("Recolor_C.out", "Recolor_P.in")),
        ("add", "cache_consume"),
        ("connect", ("Recolor_P.out", "Queue.in")),
        ("connect", ("Queue.out", "PongSink.in")),
    ]
    return SynthTask(
        "ex02_ping_pong",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=14,
        scripted_moves=scripted,
        rebuild_fn="make_ping_pong_task",
        rebuild_kwargs={"include_trap": include_trap},
    )


def make_kalman_task(include_trap: bool = True) -> SynthTask:
    """Ex03: Kinematic state estimator synthesis with naive-diff Tier-3 trap."""
    c_raw = Color("Radar.Range", "cm", "int32")
    c_si = Color("Radar.Range", "m", "float64")
    c_est = Color("Track.State", "m_s", "float64")

    def initial() -> Board:
        b = Board("RL_Kalman")
        b.add_component(ProducerBoundary("Radar", "out", c_raw, mode=TransferMode.PUSH))
        b.add_component(
            ConsumerBoundary("Tracker", "in", MessageShape.single(c_est), mode=TransferMode.PUSH)
        )
        return b

    true_vel = 20.0
    noisy_cm = {0: 1015, 1: 2980, 2: 5025, 3: 6975, 4: 9010}
    scenario = {
        t: {
            "Radar.out": Message.single(
                Field(
                    val,
                    c_raw,
                    Dynamics("Radar.out", 1.0),
                    provenance=Provenance(("Radar",), timestamp_tick=t),
                )
            )
        }
        for t, val in noisy_cm.items()
    }

    ulsc = UniversalLSC(
        name="uLSC_Kalman_RL",
        target_need_id="Tracker.in",
        horizon=5,
        pre_trigger_fn=lambda t, env: env.get("Radar.out"),
        value_distance_fn=lambda trig, out: abs(float(out.first_field().value) - true_vel),
        tolerance=0.6,
        max_delay=0,
        enforce_silence=True,
    )

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        (
            "recolor_si",
            lambda: RecolorBlock(
                "CM2M", c_raw, c_si, value_fn=lambda x: float(x) / 100.0, static_cost=0.3
            ),
        ),
    ]
    def _naive_fn(msg: Message, state: Dict[str, Any], tick: int):
        f_in = msg.first_field()
        val = (float(f_in.value) - 10.0) * 1.12
        f_out = Field(
            val,
            c_est,
            Dynamics("NaiveDiff.out", 1.0),
            provenance=f_in.provenance.append_op("NaiveDiff", tick),
        )
        return Message.single(f_out), state

    def _kalman_fn(msg: Message, state: Dict[str, Any], tick: int):
        f_in = msg.first_field()
        val = 20.0 + 0.01 * (float(f_in.value) - 50.0)
        f_out = Field(
            val,
            c_est,
            Dynamics("KalmanFilter.out", 1.0),
            provenance=f_in.provenance.append_op("KalmanFilter", tick),
        )
        return Message.single(f_out), state

    if include_trap:
        # Naive difference amplifies noise beyond 0.6 m/s tolerance, but costs less than Kalman
        catalog.append(
            (
                "naive_diff_trap",
                lambda: DeriveBlock(
                    "NaiveDiff",
                    MessageShape.single(c_si),
                    MessageShape.single(c_est),
                    _naive_fn,
                    static_cost=0.4,
                ),
            )
        )
    catalog.append(
        (
            "kalman_derive",
            lambda: DeriveBlock(
                "KalmanFilter",
                MessageShape.single(c_si),
                MessageShape.single(c_est),
                _kalman_fn,
                static_cost=1.2,
            ),
        )
    )
    scripted = [
        ("add", "recolor_si"),
        ("connect", ("Radar.out", "CM2M.in")),
        ("add", "kalman_derive"),
        ("connect", ("CM2M.out", "KalmanFilter.in")),
        ("connect", ("KalmanFilter.out", "Tracker.in")),
    ]
    return SynthTask(
        "ex03_kalman",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=10,
        scripted_moves=scripted,
        rebuild_fn="make_kalman_task",
        rebuild_kwargs={"include_trap": include_trap},
    )


def make_gateway_task() -> SynthTask:
    """Ex04: Multi-representation gateway (MIL-STD-1553 -> NATIVE -> CDR_DDS)."""
    c_1553 = Color("Link16.Track.Alt", "ft_Q12_4", "uint16")
    c_si = Color("C2.Track.Alt", "meters", "float64")

    def initial() -> Board:
        b = Board("RL_Gateway")
        b.add_component(
            ProducerBoundary(
                "Link16",
                "out",
                c_1553,
                mode=TransferMode.PUSH,
                rep=Representation.MIL_STD_1553,
            )
        )
        b.add_component(
            ConsumerBoundary(
                "C2_DDS",
                "in",
                MessageShape.single(c_si, reps=(Representation.CDR_DDS,)),
                mode=TransferMode.PUSH,
            )
        )
        return b

    scenario = {
        t: {
            "Link16.out": Message.single(
                Field(
                    16000,  # Q12.4 for 1000.0 ft
                    c_1553,
                    Dynamics("Link16.out", 1.0),
                    representation=Representation.MIL_STD_1553,
                    provenance=Provenance(("Link16",), timestamp_tick=t),
                )
            )
        }
        for t in (0, 2, 4)
    }

    ulsc = UniversalLSC(
        name="uLSC_Gateway_RL",
        target_need_id="C2_DDS.in",
        horizon=6,
        pre_trigger_fn=lambda t, env: env.get("Link16.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(out.first_field().value)["alt_m"]) - 304.8
        ),
        tolerance=0.1,
        max_delay=0,
        enforce_silence=True,
    )

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        (
            "unpack_1553",
            lambda: RepresentationBridgeBlock(
                "Unpack1553",
                c_1553,
                Representation.MIL_STD_1553,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda w: float(w) / 16.0,
            ),
        ),
        (
            "ft_to_m",
            lambda: RecolorBlock(
                "Ft2M",
                c_1553,
                c_si,
                value_fn=lambda ft: round(float(ft) * 0.3048, 4),
            ),
        ),
        (
            "pack_dds",
            lambda: RepresentationBridgeBlock(
                "PackDDS",
                c_si,
                Representation.NATIVE_STRUCT,
                Representation.CDR_DDS,
                decode_fn=lambda m: json.dumps({"alt_m": float(m)}),
            ),
        ),
    ]
    scripted = [
        ("add", "unpack_1553"),
        ("connect", ("Link16.out", "Unpack1553.in")),
        ("add", "ft_to_m"),
        ("connect", ("Unpack1553.out", "Ft2M.in")),
        ("add", "pack_dds"),
        ("connect", ("Ft2M.out", "PackDDS.in")),
        ("connect", ("PackDDS.out", "C2_DDS.in")),
    ]
    return SynthTask(
        "ex04_multi_rep",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=12,
        scripted_moves=scripted,
        rebuild_fn="make_gateway_task",
        rebuild_kwargs={},
    )


def make_piston_task(include_trap: bool = True) -> SynthTask:
    """Ex05: Hierarchical UDDL entity & unit synthesis with lying-cast Tier-3 trap."""
    c_f = Color("Engine.Cylinder1.Piston.CrownTemp", "Fahrenheit", "float32")
    c_k = Color("Airframe.Propulsion.CoreTemp", "Kelvin", "float64")

    def initial() -> Board:
        b = Board("RL_Piston")
        b.add_component(ProducerBoundary("PistonSensor", "out", c_f, mode=TransferMode.PULL))
        b.add_component(
            ConsumerBoundary("PropMonitor", "in", MessageShape.single(c_k), mode=TransferMode.PUSH)
        )
        return b

    scenario = {
        t: {
            "PistonSensor.out": Message.single(
                Field(
                    212.0,  # 212 F = 373.15 K
                    c_f,
                    Dynamics("PistonSensor.out", 0.0),
                    provenance=Provenance(("PistonSensor",), timestamp_tick=t),
                )
            )
        }
        for t in (0, 2, 4)
    }

    ulsc = UniversalLSC(
        name="uLSC_Piston_RL",
        target_need_id="PropMonitor.in",
        horizon=5,
        pre_trigger_fn=lambda t, env: env.get("PistonSensor.out"),
        value_distance_fn=lambda trig, out: abs(float(out.first_field().value) - 373.15),
        tolerance=0.1,
        max_delay=0,
        enforce_silence=True,
    )

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        (
            "pump",
            lambda: PumpBlock("SensorPump", c_f, period=2, static_cost=0.5),
        ),
    ]
    if include_trap:
        # Lying identity cast passes Tiers 1-2 with static_cost=0.1, but fails Tier 3!
        catalog.append(
            (
                "lying_cast_trap",
                lambda: RecolorBlock(
                    "LyingCast", c_f, c_k, value_fn=float, static_cost=0.1
                ),
            )
        )
    catalog.append(
        (
            "honest_f2k",
            lambda: RecolorBlock(
                "HonestF2K",
                c_f,
                c_k,
                value_fn=lambda f: (float(f) - 32.0) * (5.0 / 9.0) + 273.15,
                static_cost=0.5,
            ),
        )
    )
    scripted = [
        ("add", "pump"),
        ("connect", ("PistonSensor.out", "SensorPump.in")),
        ("add", "honest_f2k"),
        ("connect", ("SensorPump.out", "HonestF2K.in")),
        ("connect", ("HonestF2K.out", "PropMonitor.in")),
    ]
    return SynthTask(
        "ex05_piston",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=10,
        scripted_moves=scripted,
        rebuild_fn="make_piston_task",
        rebuild_kwargs={"include_trap": include_trap},
    )


def make_calculator_task(
    include_trap: bool = True, weak_coincidence_scenario: bool = False
) -> SynthTask:
    """
    Ex06: Non-Commutative Kinetic Energy ALU (E_k = 0.5 * m * v^2).
    If `weak_coincidence_scenario=True`, only tests symmetric m=10, v=10 where
    swapped ALU (0.5 * v * m^2 = 500) coincides with true ALU (0.5 * m * v^2 = 500).
    After CEGIS counterexample augmentation (`weak_coincidence_scenario=False`),
    includes asymmetric (m=2.0, v=1.5) where swapped ALU fails Tier 3.
    """
    c_m = Color("Mass", "kg", "float64")
    c_v = Color("Velocity", "m_per_s", "float64")
    c_ek = Color("KineticEnergy", "Joules", "float64")

    def initial() -> Board:
        b = Board("RL_Calculator")
        b.add_component(ProducerBoundary("MassSrc", "out", c_m, mode=TransferMode.PUSH))
        b.add_component(ProducerBoundary("VelSrc", "out", c_v, mode=TransferMode.PUSH))
        b.add_component(
            ConsumerBoundary("EnergySink", "in", MessageShape.single(c_ek), mode=TransferMode.PUSH)
        )
        return b

    samples = [(10.0, 10.0)] if weak_coincidence_scenario else [(10.0, 10.0), (2.0, 1.5)]
    scenario: Dict[int, Dict[str, Message]] = {}
    for idx, (m_val, v_val) in enumerate(samples):
        t = idx * 2
        scenario[t] = {
            "MassSrc.out": Message.single(
                Field(
                    m_val,
                    c_m,
                    Dynamics("MassSrc.out", 1.0),
                    provenance=Provenance(("MassSrc",), timestamp_tick=t),
                )
            ),
            "VelSrc.out": Message.single(
                Field(
                    v_val,
                    c_v,
                    Dynamics("VelSrc.out", 1.0),
                    provenance=Provenance(("VelSrc",), timestamp_tick=t),
                )
            ),
        }

    def expected_err(trig: Message, out: Message) -> float:
        m_val = float(trig.first_field().value)
        v_val = 10.0 if abs(m_val - 10.0) < 1e-6 else 1.5
        true_ek = 0.5 * m_val * (v_val ** 2)
        return abs(float(out.first_field().value) - true_ek)

    ulsc = UniversalLSC(
        name="uLSC_Calculator_RL",
        target_need_id="EnergySink.in",
        horizon=4,
        pre_trigger_fn=lambda t, env: env.get("MassSrc.out"),
        value_distance_fn=expected_err,
        tolerance=1e-3,
        max_delay=0,
        enforce_silence=True,
    )

    in_slots = {"m": c_m, "v": c_v}

    def _swapped_ke(msg: Message, state: Dict[str, Any], tick: int):
        m = float(msg.fields["m"].value)
        v = float(msg.fields["v"].value)
        val = 0.5 * v * (m ** 2)
        f = Field(
            val,
            c_ek,
            Dynamics("ALU_Swapped.out", 1.0),
            provenance=msg.fields["m"].provenance.append_op("ALU_Swapped", tick),
        )
        return Message.single(f), state

    def _true_ke(msg: Message, state: Dict[str, Any], tick: int):
        m = float(msg.fields["m"].value)
        v = float(msg.fields["v"].value)
        val = 0.5 * m * (v ** 2)
        f = Field(
            val,
            c_ek,
            Dynamics("ALU_True.out", 1.0),
            provenance=msg.fields["m"].provenance.append_op("ALU_True", tick),
        )
        return Message.single(f), state

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        ("assemble_mv", lambda: AssembleBlock("AsmMV", in_slots, static_cost=0.3)),
    ]
    if include_trap:
        catalog.append(
            (
                "alu_swapped_trap",
                lambda: DeriveBlock(
                    "ALU_Swapped",
                    MessageShape(slots=in_slots),
                    MessageShape.single(c_ek),
                    _swapped_ke,
                    static_cost=0.2,
                ),
            )
        )
    catalog.append(
        (
            "alu_correct",
            lambda: DeriveBlock(
                "ALU_True",
                MessageShape(slots=in_slots),
                MessageShape.single(c_ek),
                _true_ke,
                static_cost=2.0,
            ),
        )
    )
    scripted = [
        ("add", "assemble_mv"),
        ("connect", ("MassSrc.out", "AsmMV.in_m")),
        ("connect", ("VelSrc.out", "AsmMV.in_v")),
        ("add", "alu_correct"),
        ("connect", ("AsmMV.out", "ALU_True.in")),
        ("connect", ("ALU_True.out", "EnergySink.in")),
    ]
    return SynthTask(
        "ex06_calculator",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=10,
        scripted_moves=scripted,
        rebuild_fn="make_calculator_task",
        rebuild_kwargs={
            "include_trap": include_trap,
            "weak_coincidence_scenario": weak_coincidence_scenario,
        },
    )


def make_latency_task(include_trap: bool = True) -> SynthTask:
    """Ex07: Hard real-time threat avoidance synthesis with multi-tick latency trap."""
    c_rwr = Color("RWR.ThreatBearing", "deg", "float32")
    c_cmd = Color("Countermeasure.EvasionHeading", "rad", "float64")

    def initial() -> Board:
        b = Board("RL_Latency")
        b.add_component(ProducerBoundary("RWR", "out", c_rwr, mode=TransferMode.PUSH))
        b.add_component(
            ConsumerBoundary("Autopilot", "in", MessageShape.single(c_cmd), mode=TransferMode.PUSH)
        )
        return b

    scenario = {
        t: {
            "RWR.out": Message.single(
                Field(
                    90.0,
                    c_rwr,
                    Dynamics("RWR.out", 1.0),
                    provenance=Provenance(("RWR",), timestamp_tick=t),
                )
            )
        }
        for t in range(6)
    }
    ulsc = UniversalLSC(
        name="uLSC_Latency_RL",
        target_need_id="Autopilot.in",
        horizon=6,
        pre_trigger_fn=lambda t, env: env.get("RWR.out") if t == 0 else None,
        value_distance_fn=lambda trig, out: abs(
            (float(trig.first_field().value) + 180.0) * 0.0174532925 - float(out.first_field().value)
        ),
        tolerance=0.01,
        max_delay=1,
        enforce_silence=False,
    )

    def _make_delayed_solver(delay_ticks: int, cid: str):
        def _fn(msg: Message, state: Dict[str, Any], tick: int):
            q = state.setdefault("q", [])
            f_in = msg.first_field()
            val = (float(f_in.value) + 180.0) * 0.0174532925
            f_out = Field(
                val,
                c_cmd,
                Dynamics(f"{cid}.out", 1.0),
                provenance=f_in.provenance.append_op(cid, tick),
            )
            q.append((tick, Message.single(f_out)))
            if q and (tick - q[0][0]) >= delay_ticks:
                _, ready = q.pop(0)
                return ready, state
            return None, state

        return _fn

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = []
    if include_trap:
        # Cheap 3-tick batch solver passes Tiers 1-2 but misses the 1-tick hard deadline
        catalog.append(
            (
                "slow_solver_trap",
                lambda: DeriveBlock(
                    "SlowSolver",
                    MessageShape.single(c_rwr),
                    MessageShape.single(c_cmd),
                    _make_delayed_solver(3, "SlowSolver"),
                    static_cost=0.2,
                    latency=3.0,
                ),
            )
        )
    catalog.append(
        (
            "fast_solver",
            lambda: RecolorBlock(
                "FastSolver",
                c_rwr,
                c_cmd,
                value_fn=lambda x: (float(x) + 180.0) * 0.0174532925,
                static_cost=0.8,
            ),
        )
    )
    scripted = [
        ("add", "fast_solver"),
        ("connect", ("RWR.out", "FastSolver.in")),
        ("connect", ("FastSolver.out", "Autopilot.in")),
    ]
    return SynthTask(
        "ex07_latency",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=8,
        scripted_moves=scripted,
        rebuild_fn="make_latency_task",
        rebuild_kwargs={"include_trap": include_trap},
    )


def make_industrial_holdout_task(include_trap: bool = True) -> SynthTask:
    """
    Ex15: Industrial FACE/SOSA-flavored multi-bus holdout (MIL-STD-1553 -> NATIVE -> knots -> float64 -> PULL).
    Used to test zero-shot and fine-tuned transfer of relational policies trained on ex02..ex07.
    """
    c_bus = Color("Aircraft.Status.IAS", "m_per_s", "float32")
    c_dds_ms = Color("Guidance.Airspeed", "m_per_s", "float32")
    c_dds_kt = Color("Guidance.Airspeed", "knots", "float32")
    c_dds_kt64 = Color("Guidance.Airspeed", "knots", "float64")

    def initial() -> Board:
        b = Board("RL_Ex15_Industrial")
        b.add_component(
            ProducerBoundary(
                "Bus1553",
                "out",
                c_bus,
                mode=TransferMode.PUSH,
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
        return b

    samples = {0: 100.0, 2: 110.0, 4: 120.0}
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

    ulsc = UniversalLSC(
        name="uLSC_IndustrialIAS_RL",
        target_need_id="Guidance.in",
        horizon=6,
        pre_trigger_fn=lambda t, env: env.get("Bus1553.out"),
        value_distance_fn=lambda trig, out: abs(
            float(json.loads(trig.first_field().value)["ias_mps"]) * 1.94384
            - float(out.first_field().value)
        ),
        tolerance=0.5,
        max_delay=1,
        enforce_silence=True,
    )

    catalog: List[Tuple[str, Callable[[], WymorianComponent]]] = [
        (
            "decode_1553",
            lambda: RepresentationBridgeBlock(
                "1553_Decode",
                c_bus,
                Representation.MIL_STD_1553,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: float(json.loads(s)["ias_mps"]),
            ),
        ),
        (
            "recolor_c",
            lambda: RecolorBlock("Recolor_C", c_bus, c_dds_ms, value_fn=float),
        ),
        (
            "recolor_l",
            lambda: RecolorBlock(
                "Recolor_L", c_dds_ms, c_dds_kt, value_fn=lambda x: round(float(x) * 1.94384, 4)
            ),
        ),
        (
            "recolor_p",
            lambda: RecolorBlock("Recolor_P", c_dds_kt, c_dds_kt64, value_fn=float),
        ),
    ]
    if include_trap:
        catalog.append(
            (
                "latch_retain_trap",
                lambda: CacheStoreBlock(
                    "Latch_Retain", c_dds_kt64, retain_on_read=True, static_cost=0.2
                ),
            )
        )
    catalog.append(
        (
            "latch_consume",
            lambda: CacheStoreBlock(
                "Latch", c_dds_kt64, retain_on_read=False, static_cost=0.5
            ),
        )
    )
    scripted = [
        ("add", "decode_1553"),
        ("connect", ("Bus1553.out", "1553_Decode.in")),
        ("add", "recolor_c"),
        ("connect", ("1553_Decode.out", "Recolor_C.in")),
        ("add", "recolor_l"),
        ("connect", ("Recolor_C.out", "Recolor_L.in")),
        ("add", "recolor_p"),
        ("connect", ("Recolor_L.out", "Recolor_P.in")),
        ("add", "latch_consume"),
        ("connect", ("Recolor_P.out", "Latch.in")),
        ("connect", ("Latch.out", "Guidance.in")),
    ]
    return SynthTask(
        "ex15_industrial_avionics",
        initial,
        catalog,
        scenario,
        ulsc,
        max_moves=15,
        scripted_moves=scripted,
        rebuild_fn="make_industrial_holdout_task",
        rebuild_kwargs={"include_trap": include_trap},
    )


def make_training_tasks(include_traps: bool = True) -> List[SynthTask]:
    """Return the 6 training tasks (ex02..ex07) for multi-task offline RL."""
    return [
        make_ping_pong_task(include_trap=include_traps),
        make_kalman_task(include_trap=include_traps),
        make_gateway_task(),
        make_piston_task(include_trap=include_traps),
        make_calculator_task(include_trap=include_traps, weak_coincidence_scenario=False),
        make_latency_task(include_trap=include_traps),
    ]


register_task_rebuilder("make_ping_pong_task", make_ping_pong_task)
register_task_rebuilder("make_kalman_task", make_kalman_task)
register_task_rebuilder("make_gateway_task", make_gateway_task)
register_task_rebuilder("make_piston_task", make_piston_task)
register_task_rebuilder("make_calculator_task", make_calculator_task)
register_task_rebuilder("make_latency_task", make_latency_task)
register_task_rebuilder("make_industrial_holdout_task", make_industrial_holdout_task)

TASK_NAME_TO_FACTORY: Dict[str, Callable[..., SynthTask]] = {
    "ex02": make_ping_pong_task,
    "ex02_ping_pong": make_ping_pong_task,
    "ex03": make_kalman_task,
    "ex03_kalman": make_kalman_task,
    "ex04": make_gateway_task,
    "ex04_multi_rep": make_gateway_task,
    "ex05": make_piston_task,
    "ex05_piston": make_piston_task,
    "ex06": make_calculator_task,
    "ex06_calculator": make_calculator_task,
    "ex07": make_latency_task,
    "ex07_latency": make_latency_task,
    "ex15": make_industrial_holdout_task,
    "ex15_industrial_avionics": make_industrial_holdout_task,
}


@dataclass
class StepResult:
    obs: Dict[str, float]
    reward: float
    done: bool
    info: Dict[str, Any]


class IntegrationGameEnv:
    """
    Discrete synthesis MDP environment.
    Action ids index into legal_moves() for the current state (masked).
    Implements exact telescoping potential-based reward shaping (Ng et al., 1999)
    and uLSC Reward Machine pulse deltas.
    """

    def __init__(
        self,
        task: SynthTask,
        step_penalty: float = 0.05,
        rm_shaping_weight: float = 0.01,
        potential_shaping_weight: float = 0.25,
        gamma: float = 0.99,
        use_rm_shaping: bool = True,
        use_omega_breach: bool = True,
        config: Optional[GameConfig] = None,
        raise_on_illegal: bool = False,
    ):
        self.task = task
        self.step_penalty = step_penalty
        self.rm_shaping_weight = rm_shaping_weight
        self.potential_shaping_weight = potential_shaping_weight
        self.gamma = gamma
        self.use_rm_shaping = use_rm_shaping
        self.use_omega_breach = use_omega_breach
        self.config = config or DEFAULT_CONFIG
        self.raise_on_illegal = raise_on_illegal
        self.evaluator = BoardEvaluator(game_config=self.config)
        self.play: Optional[Play] = None
        self.moves_taken = 0
        self._last_rm_reward = 0.0
        self._last_potential = 0.0
        self._catalog_used: set = set()
        self._catalog_map: Dict[str, Callable[[], WymorianComponent]] = dict(task.catalog)
        self._seed: Optional[int] = None

    def __reduce__(self):
        """Pickle via task rebuild (fresh env); mid-episode board state is not serialized."""
        if not self.task.rebuild_fn:
            raise TypeError("IntegrationGameEnv requires a picklable SynthTask.rebuild_fn")
        init_kwargs = {
            "step_penalty": self.step_penalty,
            "rm_shaping_weight": self.rm_shaping_weight,
            "potential_shaping_weight": self.potential_shaping_weight,
            "gamma": self.gamma,
            "use_rm_shaping": self.use_rm_shaping,
            "use_omega_breach": self.use_omega_breach,
            "raise_on_illegal": self.raise_on_illegal,
        }
        return (_rebuild_integration_env, (self.task.rebuild_fn, dict(self.task.rebuild_kwargs), init_kwargs))

    def reset(self, seed: Optional[int] = None) -> Dict[str, float]:
        if seed is not None:
            self._seed = int(seed)
        self.play = Play(board=self.task.make_initial_board())
        self.moves_taken = 0
        self._catalog_used = set()
        self._catalog_map = dict(self.task.catalog)
        score0 = self._quick_score()
        self._last_rm_reward = float(score0.tba_result.total_rm_reward)
        self._last_potential = -float(score0.tier1_struct_penalty + score0.tier2_kin_penalty)
        return self.observe(score=score0)

    def get_state(self) -> Dict[str, Any]:
        """Snapshot MDP bookkeeping + Play for MCTS/beam (deepcopy)."""
        assert self.play is not None
        return {
            "play": self.play.clone(),
            "moves_taken": self.moves_taken,
            "catalog_used": set(self._catalog_used),
            "last_rm_reward": self._last_rm_reward,
            "last_potential": self._last_potential,
        }

    def set_state(self, state: Dict[str, Any]) -> None:
        self.play = state["play"].clone()
        self.moves_taken = int(state["moves_taken"])
        self._catalog_used = set(state["catalog_used"])
        self._last_rm_reward = float(state["last_rm_reward"])
        self._last_potential = float(state["last_potential"])

    def clone(self) -> "IntegrationGameEnv":
        """Deep copy suitable for tree search / lookahead."""
        twin = IntegrationGameEnv(
            task=self.task,
            step_penalty=self.step_penalty,
            rm_shaping_weight=self.rm_shaping_weight,
            potential_shaping_weight=self.potential_shaping_weight,
            gamma=self.gamma,
            use_rm_shaping=self.use_rm_shaping,
            use_omega_breach=self.use_omega_breach,
            config=self.config,
            raise_on_illegal=self.raise_on_illegal,
        )
        twin._seed = self._seed
        twin._catalog_map = dict(self._catalog_map)
        if self.play is not None:
            twin.set_state(self.get_state())
        return twin

    def observe(self, score: Optional[ScoreBreakdown] = None) -> Dict[str, float]:
        assert self.play is not None
        unmet = self.play.unmet_needs()
        score = score or self._quick_score()
        rm_state = 0.0
        if score.tba_result.rm_state_trace:
            last = score.tba_result.rm_state_trace[-1]
            rm_state = float(list(RMState).index(last))
        return {
            "n_unmet": float(len(unmet)),
            "tier1": float(score.tier1_struct_penalty),
            "tier2": float(score.tier2_kin_penalty),
            "tier3": float(score.tier3_tba_penalty),
            "static": float(score.static_cost),
            "S": float(score.fitness_score_S),
            "rm_state": rm_state,
            "moves": float(self.moves_taken),
            "n_components": float(len(self.play.board.components)),
            "n_routes": float(len(self.play.board.routes)),
            "cut": float(score.tba_result.cut_progress_ratio),
            "breaches": float(score.tba_result.hot_breaches),
        }

    def _quick_score(self) -> ScoreBreakdown:
        assert self.play is not None
        return self.evaluator.evaluate(
            self.play.board, self.task.ulsc, self.task.scenario, "env"
        )

    def structural_score(self) -> ScoreBreakdown:
        """Cheap Tier-1/2 + static score without TBA simulate (lookahead / MCTS)."""
        assert self.play is not None
        return self.evaluator.evaluate_structural(self.play.board, "structural")

    def legal_moves(self) -> List[Tuple[str, Any]]:
        """Return list of (kind, payload) legal actions. Empty if Play is finalized."""
        assert self.play is not None
        if self.play.finalized:
            return []
        moves: List[Tuple[str, Any]] = []
        board = self.play.board

        for name, factory in self.task.catalog:
            if name in self._catalog_used:
                continue
            probe = factory()
            if probe.comp_id not in board.components:
                moves.append(("add", name))

        offers: List[str] = []
        needs: List[str] = []
        for comp in board.components.values():
            for iface in comp.offers.values():
                offers.append(iface.full_id)
            for iface in comp.needs.values():
                if iface.connected_route_id is None:
                    needs.append(iface.full_id)
        for o in offers:
            for n in needs:
                reasons = board.check_route_compatibility(o, n, require_exact_transfer=True)
                if not reasons:
                    rid = f"{o}-->{n}"
                    if rid not in board.routes:
                        moves.append(("connect", (o, n)))

        moves.append(("finalize", None))
        return moves

    def _interface_gap(self, offer_if: Any, need_if: Any) -> float:
        """Compute normalized semantic + representation + mode gap between two interfaces."""
        c_offer = offer_if.shape.primary_color
        c_need = need_if.shape.primary_color
        gap = 0.0
        if c_offer is not None and c_need is not None:
            gap += c_offer.distance_to(c_need, self.config.color_distance)
        if not set(offer_if.shape.allowed_reps).intersection(
            set(need_if.shape.allowed_reps)
        ):
            gap += 1.0
        if offer_if.mode != need_if.mode:
            gap += 1.0
        return gap

    def action_features(self, kind: str, payload: Any) -> Dict[str, float]:
        """
        Compute ontology-grounded relational features phi(s, a) for a candidate move.
        Uses only UDDL Color/Representation/TransferMode port metadata and board graph topology.
        """
        assert self.play is not None
        board = self.play.board
        live_offer_ifs = board.live_offers()
        live_offer_ids = {iface.full_id for iface in live_offer_ifs}

        unmet_consumer_ifs = [
            iface
            for c in board.consumers
            for iface in c.needs.values()
            if iface.connected_route_id is None
        ]
        all_unmet_ifs = [
            iface
            for comp in board.components.values()
            for iface in comp.needs.values()
            if iface.connected_route_id is None
        ]

        feats: Dict[str, float] = {
            "is_add": 1.0 if kind == "add" else 0.0,
            "is_connect": 1.0 if kind == "connect" else 0.0,
            "is_finalize": 1.0 if kind == "finalize" else 0.0,
            "input_live_match": 0.0,
            "need_progress": 0.0,
            "completes_chain": 0.0,
            "op_cost_norm": 0.0,
            "chain_ready_to_connect": 0.0,
            "finalize_ready": 0.0,
        }

        if kind == "add":
            probe = self._catalog_map[payload]()
            feats["op_cost_norm"] = -min(1.0, float(probe.static_cost) / 5.0)
            probe_needs = list(probe.needs.values())
            probe_offers = list(probe.offers.values())

            if probe_needs and live_offer_ifs:
                matched = 0
                for pn in probe_needs:
                    if any(
                        lo.mode == pn.mode and lo.shape.compatible_with(pn.shape)
                        for lo in live_offer_ifs
                    ):
                        matched += 1
                feats["input_live_match"] = float(matched) / float(len(probe_needs))

            if probe_offers and unmet_consumer_ifs and live_offer_ifs:
                best_gain = 0.0
                for cn in unmet_consumer_ifs:
                    cur_best = min(self._interface_gap(lo, cn) for lo in live_offer_ifs)
                    new_best = min(self._interface_gap(po, cn) for po in probe_offers)
                    best_gain = max(best_gain, (cur_best - new_best) / 5.0)
                feats["need_progress"] = max(-1.0, min(1.0, best_gain))

        elif kind == "connect":
            src_id, tgt_id = payload
            src_if = board.get_interface(src_id)
            tgt_if = board.get_interface(tgt_id)
            tgt_comp_id = tgt_id.split(".", 1)[0]
            tgt_comp = board.components[tgt_comp_id]

            is_live_src = src_id in live_offer_ids
            feats["input_live_match"] = 1.0 if is_live_src else -0.5
            feats["chain_ready_to_connect"] = 1.0 if is_live_src else 0.0

            if isinstance(tgt_comp, ConsumerBoundary):
                feats["need_progress"] = 1.0
                feats["completes_chain"] = 1.0 if is_live_src else 0.2
            else:
                comp_offers = list(tgt_comp.offers.values())
                if comp_offers and unmet_consumer_ifs:
                    cur_gap = min(self._interface_gap(src_if, cn) for cn in unmet_consumer_ifs)
                    out_gap = min(
                        self._interface_gap(co, cn)
                        for co in comp_offers
                        for cn in unmet_consumer_ifs
                    )
                    feats["need_progress"] = max(0.1, min(1.0, (cur_gap - out_gap + 0.5) / 3.0))
                else:
                    feats["need_progress"] = 0.3

        elif kind == "finalize":
            if len(all_unmet_ifs) == 0:
                score = self._quick_score()
                feats["finalize_ready"] = 1.0 if score.is_winning_play else -0.2
            else:
                feats["finalize_ready"] = -1.0

        return feats

    def action_signature(self, kind: str, payload: Any) -> str:
        """Canonical task-scoped signature for a candidate legal move."""
        return f"{self.task.name}:{kind}:{payload}"

    def apply_only(self, kind: str, payload: Any) -> None:
        """
        Mutate the board with a legal move without scoring or reward shaping.
        Used by structural lookahead / MCTS expansion.
        """
        assert self.play is not None
        if kind == "add":
            factory = self._catalog_map[payload]
            comp = factory()
            self.play.apply(AddOperator(comp))
            self._catalog_used.add(payload)
        elif kind == "connect":
            src, tgt = payload
            self.play.apply(AddRoute(src, tgt, strict=True))
        elif kind == "finalize":
            self.play.apply(FinalizeBoard())
        else:
            raise IllegalMoveError(f"unknown_kind:{kind}")
        self.moves_taken += 1

    def step_move(self, kind: str, payload: Any) -> StepResult:
        """Apply a concrete (kind, payload) move; used by Gymnasium stable-slot adapter."""
        assert self.play is not None
        legal = self.legal_moves()
        if not legal:
            return StepResult(
                self.observe(),
                -1.0,
                True,
                {"error": "no_legal_moves", "terminal_reason": "no_legal_moves"},
            )
        if not any(k == kind and p == payload for k, p in legal):
            return self._illegal_step(f"masked_or_unknown:{(kind, payload)}")

        reward = -self.step_penalty
        info: Dict[str, Any] = {"action": kind, "payload": payload}
        done = False
        terminated = False
        truncated = False

        try:
            if kind == "add":
                factory = self._catalog_map[payload]
                # Cost shaping uses static_cost before apply_only consumes the factory
                probe = factory()
                reward -= float(probe.static_cost) * 0.1
                self.play.apply(AddOperator(probe))
                self._catalog_used.add(payload)
            elif kind == "connect":
                src, tgt = payload
                self.play.apply(AddRoute(src, tgt, strict=True))
            elif kind == "finalize":
                self.play.apply(FinalizeBoard())
                done = True
            else:
                return self._illegal_step(f"unknown_kind:{kind}")
        except IllegalMoveError as exc:
            return self._illegal_step(str(exc))

        self.moves_taken += 1
        score = self._quick_score()

        rm_total = float(score.tba_result.total_rm_reward)
        new_potential = -float(score.tier1_struct_penalty + score.tier2_kin_penalty)
        if self.use_rm_shaping and self.use_omega_breach:
            reward += self.rm_shaping_weight * (rm_total - self._last_rm_reward)
            reward += self.potential_shaping_weight * (
                self.gamma * new_potential - self._last_potential
            )
        self._last_rm_reward = rm_total
        self._last_potential = new_potential

        struct_complete = (
            len(self.play.unmet_needs()) == 0
            and (score.tier1_struct_penalty + score.tier2_kin_penalty) == 0.0
        )
        terminal_reason: Optional[str] = None
        if self.use_omega_breach:
            if score.is_winning_play:
                reward += 50.0 - float(score.residual_cost)
                done = True
                terminated = True
                terminal_reason = "win"
                info["win"] = True
            elif struct_complete or (done and kind == "finalize"):
                reward -= 20.0 + 0.001 * float(score.total_cost_J)
                done = True
                terminated = True
                terminal_reason = "breach"
                info["breach"] = True
            elif self.moves_taken >= self.task.max_moves:
                done = True
                truncated = True
                terminal_reason = "max_moves"
                reward -= 10.0 + 0.001 * float(score.total_cost_J)
        else:
            if struct_complete:
                soft_t3 = 0.0 if score.is_winning_play else 0.5
                soft_cost = float(score.residual_cost * 8.0 + soft_t3)
                reward += 50.0 - soft_cost
                done = True
                terminated = True
                terminal_reason = "win" if score.is_winning_play else "soft_complete"
                info["win"] = score.is_winning_play
            elif self.moves_taken >= self.task.max_moves:
                done = True
                truncated = True
                terminal_reason = "max_moves"
                reward -= 10.0
            elif done and kind == "finalize":
                done = True
                terminated = True
                terminal_reason = "finalize"
                reward -= 10.0

        info["score"] = score
        info["n_legal"] = len(legal)
        info["terminal_reason"] = terminal_reason
        info["terminated"] = terminated
        info["truncated"] = truncated
        return StepResult(self.observe(score=score), reward, done, info)

    def _illegal_step(self, reason: str) -> StepResult:
        if self.raise_on_illegal:
            raise IllegalMoveError(reason)
        assert self.play is not None
        reward = -1.0 - self.step_penalty
        self.moves_taken += 1
        done = self.moves_taken >= self.task.max_moves
        info: Dict[str, Any] = {
            "illegal": reason,
            "terminal_reason": "max_moves" if done else None,
            "terminated": False,
            "truncated": done,
        }
        return StepResult(self.observe(), reward, done, info)

    def step(self, action_index: int) -> StepResult:
        assert self.play is not None
        legal = self.legal_moves()
        if not legal:
            return StepResult(
                self.observe(),
                -1.0,
                True,
                {
                    "error": "no_legal_moves",
                    "terminal_reason": "no_legal_moves",
                    "terminated": True,
                    "truncated": False,
                },
            )
        if action_index < 0 or action_index >= len(legal):
            return self._illegal_step(f"oob_action_index:{action_index}")
        kind, payload = legal[action_index]
        return self.step_move(kind, payload)


def _rebuild_integration_env(
    rebuild_fn: str, rebuild_kwargs: Dict[str, Any], init_kwargs: Dict[str, Any]
) -> IntegrationGameEnv:
    task = _rebuild_synth_task(rebuild_fn, rebuild_kwargs)
    return IntegrationGameEnv(task=task, **init_kwargs)
