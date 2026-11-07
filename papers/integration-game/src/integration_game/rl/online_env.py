"""
Online RL Adaptive Mediation Environment (Section 3.4 / Table tab:online-rl).
Models runtime control of fixed mediation topologies (e.g., Ex12 primary/backup
failover MuxSwitchBlock under stochastic link dropout bursts) with uLSC Reward Machine feedback.
"""
from __future__ import annotations

import json
import math
import random
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from integration_game.board import Board
from integration_game.components import (
    ConsumerBoundary,
    MuxSwitchBlock,
    ProducerBoundary,
    RecolorBlock,
    RepresentationBridgeBlock,
)
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
from integration_game.ulsc import RMState, UniversalLSC


@dataclass
class OnlineEpisodeMetrics:
    tier3_satisfied: bool
    breaches: int
    recovery_ticks: float
    total_return: float
    backup_usage_ratio: float


class OnlineMediationEnv:
    """
    Tick-by-tick online flow-control MDP over the Ex12 primary/backup failover board.
    At each tick t in [0, horizon), the agent observes link telemetry availability,
    consecutive primary dropouts, current mux channel, and Reward Machine state,
    and selects mux active_index in {0 (Primary LOS), 1 (Backup SATCOM)}.
    """

    def __init__(
        self,
        horizon: int = 16,
        backup_step_cost: float = 0.15,
        switch_cost: float = 0.05,
        breach_penalty: float = 15.0,
        fulfill_reward: float = 2.0,
    ):
        self.horizon = horizon
        self.backup_step_cost = backup_step_cost
        self.switch_cost = switch_cost
        self.breach_penalty = breach_penalty
        self.fulfill_reward = fulfill_reward

        self.c_si = Color("Nav.Velocity", "m_per_s", "float64")
        self.c_kt = Color("Nav.Velocity", "knots", "float64")

        self.board: Optional[Board] = None
        self.mux: Optional[MuxSwitchBlock] = None
        self.tick = 0
        self.consecutive_drops = 0
        self.current_idx = 0
        self.dropout_ticks: set = set()
        self.breaches = 0
        self.recovery_ticks_list: List[int] = []
        self._in_outage = False
        self._outage_ticks_unserved = 0

    def _build_board(self) -> Tuple[Board, MuxSwitchBlock]:
        b = Board("Online_Ex12_Failover")
        b.add_component(ProducerBoundary("PrimaryLOS", "out", self.c_si, mode=TransferMode.PUSH))
        b.add_component(
            ProducerBoundary(
                "BackupSAT",
                "out",
                self.c_kt,
                mode=TransferMode.PUSH,
                rep=Representation.BYTE_BLOB_JSON,
            )
        )
        b.add_component(
            ConsumerBoundary("FlightCtrl", "in", MessageShape.single(self.c_si), mode=TransferMode.PUSH)
        )
        b.add_component(
            RepresentationBridgeBlock(
                "SAT_JSON2Nat",
                self.c_kt,
                Representation.BYTE_BLOB_JSON,
                Representation.NATIVE_STRUCT,
                decode_fn=lambda s: float(json.loads(s)["v_kt"]),
            )
        )
        b.add_component(
            RecolorBlock(
                "SAT_Kt2MS",
                self.c_kt,
                self.c_si,
                value_fn=lambda kt: round(float(kt) * 0.514444, 4),
            )
        )
        mux = MuxSwitchBlock("FailoverMux", self.c_si, n_inputs=2, active_index=0)
        b.add_component(mux)

        b.connect("PrimaryLOS.out", "FailoverMux.in_0")
        b.connect("BackupSAT.out", "SAT_JSON2Nat.in")
        b.connect("SAT_JSON2Nat.out", "SAT_Kt2MS.in")
        b.connect("SAT_Kt2MS.out", "FailoverMux.in_1")
        b.connect("FailoverMux.out", "FlightCtrl.in")
        return b, mux

    def reset(
        self,
        rng: Optional[random.Random] = None,
        dropout_window: Optional[Tuple[int, int]] = None,
    ) -> Dict[str, float]:
        rng = rng or random.Random()
        self.board, self.mux = self._build_board()
        for comp in self.board.components.values():
            comp.reset()
        self.tick = 0
        self.consecutive_drops = 0
        self.current_idx = 0
        self.breaches = 0
        self.recovery_ticks_list = []
        self._in_outage = False
        self._outage_ticks_unserved = 0

        if dropout_window is not None:
            start, end = dropout_window
            self.dropout_ticks = set(range(start, end))
        else:
            start = rng.randint(3, 6)
            length = rng.randint(4, 6)
            self.dropout_ticks = set(range(start, min(self.horizon - 2, start + length)))

        return self._observe()

    def _observe(self) -> Dict[str, float]:
        primary_ok = 0.0 if self.tick in self.dropout_ticks else 1.0
        if primary_ok == 0.0:
            next_drops = float(self.consecutive_drops + 1)
        else:
            next_drops = 0.0
        return {
            "primary_ok": primary_ok,
            "consecutive_drops": min(5.0, next_drops) / 5.0,
            "current_idx": float(self.current_idx),
            "breached": 1.0 if self.breaches > 0 else 0.0,
        }

    def step(self, action_idx: int) -> Tuple[Dict[str, float], float, bool, Dict[str, Any]]:
        assert self.board is not None and self.mux is not None
        action_idx = 1 if int(action_idx) == 1 else 0
        switched = action_idx != self.current_idx
        self.current_idx = action_idx
        self.mux.set_active(action_idx)

        t = self.tick
        true_v_ms = 100.0 + 2.0 * t
        true_v_kt = true_v_ms / 0.514444

        env_t: Dict[str, Message] = {
            "BackupSAT.out": Message.single(
                Field(
                    json.dumps({"v_kt": true_v_kt}),
                    self.c_kt,
                    Dynamics("BackupSAT.out", 1.0),
                    representation=Representation.BYTE_BLOB_JSON,
                    provenance=Provenance(("BackupSAT",), timestamp_tick=t),
                )
            )
        }
        primary_alive = t not in self.dropout_ticks
        if primary_alive:
            self.consecutive_drops = 0
            env_t["PrimaryLOS.out"] = Message.single(
                Field(
                    true_v_ms,
                    self.c_si,
                    Dynamics("PrimaryLOS.out", 1.0),
                    provenance=Provenance(("PrimaryLOS",), timestamp_tick=t),
                )
            )
        else:
            self.consecutive_drops += 1

        # Execute 1 tick on the coupled board
        for p in self.board.producers:
            p.step(t, env_t)
            self.board._propagate_push_from(p.comp_id, t)
        for blk in self.board.interior_blocks:
            blk.step(t, env_t)
            self.board._propagate_push_from(blk.comp_id, t)
        for c in self.board.consumers:
            c.step(t, env_t)

        sink = self.board.components["FlightCtrl"]
        assert isinstance(sink, ConsumerBoundary)
        rec_hist = sink.state.get("received_history", {})
        delivered = t in rec_hist and abs(
            float(rec_hist[t].first_field().value) - true_v_ms
        ) <= 0.1

        # Track outage recovery latency
        if not primary_alive:
            if not self._in_outage:
                self._in_outage = True
                self._outage_ticks_unserved = 0
            if not delivered:
                self._outage_ticks_unserved += 1
            elif self._outage_ticks_unserved >= 0 and len(self.recovery_ticks_list) == 0:
                self.recovery_ticks_list.append(self._outage_ticks_unserved)
        else:
            if self._in_outage and len(self.recovery_ticks_list) == 0:
                self.recovery_ticks_list.append(self._outage_ticks_unserved)
            self._in_outage = False

        reward = 0.0
        if delivered:
            reward += self.fulfill_reward
        else:
            self.breaches += 1
            reward -= self.breach_penalty

        if action_idx == 1:
            reward -= self.backup_step_cost
        if switched:
            reward -= self.switch_cost

        self.tick += 1
        done = self.tick >= self.horizon
        if done and self._in_outage and len(self.recovery_ticks_list) == 0:
            self.recovery_ticks_list.append(self._outage_ticks_unserved)

        obs_next = self._observe() if not done else {
            "primary_ok": 1.0,
            "consecutive_drops": 0.0,
            "current_idx": float(self.current_idx),
            "breached": 1.0 if self.breaches > 0 else 0.0,
        }
        return obs_next, reward, done, {"delivered": delivered, "breaches": self.breaches}


@dataclass
class OnlinePPOController:
    """Contextual Actor-Critic policy for online mux failover control."""
    w0: Dict[str, float] = field(
        default_factory=lambda: {
            "primary_ok": 0.5,
            "primary_down": -0.5,
            "consecutive_drops": 0.0,
            "current_idx": 0.0,
            "bias": 0.2,
        }
    )
    w1: Dict[str, float] = field(
        default_factory=lambda: {
            "primary_ok": -0.5,
            "primary_down": 0.5,
            "consecutive_drops": 0.0,
            "current_idx": 0.0,
            "bias": -0.2,
        }
    )
    lr: float = 0.20

    def _features(self, obs: Dict[str, float]) -> Dict[str, float]:
        p_ok = float(obs["primary_ok"])
        return {
            "primary_ok": p_ok,
            "primary_down": 1.0 - p_ok,
            "consecutive_drops": float(obs["consecutive_drops"]),
            "current_idx": float(obs["current_idx"]),
            "bias": 1.0,
        }

    def probs(self, obs: Dict[str, float]) -> Tuple[float, float]:
        x = self._features(obs)
        z0 = sum(self.w0[k] * x[k] for k in x)
        z1 = sum(self.w1[k] * x[k] for k in x)
        m = max(z0, z1)
        e0, e1 = math.exp(z0 - m), math.exp(z1 - m)
        s = e0 + e1
        return e0 / s, e1 / s

    def act(self, obs: Dict[str, float], rng: random.Random, greedy: bool = False) -> int:
        p0, p1 = self.probs(obs)
        if greedy:
            return 1 if p1 >= p0 else 0
        return 1 if rng.random() < p1 else 0

    def update(self, traj: List[Tuple[Dict[str, float], int, float]], gamma: float = 0.5) -> None:
        returns: List[float] = []
        G = 0.0
        for _, _, r in reversed(traj):
            G = r + gamma * G
            returns.append(G)
        returns.reverse()
        mean_g = sum(returns) / max(1, len(returns))
        std_g = math.sqrt(sum((g - mean_g) ** 2 for g in returns) / max(1, len(returns))) + 1e-5

        for (obs, a, r_step), G in zip(traj, returns):
            # Combine immediate step reward and return-to-go for low-variance per-tick credit assignment
            adv = 0.5 * r_step + 0.5 * ((G - mean_g) / std_g)
            p0, p1 = self.probs(obs)
            x = self._features(obs)
            grad0 = (1.0 if a == 0 else 0.0) - p0
            grad1 = (1.0 if a == 1 else 0.0) - p1
            for k in x:
                self.w0[k] += self.lr * adv * grad0 * x[k]
                self.w1[k] += self.lr * adv * grad1 * x[k]


def train_online_controller(n_episodes: int = 80, seed: int = 0) -> OnlinePPOController:
    rng = random.Random(seed)
    env = OnlineMediationEnv()
    ctrl = OnlinePPOController()
    for _ in range(n_episodes):
        obs = env.reset(rng=rng)
        traj = []
        done = False
        while not done:
            a = ctrl.act(obs, rng, greedy=False)
            next_obs, r, done, _ = env.step(a)
            traj.append((obs, a, r))
            obs = next_obs
        ctrl.update(traj)
    return ctrl


def evaluate_online_controller(
    mode: str,
    controller: Optional[OnlinePPOController] = None,
    n_episodes: int = 30,
    seed: int = 42,
) -> Dict[str, float]:
    """
    Evaluate an online controller mode in {'static_primary', 'scripted_threshold', 'online_ppo'}.
    """
    rng = random.Random(seed)
    env = OnlineMediationEnv()
    metrics: List[OnlineEpisodeMetrics] = []

    for _ in range(n_episodes):
        obs = env.reset(rng=rng)
        done = False
        total_r = 0.0
        backup_steps = 0
        prev_drops = 0

        while not done:
            if mode == "static_primary":
                a = 0
            elif mode == "scripted_threshold":
                # Reactive timeout: switches only after observing >= 1 prior dropped tick
                a = 1 if prev_drops >= 1 else 0
            elif mode == "online_ppo":
                assert controller is not None
                a = controller.act(obs, rng, greedy=True)
            else:
                raise ValueError(f"Unknown online mode: {mode}")

            prev_drops = env.consecutive_drops + (0 if obs["primary_ok"] == 1.0 else 1)
            if a == 1:
                backup_steps += 1
            obs, r, done, _ = env.step(a)
            total_r += r

        rec = float(env.recovery_ticks_list[0]) if env.recovery_ticks_list else 0.0
        metrics.append(
            OnlineEpisodeMetrics(
                tier3_satisfied=(env.breaches == 0),
                breaches=env.breaches,
                recovery_ticks=rec,
                total_return=total_r,
                backup_usage_ratio=backup_steps / float(env.horizon),
            )
        )

    return {
        "recovery_ticks": sum(m.recovery_ticks for m in metrics) / len(metrics),
        "mean_breaches": sum(m.breaches for m in metrics) / len(metrics),
        "tier3_sat_pct": 100.0 * sum(1 for m in metrics if m.tier3_satisfied) / len(metrics),
        "mean_return": sum(m.total_return for m in metrics) / len(metrics),
        "backup_usage_pct": 100.0 * sum(m.backup_usage_ratio for m in metrics) / len(metrics),
    }
