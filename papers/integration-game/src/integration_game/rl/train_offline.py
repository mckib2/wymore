"""Simple linear softmax REINFORCE over legal-action features (masked)."""
from __future__ import annotations

import math
import random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from .baselines import EpisodeStats
from .env import IntegrationGameEnv, SynthTask, make_ping_pong_task


FEATURE_KEYS = (
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


@dataclass
class SoftmaxAgent:
    weights: Dict[str, float] = field(default_factory=dict)
    action_bias: Dict[str, float] = field(default_factory=dict)
    lr: float = 0.05

    def __post_init__(self) -> None:
        for k in FEATURE_KEYS:
            self.weights.setdefault(k, 0.0)
        for a in ("add", "connect", "finalize"):
            self.action_bias.setdefault(a, 0.0)

    def _score_action(self, obs: Dict[str, float], kind: str) -> float:
        s = self.action_bias.get(kind, 0.0)
        for k in FEATURE_KEYS:
            s += self.weights[k] * float(obs.get(k, 0.0)) * (0.1 if kind == "finalize" else 1.0)
        if kind == "connect":
            s += 0.5
        if kind == "add":
            s += 0.2
        return s

    def select(self, obs: Dict[str, float], legal: List[Tuple[str, object]], rng: random.Random) -> int:
        logits = [self._score_action(obs, kind) for kind, _ in legal]
        m = max(logits)
        exps = [math.exp(x - m) for x in logits]
        z = sum(exps) or 1.0
        probs = [e / z for e in exps]
        u = rng.random()
        acc = 0.0
        for i, p in enumerate(probs):
            acc += p
            if u <= acc:
                return i
        return len(legal) - 1

    def update(self, trajectory: List[Tuple[Dict[str, float], str, float]], gamma: float = 0.99) -> None:
        """REINFORCE with return-to-go; updates shared state weights + action bias."""
        if not trajectory:
            return
        returns: List[float] = []
        G = 0.0
        for _, _, r in reversed(trajectory):
            G = r + gamma * G
            returns.append(G)
        returns.reverse()
        baseline = sum(returns) / len(returns)
        for (obs, kind, _), G in zip(trajectory, returns):
            adv = G - baseline
            for k in FEATURE_KEYS:
                self.weights[k] += self.lr * adv * float(obs.get(k, 0.0)) * 1e-3
            self.action_bias[kind] = self.action_bias.get(kind, 0.0) + self.lr * adv * 0.01


def train_reinforce(
    task: SynthTask,
    n_episodes: int = 200,
    seed: int = 0,
) -> SoftmaxAgent:
    rng = random.Random(seed)
    env = IntegrationGameEnv(task)
    agent = SoftmaxAgent()
    for ep in range(n_episodes):
        obs = env.reset()
        traj: List[Tuple[Dict[str, float], str, float]] = []
        done = False
        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            idx = agent.select(obs, legal, rng)
            kind = legal[idx][0]
            step = env.step(idx)
            traj.append((obs, kind, step.reward))
            obs = step.obs
            done = step.done
        agent.update(traj)
    return agent


def evaluate_reinforce(
    task: SynthTask,
    agent: SoftmaxAgent,
    n_episodes: int = 30,
    seed: int = 1,
) -> Dict[str, float]:
    rng = random.Random(seed)
    env = IntegrationGameEnv(task)
    stats: List[EpisodeStats] = []
    for _ in range(n_episodes):
        obs = env.reset()
        total_r = 0.0
        done = False
        info: dict = {}
        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            idx = agent.select(obs, legal, rng)
            step = env.step(idx)
            total_r += step.reward
            obs = step.obs
            done = step.done
            info = step.info
        score = info.get("score")
        win = bool(info.get("win")) or (score is not None and score.is_winning_play)
        stats.append(
            EpisodeStats(
                win,
                total_r,
                env.moves_taken,
                float(score.residual_cost) if score is not None else 1e9,
                float(score.fitness_score_S) if score is not None else 0.0,
            )
        )
    wins = [s for s in stats if s.win]
    return {
        "win_rate": 100.0 * len(wins) / max(1, len(stats)),
        "mean_return": sum(s.return_sum for s in stats) / max(1, len(stats)),
        "mean_residual_win": (
            sum(s.residual for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_etfw": (sum(s.moves for s in wins) / len(wins) if wins else float("nan")),
        "mean_fitness": sum(s.fitness for s in stats) / max(1, len(stats)),
        "n_episodes": float(n_episodes),
    }


if __name__ == "__main__":
    task = make_ping_pong_task()
    agent = train_reinforce(task, n_episodes=150, seed=0)
    print(evaluate_reinforce(task, agent, n_episodes=20, seed=1))
