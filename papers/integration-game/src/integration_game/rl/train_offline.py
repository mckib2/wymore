"""
Relational Policy-Gradient (Softmax REINFORCE) and Masked PPO (Actor-Critic)
agents for offline Integration Game board synthesis.
"""
from __future__ import annotations

import math
import random
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .baselines import EpisodeStats
from .env import (
    ACTION_FEATURE_KEYS,
    IntegrationGameEnv,
    SynthTask,
    make_ping_pong_task,
)

STATE_FEATURE_KEYS: Tuple[str, ...] = (
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

STATE_SCALES: Dict[str, float] = {
    "n_unmet": 5.0,
    "tier1": 50.0,
    "tier2": 20.0,
    "tier3": 10000.0,
    "static": 5.0,
    "S": 100.0,
    "rm_state": 5.0,
    "moves": 15.0,
    "n_components": 10.0,
    "n_routes": 10.0,
    "cut": 1.0,
    "breaches": 5.0,
}


def _softmax(logits: Sequence[float]) -> List[float]:
    if not logits:
        return []
    m = max(logits)
    exps = [math.exp(max(-30.0, min(30.0, x - m))) for x in logits]
    z = sum(exps) or 1.0
    return [e / z for e in exps]


def _sample_categorical(probs: Sequence[float], rng: random.Random) -> int:
    u = rng.random()
    acc = 0.0
    for i, p in enumerate(probs):
        acc += p
        if u <= acc:
            return i
    return max(0, len(probs) - 1)


@dataclass
class TrainingHistory:
    episode_returns: List[float] = field(default_factory=list)
    episode_wins: List[int] = field(default_factory=list)
    episode_fitness: List[float] = field(default_factory=list)
    first_win_episode: int = 0


@dataclass
class SoftmaxAgent:
    """
    Relational Softmax REINFORCE policy over legal actions.
    Uses exact score-function gradient: grad log pi(a|s) = phi(s,a) - E_{a'~pi}[phi(s,a')].
    """
    rel_weights: Dict[str, float] = field(default_factory=dict)
    action_prefs: Dict[str, float] = field(default_factory=dict)
    action_bias: Dict[str, float] = field(default_factory=dict)
    lr: float = 0.08
    first_win_episode: int = 0

    def __post_init__(self) -> None:
        # Mild ontology-informed prior on relational features
        defaults = {
            "is_add": 0.1,
            "is_connect": 0.4,
            "is_finalize": -0.5,
            "input_live_match": 0.8,
            "need_progress": 0.8,
            "completes_chain": 1.0,
            "op_cost_norm": 0.2,
            "chain_ready_to_connect": 0.6,
            "finalize_ready": 1.5,
        }
        for k in ACTION_FEATURE_KEYS:
            self.rel_weights.setdefault(k, defaults.get(k, 0.0))
        for a in ("add", "connect", "finalize"):
            self.action_bias.setdefault(a, 0.0)

    def _logit(
        self,
        feats: Dict[str, float],
        sig: str,
        kind: str,
        use_task_prefs: bool = True,
    ) -> float:
        score = self.action_bias.get(kind, 0.0)
        for k in ACTION_FEATURE_KEYS:
            score += self.rel_weights.get(k, 0.0) * float(feats.get(k, 0.0))
        if use_task_prefs:
            score += self.action_prefs.get(sig, 0.0)
        return score

    def action_distribution(
        self,
        env: IntegrationGameEnv,
        legal: List[Tuple[str, Any]],
        use_task_prefs: bool = True,
    ) -> Tuple[List[float], List[Dict[str, float]], List[str]]:
        feats_list = [env.action_features(k, p) for k, p in legal]
        sigs = [env.action_signature(k, p) for k, p in legal]
        logits = [
            self._logit(f, s, k, use_task_prefs=use_task_prefs)
            for f, s, (k, _) in zip(feats_list, sigs, legal)
        ]
        return _softmax(logits), feats_list, sigs

    def select(
        self,
        env: IntegrationGameEnv,
        legal: List[Tuple[str, Any]],
        rng: random.Random,
        greedy: bool = False,
        use_task_prefs: bool = True,
    ) -> int:
        probs, _, _ = self.action_distribution(env, legal, use_task_prefs=use_task_prefs)
        if greedy:
            return max(range(len(probs)), key=lambda i: probs[i])
        return _sample_categorical(probs, rng)

    def update(
        self,
        trajectory: List[
            Tuple[
                List[Dict[str, float]],
                List[str],
                List[str],
                List[float],
                int,
                float,
            ]
        ],
        gamma: float = 0.99,
    ) -> None:
        """Exact log-softmax REINFORCE update with return-to-go baseline."""
        if not trajectory:
            return
        returns: List[float] = []
        G = 0.0
        for *_, r in reversed(trajectory):
            G = r + gamma * G
            returns.append(G)
        returns.reverse()
        # Use fixed reference baseline 0.0 so winning trajectories (G > 0) always receive
        # positive advantage across all steps and trap/losing trajectories (G < 0) receive negative advantage
        scale = 40.0

        for (feats_list, sigs, kinds, probs, chosen_idx, _), G in zip(trajectory, returns):
            adv = max(-3.0, min(3.0, G / scale))
            # Expected relational features under current policy pi(.|s)
            for k in ACTION_FEATURE_KEYS:
                expected_f = sum(p * float(f.get(k, 0.0)) for p, f in zip(probs, feats_list))
                grad_f = float(feats_list[chosen_idx].get(k, 0.0)) - expected_f
                self.rel_weights[k] += self.lr * 0.25 * adv * grad_f

            # Per-action signature & kind bias gradients: (1[j == chosen] - probs[j])
            for j, (sig, kind, p) in enumerate(zip(sigs, kinds, probs)):
                indicator = 1.0 if j == chosen_idx else 0.0
                grad_logit = indicator - p
                self.action_prefs[sig] = self.action_prefs.get(sig, 0.0) + (
                    self.lr * 2.0 * adv * grad_logit
                )
                self.action_bias[kind] = self.action_bias.get(kind, 0.0) + (
                    self.lr * 0.1 * adv * grad_logit
                )


@dataclass
class MaskedPPOAgent:
    """
    Masked Proximal Policy Optimization (PPO) Actor-Critic over relational graph-action features.
    Combines shared ontology-relational weights (for cross-task generalization) with
    task-scoped operator signature logits (for Tier-3 trap disambiguation) and a linear value critic.
    """
    rel_weights: Dict[str, float] = field(default_factory=dict)
    action_prefs: Dict[str, float] = field(default_factory=dict)
    critic_weights: Dict[str, float] = field(default_factory=dict)
    critic_bias: float = 0.0
    actor_lr: float = 0.12
    critic_lr: float = 0.08
    clip_eps: float = 0.2
    ppo_epochs: int = 4
    entropy_coef: float = 0.01
    first_win_episode: int = 0
    history: TrainingHistory = field(default_factory=TrainingHistory)

    def __post_init__(self) -> None:
        defaults = {
            "is_add": 0.2,
            "is_connect": 0.6,
            "is_finalize": -0.6,
            "input_live_match": 1.2,
            "need_progress": 1.2,
            "completes_chain": 1.4,
            "op_cost_norm": 1.8,
            "chain_ready_to_connect": 0.9,
            "finalize_ready": 2.0,
        }
        for k in ACTION_FEATURE_KEYS:
            self.rel_weights.setdefault(k, defaults.get(k, 0.0))
        for k in STATE_FEATURE_KEYS:
            self.critic_weights.setdefault(k, 0.0)

    def value(self, obs: Dict[str, float]) -> float:
        v = self.critic_bias
        for k in STATE_FEATURE_KEYS:
            v += self.critic_weights.get(k, 0.0) * (float(obs.get(k, 0.0)) / STATE_SCALES[k])
        return v

    def _compute_logits(
        self,
        feats_list: List[Dict[str, float]],
        sigs: List[str],
        use_task_prefs: bool = True,
    ) -> List[float]:
        logits: List[float] = []
        for f, s in zip(feats_list, sigs):
            val = 0.0
            for k in ACTION_FEATURE_KEYS:
                val += self.rel_weights.get(k, 0.0) * float(f.get(k, 0.0))
            if use_task_prefs:
                val += self.action_prefs.get(s, 0.0)
            logits.append(val)
        return logits

    def select(
        self,
        env: IntegrationGameEnv,
        legal: List[Tuple[str, Any]],
        rng: random.Random,
        greedy: bool = False,
        use_task_prefs: bool = True,
    ) -> Tuple[int, float, List[Dict[str, float]], List[str]]:
        feats_list = [env.action_features(k, p) for k, p in legal]
        sigs = [env.action_signature(k, p) for k, p in legal]
        logits = self._compute_logits(feats_list, sigs, use_task_prefs=use_task_prefs)
        probs = _softmax(logits)
        if greedy:
            idx = max(range(len(probs)), key=lambda i: probs[i])
        else:
            idx = _sample_categorical(probs, rng)
        return idx, probs[idx], feats_list, sigs

    def update_ppo(
        self,
        batch: List[
            Tuple[
                Dict[str, float],
                List[Dict[str, float]],
                List[str],
                int,
                float,
                float,
            ]
        ],
        update_relational: bool = True,
    ) -> None:
        """Run K epochs of clipped PPO actor + MSE value critic updates on a rollout trajectory."""
        if not batch:
            return
        values = [self.value(obs) for obs, *_ in batch]
        returns = [ret for *_, ret in batch]
        # Scale advantages by 40.0 without per-episode mean subtraction so that
        # all steps of a winning episode (G > V) receive positive advantage and
        # all steps of a Tier-3 breach episode (G < V) receive negative advantage.
        norm_advs = [max(-3.0, min(3.0, (ret - 0.5 * val) / 40.0)) for ret, val in zip(returns, values)]

        for _ in range(self.ppo_epochs):
            for (obs, feats_list, sigs, chosen_idx, old_prob, ret), adv in zip(batch, norm_advs):
                logits = self._compute_logits(feats_list, sigs, use_task_prefs=True)
                probs = _softmax(logits)
                new_prob = max(1e-8, probs[chosen_idx])
                ratio = new_prob / max(1e-8, old_prob)

                # Check PPO clipping condition
                clipped = (adv > 0 and ratio > 1.0 + self.clip_eps) or (
                    adv < 0 and ratio < 1.0 - self.clip_eps
                )
                effective_weight = 0.0 if clipped else (ratio * adv)

                # Actor update (shared relational weights + task signature preference)
                if update_relational:
                    for k in ACTION_FEATURE_KEYS:
                        exp_f = sum(p * float(f.get(k, 0.0)) for p, f in zip(probs, feats_list))
                        grad_log_pi = float(feats_list[chosen_idx].get(k, 0.0)) - exp_f
                        self.rel_weights[k] += self.actor_lr * 0.25 * effective_weight * grad_log_pi

                for j, (sig, p) in enumerate(zip(sigs, probs)):
                    ind = 1.0 if j == chosen_idx else 0.0
                    grad_logit = ind - p
                    ent_grad = -p * (math.log(max(1e-8, p)) + 1.0)
                    self.action_prefs[sig] = self.action_prefs.get(sig, 0.0) + self.actor_lr * (
                        2.5 * effective_weight * grad_logit + self.entropy_coef * ent_grad
                    )

                # Critic update
                v_pred = self.value(obs)
                v_err = max(-10.0, min(10.0, (ret / 40.0) - v_pred))
                self.critic_bias += self.critic_lr * 0.05 * v_err
                for k in STATE_FEATURE_KEYS:
                    x_k = float(obs.get(k, 0.0)) / STATE_SCALES[k]
                    self.critic_weights[k] += self.critic_lr * 0.05 * v_err * x_k


def train_reinforce(
    task: SynthTask,
    n_episodes: int = 200,
    seed: int = 0,
    use_rm_shaping: bool = True,
    use_omega_breach: bool = True,
) -> SoftmaxAgent:
    rng = random.Random(seed)
    env = IntegrationGameEnv(
        task, use_rm_shaping=use_rm_shaping, use_omega_breach=use_omega_breach
    )
    agent = SoftmaxAgent()
    first_win = n_episodes

    for ep in range(n_episodes):
        env.reset()
        traj = []
        done = False
        info: Dict[str, Any] = {}
        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            probs, feats_list, sigs = agent.action_distribution(env, legal)
            idx = _sample_categorical(probs, rng)
            kinds = [k for k, _ in legal]
            step = env.step(idx)
            traj.append((feats_list, sigs, kinds, probs, idx, step.reward))
            done = step.done
            info = step.info

        score = info.get("score")
        win = bool(info.get("win")) or bool(score and score.is_winning_play)
        if win and first_win == n_episodes:
            first_win = ep + 1
        agent.update(traj)

    agent.first_win_episode = first_win
    return agent


def evaluate_reinforce(
    task: SynthTask,
    agent: SoftmaxAgent,
    n_episodes: int = 30,
    seed: int = 1,
    greedy: bool = False,
) -> Dict[str, float]:
    rng = random.Random(seed)
    env = IntegrationGameEnv(task)
    stats: List[EpisodeStats] = []
    for _ in range(n_episodes):
        env.reset()
        total_r = 0.0
        done = False
        info: dict = {}
        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            idx = agent.select(env, legal, rng, greedy=greedy)
            step = env.step(idx)
            total_r += step.reward
            done = step.done
            info = step.info
        score = info.get("score") or env._quick_score()
        win = bool(info.get("win")) or bool(score and score.is_winning_play)
        stats.append(
            EpisodeStats(
                win,
                total_r,
                env.moves_taken,
                float(score.residual_cost) if (score is not None and win) else 1e9,
                float(score.fitness_score_S) if score is not None else 0.0,
            )
        )
    wins = [s for s in stats if s.win]
    etfw = float(agent.first_win_episode) if agent.first_win_episode > 0 else (
        float(next((i + 1 for i, s in enumerate(stats) if s.win), n_episodes))
    )
    return {
        "win_rate": 100.0 * len(wins) / max(1, len(stats)),
        "mean_return": sum(s.return_sum for s in stats) / max(1, len(stats)),
        "mean_residual_win": (
            sum(s.residual for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_etfw": etfw,
        "mean_moves_win": (
            sum(s.moves for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_fitness": sum(s.fitness for s in stats) / max(1, len(stats)),
        "n_episodes": float(n_episodes),
    }


def train_masked_ppo(
    task: SynthTask,
    n_episodes: int = 120,
    seed: int = 0,
    gamma: float = 0.99,
    use_rm_shaping: bool = True,
    use_omega_breach: bool = True,
    initial_agent: Optional[MaskedPPOAgent] = None,
) -> MaskedPPOAgent:
    """Train MaskedPPOAgent on a synthesis task and record learning curve history."""
    rng = random.Random(seed)
    env = IntegrationGameEnv(
        task,
        gamma=gamma,
        use_rm_shaping=use_rm_shaping,
        use_omega_breach=use_omega_breach,
    )
    agent = initial_agent or MaskedPPOAgent()
    first_win = n_episodes

    for ep in range(n_episodes):
        obs = env.reset()
        traj_raw: List[
            Tuple[Dict[str, float], List[Dict[str, float]], List[str], int, float, float]
        ] = []
        done = False
        ep_ret = 0.0
        info: Dict[str, Any] = {}

        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            idx, prob, feats_list, sigs = agent.select(env, legal, rng, greedy=False)
            step = env.step(idx)
            traj_raw.append((obs, feats_list, sigs, idx, prob, step.reward))
            ep_ret += step.reward
            obs = step.obs
            done = step.done
            info = step.info

        # Compute discounted returns-to-go
        batch = []
        G = 0.0
        for o, fl, sg, idx, pr, r in reversed(traj_raw):
            G = r + gamma * G
            batch.append((o, fl, sg, idx, pr, G))
        batch.reverse()

        score = info.get("score") or env._quick_score()
        win = bool(info.get("win")) or bool(score and score.is_winning_play)
        if win and first_win == n_episodes:
            first_win = ep + 1

        agent.history.episode_returns.append(ep_ret)
        agent.history.episode_wins.append(1 if win else 0)
        agent.history.episode_fitness.append(float(score.fitness_score_S) if score else 0.0)
        agent.update_ppo(batch)

    agent.first_win_episode = first_win
    agent.history.first_win_episode = first_win
    return agent


def train_multitask_ppo(
    tasks: Sequence[SynthTask],
    episodes_per_task: int = 80,
    seed: int = 0,
) -> MaskedPPOAgent:
    """Train a shared MaskedPPOAgent across multiple synthesis tasks (ex02..ex07)."""
    agent = MaskedPPOAgent()
    for idx, t in enumerate(tasks):
        train_masked_ppo(
            t,
            n_episodes=episodes_per_task,
            seed=seed + idx * 17,
            initial_agent=agent,
        )
    return agent


def evaluate_masked_ppo(
    task: SynthTask,
    agent: MaskedPPOAgent,
    n_episodes: int = 30,
    seed: int = 1,
    greedy: bool = False,
    use_task_prefs: bool = True,
) -> Dict[str, float]:
    rng = random.Random(seed)
    env = IntegrationGameEnv(task)
    stats: List[EpisodeStats] = []
    for _ in range(n_episodes):
        env.reset()
        total_r = 0.0
        done = False
        info: dict = {}
        while not done:
            legal = env.legal_moves()
            if not legal:
                break
            idx, _, _, _ = agent.select(
                env, legal, rng, greedy=greedy, use_task_prefs=use_task_prefs
            )
            step = env.step(idx)
            total_r += step.reward
            done = step.done
            info = step.info
        score = info.get("score") or env._quick_score()
        win = bool(info.get("win")) or bool(score and score.is_winning_play)
        stats.append(
            EpisodeStats(
                win,
                total_r,
                env.moves_taken,
                float(score.residual_cost) if (score is not None and win) else 1e9,
                float(score.fitness_score_S) if score is not None else 0.0,
            )
        )
    wins = [s for s in stats if s.win]
    etfw = float(agent.first_win_episode) if agent.first_win_episode > 0 else (
        float(next((i + 1 for i, s in enumerate(stats) if s.win), n_episodes))
    )
    return {
        "win_rate": 100.0 * len(wins) / max(1, len(stats)),
        "mean_return": sum(s.return_sum for s in stats) / max(1, len(stats)),
        "mean_residual_win": (
            sum(s.residual for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_etfw": etfw,
        "mean_moves_win": (
            sum(s.moves for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_fitness": sum(s.fitness for s in stats) / max(1, len(stats)),
        "n_episodes": float(n_episodes),
    }


if __name__ == "__main__":
    task = make_ping_pong_task()
    ppo = train_masked_ppo(task, n_episodes=100, seed=0)
    print("Masked PPO:", evaluate_masked_ppo(task, ppo, n_episodes=20, seed=1))
