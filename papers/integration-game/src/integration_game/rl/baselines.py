"""Random, greedy, beam, and simple REINFORCE baselines for offline synthesis."""
from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .env import IntegrationGameEnv, SynthTask, make_ping_pong_task


@dataclass
class EpisodeStats:
    win: bool
    return_sum: float
    moves: int
    residual: float
    fitness: float


def run_episode(
    env: IntegrationGameEnv,
    policy: str = "random",
    beam_width: int = 4,
    rng: Optional[random.Random] = None,
) -> EpisodeStats:
    rng = rng or random.Random()
    obs = env.reset()
    total_r = 0.0
    done = False
    info: Dict[str, Any] = {}

    if policy == "beam":
        return _beam_search(env, beam_width=beam_width, rng=rng)
    if policy == "scripted":
        return _scripted_ping_pong(env)

    while not done:
        legal = env.legal_moves()
        if not legal:
            break
        if policy == "random":
            idx = rng.randrange(len(legal))
        elif policy == "greedy":
            idx = _greedy_index(env, legal)
        else:
            idx = rng.randrange(len(legal))
        step = env.step(idx)
        total_r += step.reward
        done = step.done
        info = step.info
        obs = step.obs

    score = info.get("score")
    win = bool(info.get("win")) or (score is not None and score.is_winning_play)
    residual = float(score.residual_cost) if score is not None else 1e9
    fitness = float(score.fitness_score_S) if score is not None else 0.0
    return EpisodeStats(win, total_r, env.moves_taken, residual, fitness)


def _scripted_ping_pong(env: IntegrationGameEnv) -> EpisodeStats:
    """Hand optimum sequence for the ping-pong synthesis catalog."""
    env.reset()
    total_r = 0.0
    script = [
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
    info: Dict[str, Any] = {}
    for kind, payload in script:
        legal = env.legal_moves()
        idx = None
        for i, (k, p) in enumerate(legal):
            if k == kind and p == payload:
                idx = i
                break
        if idx is None:
            # Fall back to any matching kind
            for i, (k, p) in enumerate(legal):
                if k == kind:
                    idx = i
                    break
        if idx is None:
            break
        step = env.step(idx)
        total_r += step.reward
        info = step.info
        if step.done:
            break
    score = info.get("score") or env._quick_score()
    return EpisodeStats(
        score.is_winning_play,
        total_r,
        env.moves_taken,
        score.residual_cost if score.is_winning_play else 1e9,
        score.fitness_score_S,
    )


def _greedy_index(env: IntegrationGameEnv, legal: List[Tuple[str, Any]]) -> int:
    """One-step lookahead minimizing tier1+tier2+small static, preferring finalize only if win."""
    best_i = 0
    best_key = None
    for i, (kind, payload) in enumerate(legal):
        # Clone via reset is expensive; use play.clone
        assert env.play is not None
        saved = env.play.clone()
        saved_used = set(env._catalog_used)
        saved_moves = env.moves_taken
        saved_rm = env._last_rm_reward
        step = env.step(i)
        score = step.info.get("score")
        if score is not None and score.is_winning_play:
            # restore not needed; caller ends
            env.play = saved
            env._catalog_used = saved_used
            env.moves_taken = saved_moves
            env._last_rm_reward = saved_rm
            return i
        key = (
            0 if kind != "finalize" else 1,
            float(score.tier1_struct_penalty + score.tier2_kin_penalty) if score else 1e9,
            float(score.static_cost) if score else 1e9,
            0 if kind == "connect" else 1,
        )
        env.play = saved
        env._catalog_used = saved_used
        env.moves_taken = saved_moves
        env._last_rm_reward = saved_rm
        if best_key is None or key < best_key:
            best_key = key
            best_i = i
    return best_i


def _beam_search(env: IntegrationGameEnv, beam_width: int = 4, rng: Optional[random.Random] = None) -> EpisodeStats:
    """Shallow beam over move sequences; evaluate leaves."""
    rng = rng or random.Random()
    env.reset()
    # State: (play_clone, catalog_used, moves, reward_sum)
    Beam = Tuple[Any, set, int, float]
    assert env.play is not None
    beam: List[Beam] = [(env.play.clone(), set(), 0, 0.0)]
    best_win: Optional[EpisodeStats] = None

    for depth in range(env.task.max_moves):
        candidates: List[Tuple[float, Beam, bool, Any]] = []
        for play, used, moves, ret in beam:
            env.play = play.clone()
            env._catalog_used = set(used)
            env.moves_taken = moves
            env._last_rm_reward = 0.0
            legal = env.legal_moves()
            if not legal:
                continue
            # Cap branching
            idxs = list(range(len(legal)))
            if len(idxs) > beam_width * 2:
                idxs = rng.sample(idxs, beam_width * 2)
            for i in idxs:
                env.play = play.clone()
                env._catalog_used = set(used)
                env.moves_taken = moves
                env._last_rm_reward = 0.0
                step = env.step(i)
                score = step.info.get("score")
                new_ret = ret + step.reward
                if score is not None and score.is_winning_play:
                    stats = EpisodeStats(True, new_ret, env.moves_taken, score.residual_cost, score.fitness_score_S)
                    if best_win is None or stats.residual < best_win.residual:
                        best_win = stats
                priority = -(
                    (score.fitness_score_S if score else 0.0)
                    - (score.tier1_struct_penalty + score.tier2_kin_penalty if score else 100)
                )
                candidates.append(
                    (
                        priority,
                        (env.play.clone(), set(env._catalog_used), env.moves_taken, new_ret),
                        step.done,
                        score,
                    )
                )
        if best_win is not None:
            return best_win
        if not candidates:
            break
        candidates.sort(key=lambda x: x[0])
        beam = [c[1] for c in candidates[:beam_width]]
        if all(c[2] for c in candidates[:beam_width]):
            break

    # Evaluate best remaining
    play, used, moves, ret = beam[0]
    env.play = play
    env._catalog_used = used
    env.moves_taken = moves
    score = env._quick_score()
    return EpisodeStats(
        score.is_winning_play,
        ret,
        moves,
        score.residual_cost if score.is_winning_play else 1e9,
        score.fitness_score_S,
    )


def evaluate_policy(
    task: SynthTask,
    policy: str,
    n_episodes: int = 20,
    seed: int = 0,
    beam_width: int = 4,
) -> Dict[str, float]:
    rng = random.Random(seed)
    env = IntegrationGameEnv(task)
    stats = [run_episode(env, policy=policy, beam_width=beam_width, rng=rng) for _ in range(n_episodes)]
    wins = [s for s in stats if s.win]
    return {
        "win_rate": 100.0 * len(wins) / max(1, len(stats)),
        "mean_return": sum(s.return_sum for s in stats) / max(1, len(stats)),
        "mean_residual_win": (
            sum(s.residual for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_etfw": (
            sum(s.moves for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_fitness": sum(s.fitness for s in stats) / max(1, len(stats)),
        "n_episodes": float(n_episodes),
    }
