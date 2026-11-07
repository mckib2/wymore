"""Random, greedy, beam, and scripted baselines for offline board synthesis."""
from __future__ import annotations

import random
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

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
    env.reset()
    total_r = 0.0
    done = False
    info: Dict[str, Any] = {}

    if policy == "beam":
        return _beam_search(env, beam_width=beam_width, rng=rng)
    if policy == "scripted":
        return _scripted_episode(env)

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

    score = info.get("score") or env._quick_score()
    win = bool(info.get("win")) or bool(score and score.is_winning_play)
    residual = float(score.residual_cost) if (score is not None and win) else 1e9
    fitness = float(score.fitness_score_S) if score is not None else 0.0
    return EpisodeStats(win, total_r, env.moves_taken, residual, fitness)


def _scripted_episode(env: IntegrationGameEnv) -> EpisodeStats:
    """Execute the task's reference scripted move sequence."""
    env.reset()
    total_r = 0.0
    script = env.task.scripted_moves or [
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
    """
    One-step Tier-1/Tier-2 + static-cost myopic lookahead.
    Minimizes structural/kinematic penalty and static cost without Tier-3 oracle lookahead
    on intermediate operator placement steps.
    """
    best_i = 0
    best_key = None
    assert env.play is not None
    unmet_before = len(env.play.unmet_needs())

    for i, (kind, payload) in enumerate(legal):
        feats = env.action_features(kind, payload)
        saved_play = env.play.clone()
        saved_used = set(env._catalog_used)
        saved_moves = env.moves_taken
        saved_rm = env._last_rm_reward
        saved_pot = env._last_potential

        step = env.step(i)
        score = step.info.get("score")
        unmet_after = len(env.play.unmet_needs())

        env.play = saved_play
        env._catalog_used = saved_used
        env.moves_taken = saved_moves
        env._last_rm_reward = saved_rm
        env._last_potential = saved_pot

        if kind == "finalize":
            # Only finalize when all boundary needs are wired
            if unmet_before == 0:
                return i
            key = (2, 1e9, 1e9, 0.0, 1e9)
        elif kind == "connect":
            # Prefer connecting live offers that reduce Tier-1/Tier-2 penalties
            t12 = float(score.tier1_struct_penalty + score.tier2_kin_penalty) if score else 1e9
            key = (
                0 if feats["input_live_match"] > 0 else 1,
                unmet_after,
                t12,
                -feats["need_progress"],
                float(score.static_cost) if score else 1e9,
            )
        else:
            # Adding an operator: prefer operators whose inputs match live offers
            # and that minimize static_cost (which makes Greedy susceptible to cheaper Tier-3 traps!)
            t12 = float(score.tier1_struct_penalty + score.tier2_kin_penalty) if score else 1e9
            key = (
                0 if feats["input_live_match"] >= 1.0 else 1,
                unmet_after,
                t12,
                -round(feats["need_progress"], 3),
                float(score.static_cost) if score else 1e9,
            )

        if best_key is None or key < best_key:
            best_key = key
            best_i = i
    return best_i


def _beam_search(
    env: IntegrationGameEnv,
    beam_width: int = 4,
    rng: Optional[random.Random] = None,
) -> EpisodeStats:
    """
    Bounded-width beam search over legal move sequences.
    Preserves exact MDP shaping state (last_rm_reward, last_potential) per beam node
    and never expands terminal/finalized leaves.
    """
    rng = rng or random.Random()
    env.reset()
    assert env.play is not None

    # Beam tuple: (play_clone, catalog_used, moves, last_rm, last_pot, return_sum, done, last_score)
    BeamNode = Tuple[Any, set, int, float, float, float, bool, Optional[Any]]
    beam: List[BeamNode] = [
        (
            env.play.clone(),
            set(env._catalog_used),
            env.moves_taken,
            env._last_rm_reward,
            env._last_potential,
            0.0,
            False,
            env._quick_score(),
        )
    ]
    best_win: Optional[EpisodeStats] = None

    for _depth in range(env.task.max_moves):
        candidates: List[Tuple[Tuple[float, float, float], BeamNode]] = []
        any_expanded = False

        for node in beam:
            play, used, moves, last_rm, last_pot, ret, is_done, prev_score = node
            if is_done:
                # Keep terminal node in candidate pool without re-stepping it
                s_val = prev_score.fitness_score_S if prev_score else 0.0
                t12 = (
                    prev_score.tier1_struct_penalty + prev_score.tier2_kin_penalty
                    if prev_score
                    else 100.0
                )
                candidates.append(((-s_val, t12, -ret), node))
                continue

            env.play = play.clone()
            env._catalog_used = set(used)
            env.moves_taken = moves
            env._last_rm_reward = last_rm
            env._last_potential = last_pot

            legal = env.legal_moves()
            if not legal:
                continue
            any_expanded = True

            # Prioritize non-finalize moves until all needs are met
            unmet_cnt = len(env.play.unmet_needs())
            idxs = [
                i
                for i, (k, _) in enumerate(legal)
                if not (k == "finalize" and unmet_cnt > 0 and len(legal) > 1)
            ]
            if len(idxs) > beam_width * 3:
                idxs = rng.sample(idxs, beam_width * 3)

            for i in idxs:
                env.play = play.clone()
                env._catalog_used = set(used)
                env.moves_taken = moves
                env._last_rm_reward = last_rm
                env._last_potential = last_pot

                step = env.step(i)
                score = step.info.get("score")
                new_ret = ret + step.reward

                if score is not None and score.is_winning_play:
                    stats = EpisodeStats(
                        True,
                        new_ret,
                        env.moves_taken,
                        float(score.residual_cost),
                        float(score.fitness_score_S),
                    )
                    if best_win is None or (stats.residual, -stats.return_sum) < (
                        best_win.residual,
                        -best_win.return_sum,
                    ):
                        best_win = stats

                t12 = (
                    float(score.tier1_struct_penalty + score.tier2_kin_penalty)
                    if score
                    else 100.0
                )
                s_val = float(score.fitness_score_S) if score else 0.0
                priority = (t12, -s_val, -new_ret)
                candidates.append(
                    (
                        priority,
                        (
                            env.play.clone(),
                            set(env._catalog_used),
                            env.moves_taken,
                            env._last_rm_reward,
                            env._last_potential,
                            new_ret,
                            step.done,
                            score,
                        ),
                    )
                )

        if best_win is not None:
            return best_win
        if not candidates or not any_expanded:
            break
        candidates.sort(key=lambda x: x[0])
        beam = [c[1] for c in candidates[:beam_width]]
        if all(node[6] for node in beam):
            break

    play, used, moves, last_rm, last_pot, ret, _, last_score = beam[0]
    env.play = play
    env._catalog_used = used
    env.moves_taken = moves
    env._last_rm_reward = last_rm
    env._last_potential = last_pot
    score = last_score or env._quick_score()
    return EpisodeStats(
        score.is_winning_play,
        ret,
        moves,
        float(score.residual_cost) if score.is_winning_play else 1e9,
        float(score.fitness_score_S),
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
    stats = [
        run_episode(env, policy=policy, beam_width=beam_width, rng=rng)
        for _ in range(n_episodes)
    ]
    wins = [s for s in stats if s.win]
    first_win_idx = next((idx + 1 for idx, s in enumerate(stats) if s.win), n_episodes)
    return {
        "win_rate": 100.0 * len(wins) / max(1, len(stats)),
        "mean_return": sum(s.return_sum for s in stats) / max(1, len(stats)),
        "mean_residual_win": (
            sum(s.residual for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_etfw": float(first_win_idx) if wins else float("nan"),
        "mean_moves_win": (
            sum(s.moves for s in wins) / len(wins) if wins else float("nan")
        ),
        "mean_fitness": sum(s.fitness for s in stats) / max(1, len(stats)),
        "n_episodes": float(n_episodes),
    }
