"""Evaluate random/greedy/beam (+ optional REINFORCE) and write artifacts/rl_metrics.json."""
from __future__ import annotations

import json
import time
from pathlib import Path

from .baselines import evaluate_policy
from .env import make_ping_pong_task
from .train_offline import train_reinforce, evaluate_reinforce


def main() -> None:
    task = make_ping_pong_task()
    metrics: dict = {"task": task.name, "agents": {}}

    for policy in ("scripted", "random", "greedy", "beam"):
        t0 = time.perf_counter()
        n = 5 if policy == "scripted" else (30 if policy != "beam" else 10)
        m = evaluate_policy(task, policy=policy, n_episodes=n, seed=0, beam_width=5)
        m["wall_s"] = round(time.perf_counter() - t0, 3)
        metrics["agents"][policy] = m
        print(policy, m)

    t0 = time.perf_counter()
    agent = train_reinforce(task, n_episodes=200, seed=0)
    m = evaluate_reinforce(task, agent, n_episodes=30, seed=1)
    m["wall_s"] = round(time.perf_counter() - t0, 3)
    metrics["agents"]["reinforce"] = m
    print("reinforce", m)

    from integration_game.examples.ex02_ping_pong import example_02_ping_pong

    snaps = example_02_ping_pong()
    win = snaps[-1]
    metrics["scale"] = {
        "ex02_win_fitness": win.fitness_score_S,
        "ex02_win_residual": win.residual_cost,
        "ex02_static": win.static_cost,
    }

    out = Path(__file__).resolve().parents[3] / "artifacts" / "rl_metrics.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(metrics, indent=2))
    print("wrote", out)


if __name__ == "__main__":
    main()
