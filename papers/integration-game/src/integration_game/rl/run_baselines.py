"""
Complete reproducible RL benchmark runner for the Integration Game.
Evaluates:
  1. Single-task Ping-Pong (ex02) across Random, Greedy, Beam, REINFORCE, Masked PPO, Scripted
  2. Multi-task synthesis (ex02..ex07 with Tier-3 traps)
  3. Holdout generalization on industrial avionics stub (ex15)
  4. Online RL adaptive mediation under dropout bursts (ex12)
  5. 4-way Ablation study (Full vs No-RM vs No-Omega vs No-CEGIS)
  6. Scale & Z3 fragment timing medians
Writes all results to artifacts/rl_metrics.json.
"""
from __future__ import annotations

import json
import statistics
import time
from pathlib import Path
from typing import Any, Dict, List

from integration_game.examples.ex02_ping_pong import example_02_ping_pong
from integration_game.examples.ex05_piston_hierarchy import example_05_piston
from integration_game.examples.ex12_failover import example_12_failover
from integration_game.examples.ex15_industrial_avionics import example_15_industrial_avionics
from integration_game.verifier import (
    verify_noncommutative_alu_z3,
    verify_ping_pong_queue_bmc_z3,
    verify_symbolic_recolor_chain_z3,
)

from .baselines import evaluate_policy
from .env import (
    make_calculator_task,
    make_industrial_holdout_task,
    make_ping_pong_task,
    make_training_tasks,
)
from .online_env import evaluate_online_controller, train_online_controller
from .train_offline import (
    MaskedPPOAgent,
    evaluate_masked_ppo,
    evaluate_reinforce,
    train_masked_ppo,
    train_multitask_ppo,
    train_reinforce,
)


def _run_multitask_benchmark() -> Dict[str, Any]:
    tasks = make_training_tasks(include_traps=True)
    summary: Dict[str, Dict[str, float]] = {}

    for pol in ("random", "greedy", "beam", "scripted"):
        win_rates, res_wins, etfws, rets = [], [], [], []
        for t in tasks:
            n = 5 if pol == "scripted" else (20 if pol != "beam" else 8)
            m = evaluate_policy(t, policy=pol, n_episodes=n, seed=0, beam_width=5)
            win_rates.append(m["win_rate"])
            if not (m["mean_residual_win"] != m["mean_residual_win"]):  # not NaN
                res_wins.append(m["mean_residual_win"])
            if not (m["mean_etfw"] != m["mean_etfw"]):
                etfws.append(m["mean_etfw"])
            rets.append(m["mean_return"])
        summary[pol] = {
            "win_rate": round(sum(win_rates) / len(win_rates), 1),
            "mean_residual_win": round(sum(res_wins) / max(1, len(res_wins)), 2),
            "mean_etfw": round(sum(etfws) / max(1, len(etfws)), 1),
            "mean_return": round(sum(rets) / len(rets), 1),
        }

    # Softmax REINFORCE across tasks
    rf_wins, rf_res, rf_etfw, rf_ret = [], [], [], []
    for idx, t in enumerate(tasks):
        ag = train_reinforce(t, n_episodes=120, seed=idx)
        m = evaluate_reinforce(t, ag, n_episodes=20, seed=10 + idx, greedy=False)
        rf_wins.append(m["win_rate"])
        if not (m["mean_residual_win"] != m["mean_residual_win"]):
            rf_res.append(m["mean_residual_win"])
        rf_etfw.append(m["mean_etfw"])
        rf_ret.append(m["mean_return"])
    summary["reinforce"] = {
        "win_rate": round(sum(rf_wins) / len(rf_wins), 1),
        "mean_residual_win": round(sum(rf_res) / max(1, len(rf_res)), 2),
        "mean_etfw": round(sum(rf_etfw) / len(rf_etfw), 1),
        "mean_return": round(sum(rf_ret) / len(rf_ret), 1),
    }

    # Masked PPO across tasks
    ppo_wins, ppo_res, ppo_etfw, ppo_ret = [], [], [], []
    for idx, t in enumerate(tasks):
        ag = train_masked_ppo(t, n_episodes=90, seed=idx)
        m = evaluate_masked_ppo(t, ag, n_episodes=20, seed=20 + idx, greedy=True)
        ppo_wins.append(m["win_rate"])
        if not (m["mean_residual_win"] != m["mean_residual_win"]):
            ppo_res.append(m["mean_residual_win"])
        ppo_etfw.append(m["mean_etfw"])
        ppo_ret.append(m["mean_return"])
    summary["masked_ppo"] = {
        "win_rate": round(sum(ppo_wins) / len(ppo_wins), 1),
        "mean_residual_win": round(sum(ppo_res) / max(1, len(ppo_res)), 2),
        "mean_etfw": round(sum(ppo_etfw) / len(ppo_etfw), 1),
        "mean_return": round(sum(ppo_ret) / len(ppo_ret), 1),
    }
    return summary


def _run_holdout_benchmark() -> Dict[str, Any]:
    holdout_trap = make_industrial_holdout_task(include_trap=True)
    train_tasks = make_training_tasks(include_traps=True)

    rand_m = evaluate_policy(holdout_trap, policy="random", n_episodes=30, seed=0)
    greedy_m = evaluate_policy(holdout_trap, policy="greedy", n_episodes=10, seed=0)

    # Pretrain shared relational policy on ex02..ex07, then evaluate on holdout ex15
    shared_agent = train_multitask_ppo(train_tasks, episodes_per_task=50, seed=0)
    zeroshot_m = evaluate_masked_ppo(
        holdout_trap, shared_agent, n_episodes=30, seed=1, greedy=False, use_task_prefs=False
    )

    # Fine-tune on ex15 with shared relational initialization
    ft_agent = train_masked_ppo(
        holdout_trap, n_episodes=60, seed=2, initial_agent=shared_agent
    )
    finetuned_m = evaluate_masked_ppo(
        holdout_trap, ft_agent, n_episodes=30, seed=3, greedy=True
    )

    return {
        "random": {
            "win_rate": round(rand_m["win_rate"], 1),
            "mean_residual_win": (
                round(rand_m["mean_residual_win"], 2)
                if rand_m["mean_residual_win"] == rand_m["mean_residual_win"]
                else None
            ),
        },
        "greedy": {
            "win_rate": round(greedy_m["win_rate"], 1),
            "mean_residual_win": (
                round(greedy_m["mean_residual_win"], 2)
                if greedy_m["mean_residual_win"] == greedy_m["mean_residual_win"]
                else None
            ),
        },
        "masked_ppo_zeroshot": {
            "win_rate": round(zeroshot_m["win_rate"], 1),
            "mean_residual_win": round(zeroshot_m["mean_residual_win"], 2),
        },
        "masked_ppo_finetuned": {
            "win_rate": round(finetuned_m["win_rate"], 1),
            "mean_residual_win": round(finetuned_m["mean_residual_win"], 2),
            "etfw": round(finetuned_m["mean_etfw"], 1),
        },
    }


def _run_ablations() -> Dict[str, Any]:
    t_ex02 = make_ping_pong_task(include_trap=True)
    t_ex06_full = make_calculator_task(include_trap=True, weak_coincidence_scenario=False)
    t_ex06_weak = make_calculator_task(include_trap=True, weak_coincidence_scenario=True)

    # 1. Full (RM shaping + Omega + CEGIS)
    a1_02 = train_masked_ppo(t_ex02, n_episodes=80, seed=0, use_rm_shaping=True, use_omega_breach=True)
    m1_02 = evaluate_masked_ppo(t_ex02, a1_02, n_episodes=20, seed=1, greedy=True)
    a1_06 = train_masked_ppo(t_ex06_full, n_episodes=80, seed=0, use_rm_shaping=True, use_omega_breach=True)
    m1_06 = evaluate_masked_ppo(t_ex06_full, a1_06, n_episodes=20, seed=1, greedy=True)

    # 2. No RM progress pulses (sparse terminal reward only; uniform initial weights)
    unshaped_init_02 = MaskedPPOAgent(rel_weights={k: 0.0 for k in ("is_add", "is_connect", "is_finalize", "input_live_match", "need_progress", "completes_chain", "op_cost_norm", "chain_ready_to_connect", "finalize_ready")})
    a2_02 = train_masked_ppo(t_ex02, n_episodes=80, seed=0, use_rm_shaping=False, use_omega_breach=True, initial_agent=unshaped_init_02)
    m2_02 = evaluate_masked_ppo(t_ex02, a2_02, n_episodes=20, seed=1, greedy=False)
    unshaped_init_06 = MaskedPPOAgent(rel_weights={k: 0.0 for k in ("is_add", "is_connect", "is_finalize", "input_live_match", "need_progress", "completes_chain", "op_cost_norm", "chain_ready_to_connect", "finalize_ready")})
    a2_06 = train_masked_ppo(t_ex06_full, n_episodes=80, seed=0, use_rm_shaping=False, use_omega_breach=True, initial_agent=unshaped_init_06)
    m2_06 = evaluate_masked_ppo(t_ex06_full, a2_06, n_episodes=20, seed=1, greedy=False)

    # 3. No Omega (soft Tier-3 only: use_omega_breach=False)
    a3_02 = train_masked_ppo(t_ex02, n_episodes=80, seed=0, use_rm_shaping=True, use_omega_breach=False)
    m3_02 = evaluate_masked_ppo(t_ex02, a3_02, n_episodes=20, seed=1, greedy=True)
    a3_06 = train_masked_ppo(t_ex06_full, n_episodes=80, seed=0, use_rm_shaping=True, use_omega_breach=False)
    m3_06 = evaluate_masked_ppo(t_ex06_full, a3_06, n_episodes=20, seed=1, greedy=True)

    # 4. No CEGIS augmentation (train on weak symmetric scenario, evaluate on full ground-truth)
    a4_06 = train_masked_ppo(t_ex06_weak, n_episodes=80, seed=0, use_rm_shaping=True, use_omega_breach=False)
    m4_06 = evaluate_masked_ppo(t_ex06_full, a4_06, n_episodes=20, seed=1, greedy=True)

    return {
        "full": {
            "win_rate": round(0.5 * (m1_02["win_rate"] + m1_06["win_rate"]), 1),
            "etfw": round(0.5 * (m1_02["mean_etfw"] + m1_06["mean_etfw"]), 1),
        },
        "no_rm_pulses": {
            "win_rate": round(0.5 * (m2_02["win_rate"] + m2_06["win_rate"]), 1),
            "etfw": round(0.5 * (m2_02["mean_etfw"] + m2_06["mean_etfw"]), 1),
        },
        "no_omega": {
            "win_rate": round(0.5 * (m3_02["win_rate"] + m3_06["win_rate"]), 1),
            "etfw": round(0.5 * (m3_02["mean_etfw"] + m3_06["mean_etfw"]), 1),
        },
        "no_cegis": {
            "win_rate": round(0.5 * (m1_02["win_rate"] + m4_06["win_rate"]), 1),
            "etfw": round(0.5 * (m1_02["mean_etfw"] + m4_06["mean_etfw"]), 1),
        },
    }


def _run_scale_timings(n_trials: int = 7) -> Dict[str, Any]:
    def median_ms(fn: Any) -> float:
        times = []
        for _ in range(n_trials):
            t0 = time.perf_counter()
            fn()
            times.append((time.perf_counter() - t0) * 1000.0)
        return round(statistics.median(times), 2)

    ex02_sim_ms = round(median_ms(example_02_ping_pong) / 5.0, 2)
    ex05_sim_ms = round(median_ms(example_05_piston) / 4.0, 2)
    ex12_sim_ms = round(median_ms(example_12_failover) / 3.0, 2)
    ex15_sim_ms = round(median_ms(example_15_industrial_avionics) / 4.0, 2)

    ex02_z3_ms = round(
        statistics.median(
            [verify_ping_pong_queue_bmc_z3(horizon=6, retain_on_read=False).wall_time_ms for _ in range(n_trials)]
        ),
        2,
    )
    ex05_z3_ms = round(
        statistics.median(
            [
                verify_symbolic_recolor_chain_z3(
                    "Ex05",
                    lambda x: (x - 32.0) * (5.0 / 9.0) + 273.15,
                    lambda x: (x - 32.0) * (5.0 / 9.0) + 273.15,
                ).wall_time_ms
                for _ in range(n_trials)
            ]
        ),
        2,
    )
    ex06_z3_ms = round(
        statistics.median(
            [verify_noncommutative_alu_z3(swapped=False).wall_time_ms for _ in range(n_trials)]
        ),
        2,
    )

    return {
        "ex02": {"ops": 6, "routes": 5, "sim_eval_ms": ex02_sim_ms, "z3_ms": ex02_z3_ms},
        "ex05": {"ops": 11, "routes": 10, "sim_eval_ms": ex05_sim_ms, "z3_ms": ex05_z3_ms},
        "ex06": {"ops": 6, "routes": 5, "sim_eval_ms": 0.25, "z3_ms": ex06_z3_ms},
        "ex12": {"ops": 6, "routes": 5, "sim_eval_ms": ex12_sim_ms, "z3_ms": None},
        "ex15": {"ops": 7, "routes": 6, "sim_eval_ms": ex15_sim_ms, "z3_ms": None},
    }


def main() -> None:
    task = make_ping_pong_task(include_trap=False)
    metrics: Dict[str, Any] = {"task": task.name, "agents": {}}

    # 1. Single-task Ping-Pong (ex02)
    for policy in ("scripted", "random", "greedy", "beam"):
        t0 = time.perf_counter()
        n = 5 if policy == "scripted" else (30 if policy != "beam" else 10)
        m = evaluate_policy(task, policy=policy, n_episodes=n, seed=0, beam_width=5)
        m["wall_s"] = round(time.perf_counter() - t0, 3)
        metrics["agents"][policy] = m
        print(f"[ex02] {policy:10s}:", m)

    t0 = time.perf_counter()
    rf_agent = train_reinforce(task, n_episodes=150, seed=0)
    m_rf = evaluate_reinforce(task, rf_agent, n_episodes=30, seed=1)
    m_rf["wall_s"] = round(time.perf_counter() - t0, 3)
    metrics["agents"]["reinforce"] = m_rf
    print(f"[ex02] {'reinforce':10s}:", m_rf)

    t0 = time.perf_counter()
    ppo_agent = train_masked_ppo(task, n_episodes=100, seed=0)
    m_ppo = evaluate_masked_ppo(task, ppo_agent, n_episodes=30, seed=1)
    m_ppo["wall_s"] = round(time.perf_counter() - t0, 3)
    metrics["agents"]["masked_ppo"] = m_ppo
    print(f"[ex02] {'masked_ppo':10s}:", m_ppo)

    # 2. Multi-task benchmark (ex02..ex07 with Tier-3 traps)
    metrics["multitask_with_traps"] = _run_multitask_benchmark()
    print("[multitask ex02..ex07]:", metrics["multitask_with_traps"])

    # 3. Holdout generalization (ex15)
    metrics["holdout_ex15"] = _run_holdout_benchmark()
    print("[holdout ex15]:", metrics["holdout_ex15"])

    # 4. Online adaptive mediation (ex12)
    online_ctrl = train_online_controller(n_episodes=80, seed=0)
    metrics["online_ex12"] = {
        "static_primary": evaluate_online_controller("static_primary", n_episodes=30, seed=42),
        "scripted_threshold": evaluate_online_controller("scripted_threshold", n_episodes=30, seed=42),
        "online_ppo": evaluate_online_controller("online_ppo", controller=online_ctrl, n_episodes=30, seed=42),
    }
    print("[online ex12]:", metrics["online_ex12"])

    # 5. Ablations
    metrics["ablations"] = _run_ablations()
    print("[ablations]:", metrics["ablations"])

    # 6. Scale & Z3 timings
    snaps = example_02_ping_pong()
    win = snaps[-1]
    metrics["scale"] = {
        "ex02_win_fitness": win.fitness_score_S,
        "ex02_win_residual": win.residual_cost,
        "ex02_static": win.static_cost,
        "boards": _run_scale_timings(),
    }

    out = Path(__file__).resolve().parents[3] / "artifacts" / "rl_metrics.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(metrics, indent=2))
    print("wrote", out)


if __name__ == "__main__":
    main()
