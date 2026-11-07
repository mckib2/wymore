"""Tests for offline synthesis MDP, Masked PPO, Tier-3 traps, CEGIS, and Online RL adaptation."""
from __future__ import annotations

import pytest

from integration_game import (
    Board,
    Color,
    ConsumerBoundary,
    FinalizeBoard,
    IllegalMoveError,
    MessageShape,
    Play,
    ProducerBoundary,
    RMState,
    TransferMode,
    UniversalLSC,
)
from integration_game.board import CompatibilityError
from integration_game.primitives import Field, Message, Provenance
from integration_game.rl import (
    IntegrationGameEnv,
    evaluate_masked_ppo,
    evaluate_online_controller,
    evaluate_policy,
    make_calculator_task,
    make_industrial_holdout_task,
    make_kalman_task,
    make_ping_pong_task,
    make_training_tasks,
    run_episode,
    train_masked_ppo,
    train_multitask_ppo,
    train_online_controller,
)


def test_absorbing_breach_does_not_heal():
    c = Color("A", "u", "f")
    ulsc = UniversalLSC(
        name="t",
        target_need_id="N",
        horizon=4,
        pre_trigger_fn=lambda t, env: Message.single(
            Field(1, c, provenance=Provenance(timestamp_tick=t))
        )
        if t in (0, 2)
        else None,
        value_distance_fn=lambda trig, out: 10.0,  # always bad
        tolerance=0.0,
        max_delay=1,
        enforce_silence=True,
    )
    outs = {
        0: Message.single(Field(0, c)),
        2: Message.single(Field(0, c)),
    }
    res = ulsc.evaluate_trace({}, outs)
    assert res.hot_breaches >= 1
    assert RMState.BREACH in res.rm_state_trace
    last_breach = max(i for i, s in enumerate(res.rm_state_trace) if s == RMState.BREACH)
    assert all(s != RMState.COMPLETED for s in res.rm_state_trace[last_breach:])


def test_strict_connect_rejects_trust_gap():
    c = Color("A", "u", "f")
    b = Board("t")
    b.add_component(ProducerBoundary("P", "out", c))
    b.add_component(
        ConsumerBoundary(
            "C",
            "in",
            MessageShape.single(c, min_trust=0.99, required_assurance="TMR_VOTED"),
        )
    )
    with pytest.raises(CompatibilityError):
        b.connect("P.out", "C.in", strict=True)


def test_finalized_play_rejects_redundant_finalize_and_clears_legal_moves():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset()
    assert env.play is not None
    env.play.apply(FinalizeBoard())
    assert env.legal_moves() == []
    with pytest.raises(IllegalMoveError):
        env.play.apply(FinalizeBoard())


def test_ping_pong_env_legal_moves_and_greedy_can_win():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset()
    legal = env.legal_moves()
    assert any(k == "add" for k, _ in legal)
    assert any(k == "finalize" for k, _ in legal)
    scripted = run_episode(env, policy="scripted")
    assert scripted.win
    assert scripted.return_sum > 40.0
    greedy = evaluate_policy(task, "greedy", n_episodes=5, seed=0)
    assert greedy["win_rate"] == 100.0
    beam = evaluate_policy(task, "beam", n_episodes=3, seed=0, beam_width=5)
    assert beam["win_rate"] == 100.0
    assert beam["mean_return"] > 40.0


def test_silence_dilutes_cut_progress():
    c = Color("A", "u", "f")
    ulsc = UniversalLSC(
        name="t",
        target_need_id="N",
        horizon=3,
        pre_trigger_fn=lambda t, env: Message.single(Field(1, c)) if t == 0 else None,
        value_distance_fn=lambda trig, out: 0.0,
        tolerance=0.0,
        max_delay=0,
        enforce_silence=True,
    )
    res = ulsc.evaluate_trace(
        {},
        {
            0: Message.single(Field(1, c)),
            1: Message.single(Field(1, c)),
        },
    )
    assert res.silence_violations >= 1
    assert res.cut_progress_ratio < 1.0


def test_tier3_trap_fools_myopic_greedy_but_masked_ppo_wins():
    task = make_kalman_task(include_trap=True)
    # Greedy picks the cheaper NaiveDiff trap (static_cost=0.4 < 1.2) which passes Tiers 1-2 but fails Tier 3
    greedy_m = evaluate_policy(task, "greedy", n_episodes=5, seed=0)
    assert greedy_m["win_rate"] == 0.0

    # Masked PPO learns from Tier-3 RM/Omega feedback to select KalmanFilter
    ppo_agent = train_masked_ppo(task, n_episodes=80, seed=0)
    ppo_m = evaluate_masked_ppo(task, ppo_agent, n_episodes=20, seed=1, greedy=True)
    assert ppo_m["win_rate"] == 100.0


def test_cegis_augmentation_prevents_swapped_alu_overfitting():
    weak_task = make_calculator_task(include_trap=True, weak_coincidence_scenario=True)
    full_task = make_calculator_task(include_trap=True, weak_coincidence_scenario=False)

    # Without Omega/CEGIS on the weak symmetric scenario (m=10, v=10), the cheaper swapped ALU wins weak_task
    weak_agent = train_masked_ppo(
        weak_task, n_episodes=60, seed=0, use_omega_breach=False
    )
    eval_on_full = evaluate_masked_ppo(full_task, weak_agent, n_episodes=10, seed=1, greedy=True)
    assert eval_on_full["win_rate"] == 0.0

    # With CEGIS-augmented scenario (full_task) and Omega, Masked PPO converges to the true ALU
    cegis_agent = train_masked_ppo(
        full_task, n_episodes=80, seed=0, use_omega_breach=True
    )
    eval_cegis = evaluate_masked_ppo(full_task, cegis_agent, n_episodes=10, seed=1, greedy=True)
    assert eval_cegis["win_rate"] == 100.0


def test_holdout_ex15_relational_transfer():
    train_tasks = make_training_tasks(include_traps=True)[:3]
    shared_agent = train_multitask_ppo(train_tasks, episodes_per_task=40, seed=0)
    holdout = make_industrial_holdout_task(include_trap=True)
    ft_agent = train_masked_ppo(holdout, n_episodes=60, seed=1, initial_agent=shared_agent)
    m = evaluate_masked_ppo(holdout, ft_agent, n_episodes=15, seed=2, greedy=True)
    assert m["win_rate"] == 100.0


def test_online_adaptive_mediation_failover():
    ctrl = train_online_controller(n_episodes=60, seed=0)
    m_static = evaluate_online_controller("static_primary", n_episodes=15, seed=42)
    m_scripted = evaluate_online_controller("scripted_threshold", n_episodes=15, seed=42)
    m_ppo = evaluate_online_controller("online_ppo", controller=ctrl, n_episodes=15, seed=42)

    assert m_ppo["mean_breaches"] < m_scripted["mean_breaches"] < m_static["mean_breaches"]
    assert m_ppo["tier3_sat_pct"] > m_static["tier3_sat_pct"]
    assert m_ppo["recovery_ticks"] <= m_scripted["recovery_ticks"]
