"""Tests for synthesis MDP, absorbing BREACH, and provenance-strict connect."""
from __future__ import annotations

from integration_game import (
    Board,
    Color,
    ConsumerBoundary,
    MessageShape,
    ProducerBoundary,
    RMState,
    TransferMode,
    UniversalLSC,
)
from integration_game.board import CompatibilityError
from integration_game.primitives import Message, Field, Dynamics, Provenance
from integration_game.rl.env import IntegrationGameEnv, make_ping_pong_task
from integration_game.rl.baselines import evaluate_policy, run_episode


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
    # After first breach, state must remain BREACH (no COMPLETED heal)
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
    try:
        b.connect("P.out", "C.in", strict=True)
        raised = False
    except CompatibilityError:
        raised = True
    assert raised


def test_ping_pong_env_legal_moves_and_greedy_can_win():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset()
    legal = env.legal_moves()
    assert any(k == "add" for k, _ in legal)
    assert any(k == "finalize" for k, _ in legal)
    scripted = run_episode(env, policy="scripted")
    assert scripted.win
    greedy = evaluate_policy(task, "greedy", n_episodes=5, seed=0)
    assert greedy["win_rate"] == 100.0


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
    # Proper fulfill at 0, then silence breach at 1
    res = ulsc.evaluate_trace(
        {},
        {
            0: Message.single(Field(1, c)),
            1: Message.single(Field(1, c)),
        },
    )
    assert res.silence_violations >= 1
    assert res.cut_progress_ratio < 1.0
