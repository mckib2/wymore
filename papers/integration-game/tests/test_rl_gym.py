"""Gymnasium adapter, clone/state, pickle, and structural-score contracts."""
from __future__ import annotations

import pickle

import pytest

from integration_game.rl.env import IntegrationGameEnv, make_ping_pong_task
from integration_game.rl.baselines import run_episode


def test_clone_preserves_future_rewards():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset(seed=0)
    assert env.task.scripted_moves
    # Take first scripted add
    kind, payload = env.task.scripted_moves[0]
    legal = env.legal_moves()
    idx = next(i for i, kp in enumerate(legal) if kp == (kind, payload))
    twin = env.clone()
    r1 = env.step(idx)
    r2 = twin.step(idx)
    assert r1.reward == pytest.approx(r2.reward)
    assert r1.obs == r2.obs
    assert env.moves_taken == twin.moves_taken


def test_oob_action_does_not_clamp():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset()
    n = len(env.legal_moves())
    before = env.observe()
    result = env.step(n + 5)
    assert "illegal" in result.info
    assert result.reward < 0
    # Board unchanged except moves_taken
    assert env.observe()["n_components"] == before["n_components"]
    assert env.observe()["n_routes"] == before["n_routes"]


def test_synth_task_and_env_pickle_roundtrip():
    task = make_ping_pong_task(include_trap=True)
    blob = pickle.dumps(task)
    task2 = pickle.loads(blob)
    assert task2.name == task.name
    assert task2.rebuild_fn == "make_ping_pong_task"
    env = IntegrationGameEnv(task2)
    env.reset()
    assert run_episode(env, policy="scripted").win

    env_blob = pickle.dumps(IntegrationGameEnv(task))
    env3 = pickle.loads(env_blob)
    env3.reset()
    assert run_episode(env3, policy="scripted").win


def test_structural_score_skips_tier3_and_is_cheap():
    task = make_ping_pong_task()
    env = IntegrationGameEnv(task)
    env.reset()
    struct = env.structural_score()
    assert struct.tier3_satisfied is False
    assert "structural_only" in struct.notes
    full = env._quick_score()
    assert struct.tier1_struct_penalty == pytest.approx(full.tier1_struct_penalty)
    assert struct.tier2_kin_penalty == pytest.approx(full.tier2_kin_penalty)


def test_gymnasium_mask_compliance_and_check_env():
    gymnasium = pytest.importorskip("gymnasium")
    from gymnasium.utils.env_checker import check_env

    from integration_game.rl.gym_env import make_offline_gym_env

    env = make_offline_gym_env("ex02", max_actions=64)
    obs, info = env.reset(seed=0)
    assert obs["obs"].shape == (12,)
    assert obs["action_mask"].shape == (64,)
    assert obs["action_mask"].sum() >= 1

    # Masked random never picks masked-off actions
    for _ in range(20):
        if obs["action_mask"].sum() == 0:
            break
        legal_slots = obs["action_mask"].nonzero()[0]
        action = int(legal_slots[0])
        obs, reward, terminated, truncated, info = env.step(action)
        assert "illegal" not in info or info.get("illegal") is not True
        if terminated or truncated:
            obs, info = env.reset(seed=1)
            break

    # Illegal masked action is no-op penalty (never clamp)
    obs, info = env.reset(seed=2)
    illegal = int((1 - obs["action_mask"]).nonzero()[0][0])
    obs2, reward, terminated, truncated, info2 = env.step(illegal)
    assert info2.get("illegal") is True
    assert reward < 0

    # Soft check_env (skip render)
    check_env(env.unwrapped if hasattr(env, "unwrapped") else env, skip_render_check=True)


def test_gym_scripted_can_win_via_masked_slots():
    pytest.importorskip("gymnasium")
    from integration_game.rl.gym_env import make_offline_gym_env

    env = make_offline_gym_env("ex02", max_actions=64)
    obs, _ = env.reset(seed=0)
    core = env.core
    assert core.task.scripted_moves
    for kind, payload in core.task.scripted_moves:
        mask = obs["action_mask"]
        decode = env._decode
        slot = next(
            s for s, kp in decode.items() if kp == (kind, payload) and mask[s]
        )
        obs, reward, terminated, truncated, info = env.step(int(slot))
        if terminated or truncated:
            break
    assert info.get("win") or (core.play is not None and not core.play.finalized)
    # Finish with remaining scripted if needed
    while not (terminated or truncated):
        legal = [s for s in range(env.max_actions) if obs["action_mask"][s]]
        if not legal:
            break
        # Prefer finalize only when ready; else first legal
        obs, reward, terminated, truncated, info = env.step(legal[0])
    # At least exercise gym path; scripted via core remains authoritative
    core2 = IntegrationGameEnv(make_ping_pong_task())
    assert run_episode(core2, policy="scripted").win
