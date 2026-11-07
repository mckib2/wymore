"""Regression tests for Examples 1–12 progressive catalogs."""
from __future__ import annotations

import pytest

from integration_game.examples.catalog import ALL_EXAMPLES, example_02_ping_pong, example_03_kalman
from integration_game.scoring import rank_winning_plays


@pytest.mark.parametrize("title,fn", ALL_EXAMPLES)
def test_example_ends_in_win(title, fn):
    snaps = fn()
    assert snaps, f"{title} produced no snapshots"
    assert snaps[-1].is_winning_play, f"{title} final snapshot is not a winning play: {snaps[-1].notes[:3]}"


def test_ping_pong_silence_trap():
    snaps = example_02_ping_pong()
    retain = snaps[3]
    assert retain.tier1_satisfied and retain.tier2_satisfied
    assert not retain.tier3_satisfied
    assert retain.tba_result.silence_violations > 0
    assert snaps[-1].is_winning_play
    assert snaps[-1].fitness_score_S >= retain.fitness_score_S


def test_kalman_naive_trap_and_cost_ranking():
    snaps = example_03_kalman()
    naive, kf = snaps[1], snaps[2]
    assert naive.tier1_satisfied and naive.tier2_satisfied and not naive.tier3_satisfied
    assert kf.is_winning_play
    winners = rank_winning_plays(snaps)
    assert winners[0].snapshot_label == kf.snapshot_label
    # Kalman has higher static cost than a hypothetical cheaper win; residual reported
    assert kf.residual_cost >= naive.static_cost or kf.static_cost > naive.static_cost


def test_fitness_nondecreasing_to_win_ping_pong():
    snaps = example_02_ping_pong()
    # Soft progress: final S should beat initial S
    assert snaps[-1].fitness_score_S > snaps[0].fitness_score_S
