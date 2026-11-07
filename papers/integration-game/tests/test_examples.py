"""Regression tests for all 14 Progressive Integration Game Examples (`ex01`–`ex14`)."""
from __future__ import annotations

import pytest

from integration_game.examples.catalog import (
    ALL_EXAMPLES,
    example_01_autonomous,
    example_02_ping_pong,
    example_03_kalman,
    example_04_multi_rep,
    example_05_piston,
    example_06_calculator,
    example_07_latency,
    example_08_fanout,
    example_09_ticks,
    example_10_provenance,
    example_11_temporal_join,
    example_12_failover,
    example_13_vending_machine,
    example_14_cost_sensitivity,
)
from integration_game.scoring import rank_winning_plays


@pytest.mark.parametrize("title,fn", ALL_EXAMPLES)
def test_example_ends_in_win(title, fn):
    snaps = fn()
    assert len(snaps) >= 3, f"{title} should have at least 3 progressive snapshots"
    assert snaps[-1].is_winning_play, f"{title} final snapshot is not a winning play: {snaps[-1].notes[:3]}"
    assert snaps[-1].fitness_score_S > snaps[0].fitness_score_S
    assert snaps[-1].total_cost_J < snaps[0].total_cost_J


def test_ex01_autonomous_closed_loop():
    snaps = example_01_autonomous()
    # S0 -> S1 -> S2 (Tier-3 trap) -> S3 (WIN)
    assert snaps[1].tier1_struct_penalty < snaps[0].tier1_struct_penalty
    assert snaps[2].tier1_satisfied and snaps[2].tier2_satisfied and not snaps[2].tier3_satisfied
    assert snaps[3].is_winning_play


def test_ex02_ping_pong_silence_trap():
    snaps = example_02_ping_pong()
    retain = snaps[3]
    assert retain.tier1_satisfied and retain.tier2_satisfied
    assert not retain.tier3_satisfied
    assert retain.tba_result.silence_violations > 0
    assert snaps[-1].is_winning_play
    assert snaps[-1].fitness_score_S > retain.fitness_score_S


def test_ex03_kalman_naive_trap_and_cost_ranking():
    snaps = example_03_kalman()
    naive, kf = snaps[2], snaps[3]
    assert naive.tier1_satisfied and naive.tier2_satisfied and not naive.tier3_satisfied
    assert kf.is_winning_play
    winners = rank_winning_plays(snaps)
    assert winners[0].snapshot_label == kf.snapshot_label


def test_ex04_multi_representation_gateway():
    snaps = example_04_multi_rep()
    # Monotonic fitness increase across S0 -> S1 -> S2 -> S3 (WIN)
    for i in range(len(snaps) - 1):
        assert snaps[i + 1].fitness_score_S > snaps[i].fitness_score_S
    assert snaps[-1].is_winning_play


def test_ex05_piston_hierarchy_and_lying_cast_trap():
    snaps = example_05_piston()
    for i in range(len(snaps) - 1):
        assert snaps[i + 1].fitness_score_S > snaps[i].fitness_score_S
    assert snaps[3].tier1_satisfied and snaps[3].tier2_satisfied and not snaps[3].tier3_satisfied
    assert snaps[4].is_winning_play


def test_ex06_calculator_swapped_operand_trap():
    snaps = example_06_calculator()
    swapped, correct = snaps[2], snaps[3]
    assert swapped.tier1_satisfied and swapped.tier2_satisfied and not swapped.tier3_satisfied
    assert correct.is_winning_play


def test_ex07_hard_latency_overrun_monotonicity():
    snaps = example_07_latency()
    slow5, med3, fast0 = snaps[1], snaps[2], snaps[3]
    assert not slow5.tier3_satisfied and not med3.tier3_satisfied
    assert med3.total_cost_J < slow5.total_cost_J
    assert med3.fitness_score_S > slow5.fitness_score_S
    assert fast0.is_winning_play


def test_ex08_multi_flow_composite_lsc():
    snaps = example_08_fanout()
    assert snaps[1].tba_result.cut_progress_ratio == pytest.approx(0.5)
    assert not snaps[1].is_winning_play
    assert snaps[2].is_winning_play


def test_ex09_mismatched_ticks_invariant_boundaries_and_stale_gate():
    snaps = example_09_ticks()
    no_gate, with_gate = snaps[2], snaps[3]
    assert no_gate.tier1_satisfied and no_gate.tier2_satisfied and not no_gate.tier3_satisfied
    assert no_gate.tba_result.silence_violations >= 1
    assert with_gate.is_winning_play


def test_ex10_provenance_tmr_glitch_masking():
    snaps = example_10_provenance()
    bypass, tmr = snaps[1], snaps[2]
    assert not bypass.tier1_satisfied and not bypass.tier3_satisfied
    assert tmr.is_winning_play


def test_ex11_temporal_join_window_correlation():
    snaps = example_11_temporal_join()
    win0, win1 = snaps[1], snaps[2]
    assert win0.tier1_satisfied and not win0.tier3_satisfied
    assert win1.is_winning_play


def test_ex12_dynamic_failover_mux():
    snaps = example_12_failover()
    static_mux, dyn_mux = snaps[2], snaps[3]
    assert static_mux.tier1_satisfied and not static_mux.tier3_satisfied
    assert dyn_mux.is_winning_play


def test_ex13_stateful_vending_machine_fsm():
    snaps = example_13_vending_machine()
    stateless, stateful = snaps[2], snaps[3]
    assert stateless.tier1_satisfied and stateless.tier2_satisfied and not stateless.tier3_satisfied
    assert stateless.tba_result.silence_violations >= 1
    assert stateful.is_winning_play


def test_ex14_cost_sensitivity_pareto_ranking():
    snaps = example_14_cost_sensitivity()
    assert not snaps[0].is_winning_play
    winners = rank_winning_plays(snaps)
    assert len(winners) == 4
    # Optimal minimal play is ranked #1, followed by redundant identity, lossy f32, and high-latency IPC
    assert "Arch 5" in winners[0].snapshot_label
    assert "Arch 4" in winners[1].snapshot_label
    assert "Arch 3" in winners[2].snapshot_label
    assert "Arch 2" in winners[3].snapshot_label
