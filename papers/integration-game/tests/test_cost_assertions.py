"""Tests for Technology-Independent Cost Function Assertions (Axioms A1–A7) and Sensitivity Analysis."""
from __future__ import annotations

import pytest

from integration_game import (
    BoardEvaluator,
    CatalogCostConfig,
    ColorDistanceConfig,
    DEFAULT_CONFIG,
    GameConfig,
    ScoringConfig,
    run_all_cost_assertions,
    run_weight_sensitivity_sweep,
    verify_a1_feasibility_dominance,
    verify_a2_live_frontier_grounding,
    verify_a3_stepwise_potential_monotonicity,
    verify_a4_route_wiring_continuity,
    verify_a5_tier3_behavioral_monotonicity,
    verify_a6_dynamic_qos_monotonicity,
    verify_a7_parsimony_monotonicity,
)
from integration_game.examples.catalog import ALL_EXAMPLES


def test_axiom_a1_feasibility_dominance_across_all_examples():
    all_breakdowns = []
    for _title, fn in ALL_EXAMPLES:
        all_breakdowns.extend(fn())
    rep = verify_a1_feasibility_dominance(all_breakdowns)
    assert rep.passed, f"Axiom A1 failed: {rep.details}"


def test_axiom_a2_live_frontier_grounding():
    rep = verify_a2_live_frontier_grounding()
    assert rep.passed, f"Axiom A2 failed: {rep.details}"


def test_axiom_a3_stepwise_potential_monotonicity():
    rep = verify_a3_stepwise_potential_monotonicity()
    assert rep.passed, f"Axiom A3 failed: {rep.details}"


def test_axiom_a4_route_wiring_continuity():
    rep = verify_a4_route_wiring_continuity()
    assert rep.passed, f"Axiom A4 failed: {rep.details}"


def test_axiom_a5_tier3_behavioral_monotonicity():
    rep = verify_a5_tier3_behavioral_monotonicity()
    assert rep.passed, f"Axiom A5 failed: {rep.details}"


def test_axiom_a6_dynamic_qos_monotonicity():
    rep = verify_a6_dynamic_qos_monotonicity()
    assert rep.passed, f"Axiom A6 failed: {rep.details}"


def test_axiom_a7_parsimony_monotonicity():
    rep = verify_a7_parsimony_monotonicity()
    assert rep.passed, f"Axiom A7 failed: {rep.details}"


def test_run_all_cost_assertions_suite():
    reports = run_all_cost_assertions()
    assert len(reports) == 7
    for r in reports:
        assert r.passed, f"{r.axiom_id} ({r.title}) failed: {r.details}"


def test_weight_sensitivity_sweep_invariants_and_pareto_shifts():
    points = run_weight_sensitivity_sweep()
    assert len(points) >= 15
    for pt in points:
        assert pt.all_axioms_passed, (
            f"Axiom violated at {pt.parameter_name}={pt.parameter_value}"
        )

    # Verify that low w_loss favors Win_Cheap_Lossy while high w_loss favors Win_Exact_InProcess
    low_loss_pts = [p for p in points if p.parameter_name == "w_loss" and p.parameter_value == 0.2]
    high_loss_pts = [p for p in points if p.parameter_name == "w_loss" and p.parameter_value == 12.0]
    assert low_loss_pts and high_loss_pts
    assert low_loss_pts[0].winner_ranking[0] == "Win_Cheap_Lossy"
    assert high_loss_pts[0].winner_ranking[0] == "Win_Exact_InProcess"
    assert high_loss_pts[0].winner_ranking[-1] == "Win_Cheap_Lossy"


def test_configurable_game_config_overrides():
    custom_cfg = DEFAULT_CONFIG.with_overrides(
        scoring=DEFAULT_CONFIG.scoring.with_overrides(w_color=12.0, w_kin=15.0, gamma=0.9),
        catalog_costs=DEFAULT_CONFIG.catalog_costs.with_overrides(recolor_l=0.75),
        color_distance=DEFAULT_CONFIG.color_distance.with_overrides(c_same_root_penalty=0.4),
    )
    assert isinstance(custom_cfg, GameConfig)
    assert isinstance(custom_cfg.scoring, ScoringConfig)
    assert isinstance(custom_cfg.catalog_costs, CatalogCostConfig)
    assert isinstance(custom_cfg.color_distance, ColorDistanceConfig)
    ev = BoardEvaluator(game_config=custom_cfg)
    assert ev.w_color == 12.0
    assert ev.w_kin == 15.0
    assert ev.gamma == 0.9

    reports = run_all_cost_assertions(game_config=custom_cfg)
    assert all(r.passed for r in reports)
