"""CLI runner for the 14 Progressive Integration Game Examples & Cost Axiom Verification."""

from __future__ import annotations

from integration_game.examples.catalog import ALL_EXAMPLES
from integration_game.scoring import print_progression_table, rank_winning_plays
from integration_game.sensitivity import run_all_cost_assertions, run_weight_sensitivity_sweep


def main() -> None:
    print("=" * 98)
    print("INTEGRATION GAME: 14 PROGRESSIVE SYNTHESIS EXAMPLES & COST AXIOM VERIFICATION")
    print("=" * 98)

    all_breakdowns = []
    for title, fn in ALL_EXAMPLES:
        print(f"\n>>> {title}")
        snaps = fn()
        all_breakdowns.extend(snaps)
        print_progression_table(snaps)
        winners = rank_winning_plays(snaps)
        if len(winners) > 1:
            ranking_str = " > ".join(
                f"{w.snapshot_label} (C_res={w.residual_cost:.2f}, S={w.fitness_score_S:.2f})"
                for w in winners
            )
            print(f"    Pareto Ranking of Winning Plays: {ranking_str}")

    print("\n" + "=" * 98)
    print("TECHNOLOGY-INDEPENDENT COST FUNCTION ASSERTIONS (AXIOMS A1 - A7)")
    print("=" * 98)
    for ax in run_all_cost_assertions(all_breakdowns):
        badge = "PASS" if ax.passed else "FAIL"
        print(f"[{badge}] {ax.axiom_id}: {ax.title}")
        for d in ax.details:
            print(f"       - {d}")

    sweep_points = run_weight_sensitivity_sweep()
    all_sweep_ok = all(pt.all_axioms_passed for pt in sweep_points)
    print("\n" + "=" * 98)
    print(
        f"WEIGHT SENSITIVITY SWEEP: {len(sweep_points)} parameter variations tested | "
        f"All Axioms A1-A7 Invariant: {all_sweep_ok}"
    )
    print("-" * 98)
    for pt in sweep_points:
        rank_summary = " > ".join(pt.winner_ranking)
        print(
            f"  {pt.parameter_name:<8} = {pt.parameter_value:<6.2f} | "
            f"Axioms={str(pt.all_axioms_passed):<5} | Winner Order: {rank_summary}"
        )
    print("=" * 98)


if __name__ == "__main__":
    main()
