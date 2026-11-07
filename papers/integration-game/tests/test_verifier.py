"""Tests for Z3 Symbolic Verification, Bounded Model Checking (BMC), and CEGIS."""
from __future__ import annotations

import z3

from integration_game.verifier import (
    cegis_verify_and_augment_ex06,
    run_all_z3_verifications,
    verify_noncommutative_alu_z3,
    verify_ping_pong_queue_bmc_z3,
    verify_stale_gate_bmc_z3,
    verify_symbolic_recolor_chain_z3,
    verify_tmr_voter_bmc_z3,
    verify_vending_fsm_bmc_z3,
)


def test_z3_recolor_chain_coincidence_trap():
    """
    At x = -40, Fahrenheit equals Celsius (-40 F == -40 C).
    Z3 QF_LRA proves the true affine formula universally (unsat) and refutes the
    identity cast y = x (sat) by synthesizing a counterexample x != -40.
    """
    good = verify_symbolic_recolor_chain_z3(
        "Good_F_to_C",
        symbolic_board_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)),
        symbolic_spec_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)),
    )
    bad = verify_symbolic_recolor_chain_z3(
        "Bad_F_to_C_Identity",
        symbolic_board_fn=lambda f: f,
        symbolic_spec_fn=lambda f: (f - z3.RealVal(32)) * (z3.RealVal(5) / z3.RealVal(9)),
    )
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"
    assert "x_in" in bad.counterexample


def test_z3_noncommutative_alu_qf_nra():
    """Z3 QF_NRA certifies E_k = 0.5*m*v^2 and refutes swapped 0.5*v*m^2."""
    good = verify_noncommutative_alu_z3(swapped=False)
    bad = verify_noncommutative_alu_z3(swapped=True)
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"
    assert bad.counterexample["mass_kg"] != bad.counterexample["vel_mps"]


def test_z3_ping_pong_bmc_qf_lira():
    """Z3 BMC proves consume-on-read FIFO across all 2^H schedules and refutes retain-on-read."""
    good = verify_ping_pong_queue_bmc_z3(retain_on_read=False, horizon=6)
    bad = verify_ping_pong_queue_bmc_z3(retain_on_read=True, horizon=6)
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"
    assert "ping_schedule" in bad.counterexample


def test_z3_stale_gate_bmc_qf_lira():
    """Z3 BMC proves StaleGate(max_age=2) prevents stale emissions across all dropout schedules."""
    good = verify_stale_gate_bmc_z3(use_stale_gate=True, max_age=2, horizon=7)
    bad = verify_stale_gate_bmc_z3(use_stale_gate=False, max_age=2, horizon=7)
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"


def test_z3_tmr_voter_bmc_qf_lra():
    """Z3 BMC proves 3-channel TMR majority voter masks any single-sensor glitch."""
    good = verify_tmr_voter_bmc_z3(use_tmr=True, horizon=4)
    bad = verify_tmr_voter_bmc_z3(use_tmr=False, horizon=4)
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"


def test_z3_vending_fsm_bmc_qf_lira():
    """Z3 BMC proves stateful Vending Machine FSM across all coin sequences and refutes stateless assembly."""
    good = verify_vending_fsm_bmc_z3(stateful_fsm=True, horizon=4)
    bad = verify_vending_fsm_bmc_z3(stateful_fsm=False, horizon=4)
    assert good.verified and good.solver_status == "unsat"
    assert not bad.verified and bad.solver_status == "sat"


def test_cegis_counterexample_augmentation_loop():
    """
    Demonstrates that when a weak test scenario (m=10, v=10) is fooled by the swapped-operand
    ALU, Z3 QF_NRA extracts a counterexample (m != v) that augments the scenario and flips
    the swapped board from WIN to UNSAT while the correct board remains WIN.
    """
    res = cegis_verify_and_augment_ex06()
    assert res["weak_scenario_fooled_by_swapped"] is True
    assert res["z3_swapped_result"].verified is False
    assert res["z3_correct_result"].verified is True
    assert res["post_cegis_swapped_wins"] is False
    assert res["post_cegis_correct_wins"] is True


def test_run_all_z3_verifications_suite():
    results = run_all_z3_verifications()
    assert len(results) == 12
    # Even indices are winning architectures (verified=True), odd indices are traps (verified=False)
    for i in range(0, len(results), 2):
        assert results[i].verified, f"Expected {results[i].name} to be certified (UNSAT)"
        assert not results[i + 1].verified, f"Expected {results[i + 1].name} to be refuted (SAT)"
