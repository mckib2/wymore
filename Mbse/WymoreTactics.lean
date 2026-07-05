import Mbse.WymoreSimp

/-!
# Wymore proof tactics

Macro tactics wrapping the lemma library in [`Trajectory`](Trajectory.lean).
-/

open Lean Parser Tactic

/-- `wymore_trajectory_induction` runs standard induction on trajectory time. -/
syntax (name := wymoreTrajectoryInduction) "wymore_trajectory_induction" : tactic

macro_rules
  | `(tactic| wymore_trajectory_induction) =>
    `(tactic| intro t; induction t with
      | zero => simp [generateStateTrajectory_zero]
      | succ n ih => simp [generateStateTrajectory_succ])

/-- `wymore_output_of_state h` rewrites an output goal using a state trajectory lemma. -/
syntax (name := wymoreOutputOfState) "wymore_output_of_state " rwRule : tactic

macro_rules
  | `(tactic| wymore_output_of_state $h:rwRule) =>
    `(tactic| unfold generateOutputTrajectory; rw [$h])

/-- `wymore_card_rng` closes the varying-output ↔ `RNG` cardinality equivalence. -/
syntax (name := wymoreCardRng) "wymore_card_rng" : tactic

macro_rules
  | `(tactic| wymore_card_rng) =>
    `(tactic| exact Trajectory.varyingOutput_iff_card_rng)

/-- `wymore_simp` runs the `@[wymore]` simp set. -/
syntax (name := wymoreSimp) "wymore_simp" : tactic

macro_rules
  | `(tactic| wymore_simp) =>
    `(tactic| simp only [wymore])
