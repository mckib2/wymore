import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx5: Input-Determined System

  The next state depends only on the input, not the current state:
  input 3 always goes to state 1, input 4 always goes to state 2.
  This is the discrete-system analogue of a constant-output-per-input
  function — the state provides no memory.
-/

wymore_system Zx5 = (SZx5, IZx5, OZx5, NZx5, RZx5) where
  SZx5 = {1, 2},
  IZx5 = {3, 4},
  OZx5 = {5, 6},
  NZx5 = {((1, 3), 1), ((1, 4), 2), ((2, 3), 1), ((2, 4), 2)},
  RZx5 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- The next state depends only on the input, not the current state. -/
theorem zx5_input_determined (s1 s2 : SZx5) (i : IZx5) :
    Zx5.NZ s1 i = Zx5.NZ s2 i := by
  cases s1 <;> cases s2 <;> cases i <;> rfl

/-- Input v3 always leads to state v1. -/
theorem zx5_input_v3 (s : SZx5) : Zx5.NZ s IZx5.v3 = SZx5.v1 := by
  cases s <;> rfl

/-- Input v4 always leads to state v2. -/
theorem zx5_input_v4 (s : SZx5) : Zx5.NZ s IZx5.v4 = SZx5.v2 := by
  cases s <;> rfl

/-- After one step, the state is completely determined by the most recent input.
    The system "forgets" its history after a single step. -/
theorem zx5_forgets_initial (s0 s0' : SZx5) (f : ITZ IZx5) :
    FSM.generateStateTrajectory Zx5 s0 f 1 = FSM.generateStateTrajectory Zx5 s0' f 1 := by
  simp only [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero]
  exact zx5_input_determined s0 s0' (f 0)

/-- More generally: for any t ≥ 1, the state depends only on f, not s0. -/
theorem zx5_forgets_initial_general (s0 s0' : SZx5) (f : ITZ IZx5) (n : Nat) :
    FSM.generateStateTrajectory Zx5 s0 f (n + 1) =
    FSM.generateStateTrajectory Zx5 s0' f (n + 1) := by
  induction n with
  | zero =>
    simp only [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero]
    exact zx5_input_determined s0 s0' (f 0)
  | succ m ih =>
    simp only [FSM.generateStateTrajectory_succ]
    congr 1

/-- Both states are reachable from any initial state (by choosing the right input). -/
theorem zx5_fully_reachable (s0 s : SZx5) : FSM.Reachable Zx5 s0 s := by
  cases s
  · exact ⟨fun _ => IZx5.v3, 1, by
      show FSM.generateStateTrajectory Zx5 s0 (fun _ => IZx5.v3) 1 = SZx5.v1
      simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, zx5_input_v3]⟩
  · exact ⟨fun _ => IZx5.v4, 1, by
      show FSM.generateStateTrajectory Zx5 s0 (fun _ => IZx5.v4) 1 = SZx5.v2
      simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, zx5_input_v4]⟩
