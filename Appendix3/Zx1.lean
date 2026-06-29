import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx1: Trivial Single-State System

  The simplest possible Wymore system: one state, one input, one output.
  All transitions return to the only state. This is a fixed point of the
  dynamics — it demonstrates the degenerate base case.
-/

wymore_system Zx1 = (SZx1, IZx1, OZx1, NZx1, RZx1) where
  SZx1 = {1},
  IZx1 = {2},
  OZx1 = {3},
  NZx1 = {((1, 2), 1)},
  RZx1 = {(1, 3)}.

-- Basic definitional checks
example : Zx1.NZ SZx1.v1 IZx1.v2 = SZx1.v1 := rfl
example : Zx1.RZ SZx1.v1 = OZx1.v3 := rfl

/-! ### Proved Properties -/

/-- In a single-state system, the state is always v1 regardless of input. -/
theorem zx1_constant_state (s : SZx1) : s = SZx1.v1 := by
  cases s; rfl

/-- NZ always returns v1 — the system is a trivial fixed point. -/
theorem zx1_nz_fixed (s : SZx1) (i : IZx1) : Zx1.NZ s i = SZx1.v1 := by
  cases s; all_goals cases i; all_goals rfl

/-- The state trajectory is constant: state is always v1 at every time step. -/
theorem zx1_trajectory_constant (s0 : SZx1) (f : ITZ IZx1) (t : Time) :
    FSM.generateStateTrajectory Zx1 s0 f t = SZx1.v1 := by
  induction t with
  | zero => exact zx1_constant_state s0
  | succ n ih => simp [FSM.generateStateTrajectory_succ, ih, zx1_nz_fixed]

/-- The output trajectory is constant: output is always v3. -/
theorem zx1_output_constant (s0 : SZx1) (f : ITZ IZx1) (t : Time) :
    FSM.generateOutputTrajectory Zx1 s0 f t = some OZx1.v3 := by
  rw [FSM.generateOutputTrajectory_eq, zx1_trajectory_constant]

/-- All states in Zx1 are equivalent (trivially, there's only one). -/
theorem zx1_all_states_equiv (s1 s2 : SZx1) : StateEquiv Zx1 s1 s2 := by
  intro f t
  rw [FSM.generateOutputTrajectory_eq, zx1_trajectory_constant]
