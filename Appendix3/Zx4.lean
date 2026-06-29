import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx4: Toggle System (Alternating States)

  Every transition maps to the opposite state: 1→2 and 2→1, regardless
  of input. The system oscillates between the two states on every step.
-/

wymore_system Zx4 = (SZx4, IZx4, OZx4, NZx4, RZx4) where
  SZx4 = {1, 2},
  IZx4 = {3, 4},
  OZx4 = {5, 6},
  NZx4 = {((1, 3), 2), ((1, 4), 2), ((2, 3), 1), ((2, 4), 1)},
  RZx4 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- NZ always swaps the state: v1 ↔ v2. -/
theorem zx4_toggle (s : SZx4) (i : IZx4) :
    Zx4.NZ s i = match s with | .v1 => SZx4.v2 | .v2 => SZx4.v1 := by
  cases s <;> cases i <;> rfl

/-- Applying NZ twice returns to the original state — the toggle is an involution. -/
theorem zx4_double_toggle (s : SZx4) (i1 i2 : IZx4) :
    Zx4.NZ (Zx4.NZ s i1) i2 = s := by
  cases s <;> cases i1 <;> cases i2 <;> rfl

/-- At even times the system is in the initial state; at odd times, the opposite. -/
theorem zx4_even_returns (s0 : SZx4) (f : ITZ IZx4) (n : Nat) :
    FSM.generateStateTrajectory Zx4 s0 f (2 * n) = s0 := by
  induction n with
  | zero => simp [FSM.generateStateTrajectory_zero]
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h1, FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_succ, ih, zx4_double_toggle]

/-- Both states are reachable from either starting state. -/
theorem zx4_fully_reachable (s0 s : SZx4) : FSM.Reachable Zx4 s0 s := by
  cases s0 <;> cases s
  · exact ⟨fun _ => IZx4.v3, 0, rfl⟩
  · exact ⟨fun _ => IZx4.v3, 1, rfl⟩
  · exact ⟨fun _ => IZx4.v3, 1, rfl⟩
  · exact ⟨fun _ => IZx4.v3, 0, rfl⟩
