import Mbse.Notation
import Mbse.Wymore

/-!
  ## Zx3: Identity System (State-Preserving)

  Every transition preserves the current state regardless of input.
  The system remembers its initial state forever — it's the discrete-system
  analogue of the identity function. Inputs are completely ignored.
-/

wymore_system Zx3 = (SZx3, IZx3, OZx3, NZx3, RZx3) where
  SZx3 = {1, 2},
  IZx3 = {3, 4},
  OZx3 = {5, 6},
  NZx3 = {((1, 3), 1), ((1, 4), 1), ((2, 3), 2), ((2, 4), 2)},
  RZx3 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- NZ always returns the current state — inputs are ignored. -/
theorem zx3_identity (s : SZx3) (i : IZx3) : Zx3.NZ s i = s := by
  cases s <;> cases i <;> rfl

/-- The state trajectory is constant: the initial state persists forever. -/
theorem zx3_state_constant (s0 : SZx3) (f : ITZ IZx3) (t : Time) :
    generateStateTrajectory Zx3 s0 f t = s0 := by
  induction t with
  | zero => rfl
  | succ n ih => simp [generateStateTrajectory_succ, ih, zx3_identity]

/-- The output trajectory is constant and determined solely by the initial state. -/
theorem zx3_output_constant (s0 : SZx3) (f : ITZ IZx3) (t : Time) :
    generateOutputTrajectory Zx3 s0 f t = Zx3.RZ s0 := by
  simp [generateOutputTrajectory, zx3_state_constant]

/-- Starting from v1 always produces output v5. -/
example (f : ITZ IZx3) (t : Time) :
    generateOutputTrajectory Zx3 SZx3.v1 f t = OZx3.v5 := by
  unfold generateOutputTrajectory
  rw [zx3_state_constant]
  native_decide

/-- Starting from v2 always produces output v6. -/
example (f : ITZ IZx3) (t : Time) :
    generateOutputTrajectory Zx3 SZx3.v2 f t = OZx3.v6 := by
  unfold generateOutputTrajectory
  rw [zx3_state_constant]
  native_decide

/-- States v1 and v2 are NOT equivalent (they produce different outputs). -/
theorem zx3_states_not_equiv : ¬ StateEquiv Zx3 SZx3.v1 SZx3.v2 := by
  intro h
  have := h (fun _ => IZx3.v3) 0
  simp [generateOutputTrajectory, generateStateTrajectory_zero] at this
  -- `this` is now `Zx3.RZ SZx3.v1 = Zx3.RZ SZx3.v2`, which is `OZx3.v5 = OZx3.v6`
  exact absurd this (by decide)

/-- Only state reachable from v1 is v1 (and vice versa for v2).
    The system has two disconnected components. -/
theorem zx3_v2_unreachable_from_v1 : ¬ Reachable Zx3 SZx3.v1 SZx3.v2 := by
  intro ⟨f, t, h⟩
  simp [zx3_state_constant] at h
