import Mbse.Notation
import Mbse.FiniteWymore

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
    FSM.generateStateTrajectory Zx3 s0 f t = s0 := by
  induction t with
  | zero => rfl
  | succ n ih => simp [FSM.generateStateTrajectory_succ, ih, zx3_identity]

/-- The output trajectory is constant and determined solely by the initial state. -/
theorem zx3_output_constant (s0 : SZx3) (f : ITZ IZx3) (t : Time) :
    FSM.generateOutputTrajectory Zx3 s0 f t = Zx3.RZ s0 := by
  rw [FSM.generateOutputTrajectory_eq, zx3_state_constant s0 f t]

/-- Starting from v1 always produces output v5. -/
example (f : ITZ IZx3) (t : Time) :
    FSM.generateOutputTrajectory Zx3 SZx3.v1 f t = OZx3.v5 := by
  rw [zx3_output_constant]
  rfl

/-- Starting from v2 always produces output v6. -/
example (f : ITZ IZx3) (t : Time) :
    FSM.generateOutputTrajectory Zx3 SZx3.v2 f t = OZx3.v6 := by
  rw [zx3_output_constant]
  rfl

/-- States v1 and v2 are NOT equivalent (they produce different outputs). -/
theorem zx3_states_not_equiv : ¬ FSM.StateEquiv Zx3 SZx3.v1 SZx3.v2 := by
  intro h
  have h' := (FSM.stateEquiv_iff Zx3 SZx3.v1 SZx3.v2).mp h
  have := h' (fun _ => IZx3.v3) 0
  rw [zx3_output_constant, zx3_output_constant] at this
  exact absurd this (by decide)

/-- Only state reachable from v1 is v1 (and vice versa for v2).
    The system has two disconnected components. -/
theorem zx3_v2_unreachable_from_v1 : ¬ FSM.Reachable Zx3 SZx3.v1 SZx3.v2 := by
  intro h
  obtain ⟨f, t, ht⟩ := (FSM.reachable_iff Zx3 SZx3.v1 SZx3.v2).mp h
  rw [zx3_state_constant SZx3.v1 f t] at ht
  cases ht
