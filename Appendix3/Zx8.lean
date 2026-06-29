import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx8: Asymmetric Transition System (Variant)

  From state 1: both inputs stay at state 1.
  From state 2: input 3 goes to state 1, input 4 stays at state 2.
  State 1 is absorbing once reached; state 2 can only escape via input 3.
-/

wymore_system Zx8 = (SZx8, IZx8, OZx8, NZx8, RZx8) where
  SZx8 = {1, 2},
  IZx8 = {3, 4},
  OZx8 = {5, 6},
  NZx8 = {((1, 3), 1), ((1, 4), 1), ((2, 3), 1), ((2, 4), 2)},
  RZx8 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- State v1 is absorbing: once in v1, you stay forever. -/
theorem zx8_v1_absorbing (i : IZx8) : Zx8.NZ SZx8.v1 i = SZx8.v1 := by
  cases i <;> rfl

/-- Starting from v1, the state trajectory is constant. -/
theorem zx8_v1_constant (f : ITZ IZx8) (t : Time) :
    FSM.generateStateTrajectory Zx8 SZx8.v1 f t = SZx8.v1 := by
  induction t with
  | zero => rfl
  | succ n ih => simp [FSM.generateStateTrajectory_succ, ih, zx8_v1_absorbing]

/-- State v2 is NOT reachable from v1 — the two-state system has
    a one-way escape from v2 to v1 but not the reverse. -/
theorem zx8_v2_unreachable_from_v1 : ¬ FSM.Reachable Zx8 SZx8.v1 SZx8.v2 := by
  intro h
  obtain ⟨f, t, ht⟩ := (FSM.reachable_iff Zx8 SZx8.v1 SZx8.v2).mp h
  rw [zx8_v1_constant f t] at ht
  cases ht
