import Mbse.Notation
import Mbse.Wymore

/-!
  ## Zx7: Asymmetric Transition System

  From state 1: input 3 stays, input 4 goes to state 2.
  From state 2: both inputs go to state 1.
  State 1 is an attractor for state 2 — once you leave state 1 (via input 4),
  you return in exactly one step.
-/

wymore_system Zx7 = (SZx7, IZx7, OZx7, NZx7, RZx7) where
  SZx7 = {1, 2},
  IZx7 = {3, 4},
  OZx7 = {5, 6},
  NZx7 = {((1, 3), 1), ((1, 4), 2), ((2, 3), 1), ((2, 4), 1)},
  RZx7 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- From state v2, any input returns to v1. State v2 is transient. -/
theorem zx7_v2_returns (i : IZx7) : Zx7.NZ SZx7.v2 i = SZx7.v1 := by
  cases i <;> rfl

/-- Both states are reachable from v1. -/
theorem zx7_reachable_from_v1 (s : SZx7) : Reachable Zx7 SZx7.v1 s := by
  cases s
  · exact ⟨fun _ => IZx7.v3, 0, rfl⟩
  · exact ⟨fun _ => IZx7.v4, 1, rfl⟩
