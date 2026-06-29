import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx10: Product-Structured System

  A 4-state system with tuple-structured states, inputs, and outputs.
  The state/input/output spaces are structured as pairs, suggesting this
  system is the parallel composition of two simpler subsystems.

  States: (1,1), (1,2), (2,1), (2,2)
  Inputs: (3,3), (3,4), (4,3), (4,4)
  Outputs: (5,5), (5,6), (6,5), (6,6)
-/

wymore_system Zx10 = (SZx10, IZx10, OZx10, NZx10, RZx10) where
  SZx10 = {(1, 1), (1, 2), (2, 1), (2, 2)},
  IZx10 = {(3, 3), (3, 4), (4, 3), (4, 4)},
  OZx10 = {(5, 5), (5, 6), (6, 5), (6, 6)},
  NZx10 = {(((1, 1), (3, 3)), (1, 1)), (((1, 1), (3, 4)), (1, 1)),
           (((1, 1), (4, 3)), (2, 1)), (((1, 1), (4, 4)), (2, 1)),
           (((1, 2), (3, 3)), (1, 1)), (((1, 2), (3, 4)), (1, 2)),
           (((1, 2), (4, 3)), (2, 1)), (((1, 2), (4, 4)), (2, 2)),
           (((2, 1), (3, 3)), (1, 1)), (((2, 1), (3, 4)), (1, 1)),
           (((2, 1), (4, 3)), (1, 1)), (((2, 1), (4, 4)), (1, 1)),
           (((2, 2), (3, 3)), (1, 1)), (((2, 2), (3, 4)), (1, 2)),
           (((2, 2), (4, 3)), (1, 1)), (((2, 2), (4, 4)), (1, 2))},
  RZx10 = {((1, 1), (5, 5)), ((1, 2), (5, 6)), ((2, 1), (6, 5)), ((2, 2), (6, 6))}.

/-! ### Proved Properties -/

/-- The readout function preserves the product structure:
    the first output component depends on the first state component,
    and similarly for the second. -/
example : Zx10.RZ SZx10.v_1_1_ = OZx10.v_5_5_ := rfl
example : Zx10.RZ SZx10.v_1_2_ = OZx10.v_5_6_ := rfl
example : Zx10.RZ SZx10.v_2_1_ = OZx10.v_6_5_ := rfl
example : Zx10.RZ SZx10.v_2_2_ = OZx10.v_6_6_ := rfl

/-- State (1,1) is reachable from any state via input (3,3). -/
theorem zx10_reset_to_v11 (s : SZx10) :
    Zx10.NZ s IZx10.v_3_3_ = SZx10.v_1_1_ := by
  cases s <;> rfl
