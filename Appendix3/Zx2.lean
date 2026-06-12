import Mbse.Notation
import Mbse.Wymore

/-!
  ## Zx2: Absorbing-State System

  All transitions lead to state 1 regardless of current state or input.
  State 1 is an absorbing state — once entered (after one step), the system
  never leaves. This demonstrates convergence behavior.
-/

/--
  [textbook/definition2.5/entity/Zxk]
  [textbook/definition2.5/entity/dsystems]
  [textbook/definition2.5/proof/sz_nonempty]
  [textbook/definition2.5/proof/iz_nonempty]
  [textbook/definition2.5/proof/oz_nonempty]
  [textbook/definition2.5/proof/nz_function]
  [textbook/definition2.5/proof/rz_function]
  Definition and verification of the discrete system Zx2.
-/
wymore_system Zx2 = (SZx2, IZx2, OZx2, NZx2, RZx2) where
  SZx2 = {1, 2},
  IZx2 = {3, 4},
  OZx2 = {5, 6},
  NZx2 = {((1, 3), 1), ((1, 4), 1), ((2, 3), 1), ((2, 4), 1)},
  RZx2 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- Every transition leads to state v1 — the absorbing state. -/
theorem zx2_absorbing (s : SZx2) (i : IZx2) : Zx2.NZ s i = SZx2.v1 := by
  cases s <;> cases i <;> rfl

/-- After exactly one time step, the system is in state v1 regardless of
    the initial state or input. -/
theorem zx2_reaches_v1_at_1 (s0 : SZx2) (f : ITZ IZx2) :
    generateStateTrajectory Zx2 s0 f 1 = SZx2.v1 := by
  simp [generateStateTrajectory_succ, zx2_absorbing]

/-- The system remains in v1 permanently after the first step.
    This is the key stability result: convergence in one step. -/
theorem zx2_stable_after_1 (s0 : SZx2) (f : ITZ IZx2) (t : Time) (ht : t ≥ 1) :
    generateStateTrajectory Zx2 s0 f t = SZx2.v1 := by
  match t, ht with
  | n + 1, _ => simp [generateStateTrajectory_succ, zx2_absorbing]

/-- After one step, the output is always v5 (the readout of the absorbing state). -/
theorem zx2_output_after_1 (s0 : SZx2) (f : ITZ IZx2) (t : Time) (ht : t ≥ 1) :
    generateOutputTrajectory Zx2 s0 f t = OZx2.v5 := by
  unfold generateOutputTrajectory
  rw [zx2_stable_after_1 s0 f t ht]
  rfl

/-- State v1 is reachable from any initial state. -/
theorem zx2_v1_reachable (s0 : SZx2) : Reachable Zx2 s0 SZx2.v1 := by
  exact ⟨fun _ => IZx2.v3, 1, zx2_reaches_v1_at_1 s0 _⟩

/-- Zx2 is finite by definition. -/
theorem zx2_is_finite : IsFinite Zx2 := by
  rfl

/-- Zx2 has order vector (2, 2, 2). -/
theorem zx2_order_vector : HasOrderVector Zx2 2 2 2 := by
  decide

/-- Zx2 is trivial because it fails the nontrivial requirements (no state-dependent transition). -/
theorem zx2_is_trivial : IsTrivial Zx2 := by
  decide

/-- [3, 4] is a test input string for Zx2. -/
def zx2_test_string : STRINGS IZx2 := [IZx2.v3, IZx2.v4]

/-- The length LTH of the test string is 2. -/
theorem zx2_test_string_length : LTH zx2_test_string = 2 := by
  rfl

/-- The test string is a valid nonempty input trajectory. -/
theorem zx2_test_string_trajectory : Nonempty (InputTrajectory IZx2) := by
  exact ⟨⟨zx2_test_string, by decide⟩⟩
