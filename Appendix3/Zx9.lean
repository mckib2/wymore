import Mbse.Notation
import Mbse.FiniteWymore

/-!
  ## Zx9: Three-State System

  A more complex system with 3 states, 3 inputs, and 3 outputs.
  Demonstrates richer transition behavior and interesting reachability properties.

  Transition table:
  | State | Input 3 | Input 4 | Input 8 |
  |-------|---------|---------|---------|
  | 1     | 1       | 1       | 7       |
  | 2     | 1       | 2       | 2       |
  | 7     | 1       | 2       | 7       |

  Readout: 1→5, 2→6, 7→9
-/

wymore_system Zx9 = (SZx9, IZx9, OZx9, NZx9, RZx9) where
  SZx9 = {1, 2, 7},
  IZx9 = {3, 4, 8},
  OZx9 = {5, 6, 9},
  NZx9 = {((1, 3), 1), ((1, 4), 1), ((1, 8), 7), ((2, 3), 1), ((2, 4), 2), ((2, 8), 2), ((7, 3), 1), ((7, 4), 2), ((7, 8), 7)},
  RZx9 = {(1, 5), (2, 6), (7, 9)}.

/-! ### Proved Properties -/

/-- Input v3 always leads to state v1 regardless of current state.
    v3 acts as a "reset" input. -/
theorem zx9_reset (s : SZx9) : Zx9.NZ s IZx9.v3 = SZx9.v1 := by
  cases s <;> rfl

/-- After a reset (input v3), the system is always in v1. -/
theorem zx9_after_reset (s0 : SZx9) (f : ITZ IZx9) (t : Time)
    (hf : f t = IZx9.v3) :
    FSM.generateStateTrajectory Zx9 s0 f (t + 1) = SZx9.v1 := by
  simp [FSM.generateStateTrajectory_succ, hf, zx9_reset]

/-- All three states are reachable from state v1. -/
theorem zx9_v1_reaches_all (s : SZx9) : FSM.Reachable Zx9 SZx9.v1 s := by
  cases s
  · -- v1: already there
    exact ⟨fun _ => IZx9.v3, 0, rfl⟩
  · -- v2: go to v7 via input 8 at step 0, then to v2 via input 4 at step 1
    refine ⟨fun | 0 => IZx9.v8 | _ => IZx9.v4, 2, ?_⟩
    show FSM.generateStateTrajectory Zx9 SZx9.v1 (fun | 0 => IZx9.v8 | _ => IZx9.v4) 2 = SZx9.v2
    simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero]
    native_decide
  · -- v7: go to v7 via input 8
    exact ⟨fun _ => IZx9.v8, 1, by
      show FSM.generateStateTrajectory Zx9 SZx9.v1 (fun _ => IZx9.v8) 1 = SZx9.v7
      simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero]
      native_decide⟩

/-- All states are reachable from any starting state (via reset to v1). -/
theorem zx9_fully_reachable (s0 s : SZx9) : FSM.Reachable Zx9 s0 s := by
  -- First reset to v1 via input v3, then reach target from v1
  cases s
  · exact ⟨fun _ => IZx9.v3, 1, by
      show FSM.generateStateTrajectory Zx9 s0 (fun _ => IZx9.v3) 1 = SZx9.v1
      simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, zx9_reset]⟩
  · refine ⟨fun | 0 => IZx9.v3 | 1 => IZx9.v8 | _ => IZx9.v4, 3, ?_⟩
    show FSM.generateStateTrajectory Zx9 s0 (fun | 0 => IZx9.v3 | 1 => IZx9.v8 | _ => IZx9.v4) 3 = SZx9.v2
    cases s0 <;> simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, zx9_reset] <;> native_decide
  · refine ⟨fun | 0 => IZx9.v3 | _ => IZx9.v8, 2, ?_⟩
    show FSM.generateStateTrajectory Zx9 s0 (fun | 0 => IZx9.v3 | _ => IZx9.v8) 2 = SZx9.v7
    cases s0 <;> simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, zx9_reset] <;> native_decide

/-- Zx9 is a nontrivial system: it has a state-dependent transition, an active transition,
    and more than one possible output. -/
theorem zx9_is_nontrivial : FSM.IsNontrivial Zx9 := by
  unfold FSM.IsNontrivial
  refine ⟨⟨SZx9.v2, SZx9.v1, IZx9.v8, by decide⟩, ⟨SZx9.v1, IZx9.v8, by decide⟩, ?_⟩
  refine Finset.one_lt_card.mpr ⟨OZx9.v5, ?_, OZx9.v6, ?_, by decide⟩
  · simp only [FSM.RNG, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨SZx9.v1, rfl⟩
  · simp only [FSM.RNG, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨SZx9.v2, rfl⟩
