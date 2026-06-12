import Mbse.Notation
import Mbse.Wymore

/-!
  ## Zx6: Input-Controlled Toggle (XOR-like)

  Input 3 preserves the current state; input 4 swaps it.
  This system behaves like a T flip-flop where input 4 is the toggle signal.
-/

wymore_system Zx6 = (SZx6, IZx6, OZx6, NZx6, RZx6) where
  SZx6 = {1, 2},
  IZx6 = {3, 4},
  OZx6 = {5, 6},
  NZx6 = {((1, 3), 1), ((1, 4), 2), ((2, 3), 2), ((2, 4), 1)},
  RZx6 = {(1, 5), (2, 6)}.

/-! ### Proved Properties -/

/-- Input v3 preserves the state (hold). -/
theorem zx6_hold (s : SZx6) : Zx6.NZ s IZx6.v3 = s := by
  cases s <;> rfl

/-- Input v4 swaps the state (toggle). -/
theorem zx6_toggle (s : SZx6) :
    Zx6.NZ s IZx6.v4 = match s with | .v1 => SZx6.v2 | .v2 => SZx6.v1 := by
  cases s <;> rfl

/-- If the input is always v3 (hold), the state never changes. -/
theorem zx6_constant_hold (s0 : SZx6) (t : Time) :
    generateStateTrajectory Zx6 s0 (fun _ => IZx6.v3) t = s0 := by
  induction t with
  | zero => rfl
  | succ n ih => simp [generateStateTrajectory_succ, ih, zx6_hold]

/-- Both states are reachable from either state (using toggle). -/
theorem zx6_fully_reachable (s0 s : SZx6) : Reachable Zx6 s0 s := by
  cases s0 <;> cases s
  · exact ⟨fun _ => IZx6.v3, 0, rfl⟩
  · exact ⟨fun _ => IZx6.v4, 1, rfl⟩
  · exact ⟨fun _ => IZx6.v4, 1, rfl⟩
  · exact ⟨fun _ => IZx6.v3, 0, rfl⟩
