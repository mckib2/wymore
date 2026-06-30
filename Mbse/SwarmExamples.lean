import Mbse.FiniteWymore
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring

/-!
# UAV swarm case study: mask-based participation

Formal exploration for the INCOSE paper. **Return to Base (RTB):** when battery falls below
threshold, agent becomes inactive in the swarm mask.

Continuous-valued positions in $\mathbb{R}^2$; coverage is projected to a finite cell grid.
-/

namespace Swarm

open FSM

abbrev Cell := Fin 10 × Fin 10

def gridSize : Nat := 10

def regionSize : ℝ := 10

/-- Clamp a natural index into the grid. -/
def clampCellIdx (k : Nat) : Fin gridSize :=
  ⟨min 9 k, Nat.lt_succ_of_le (Nat.min_le_left 9 k)⟩

/-- Project continuous coordinates to a coverage cell (paper: discretization of $R$). -/
noncomputable def locateCell (x y : ℝ) : Cell :=
  let ix := (⌊x⌋).toNat
  let iy := (⌊y⌋).toNat
  (clampCellIdx ix, clampCellIdx iy)

noncomputable def cellCenterX (c : Cell) : ℝ := (c.1.val : ℝ) + (0.5 : ℝ)
noncomputable def cellCenterY (c : Cell) : ℝ := (c.2.val : ℝ) + (0.5 : ℝ)

private theorem nat_floor_center (n : Fin gridSize) :
    ⌊((n.val : ℝ) + (0.5 : ℝ))⌋ = (n.val : ℤ) := by
  rw [Int.floor_natCast_add, show ⌊(0.5 : ℝ)⌋ = (0 : ℤ) by norm_num, add_zero]

private theorem nat_toNat_floor_center (n : Fin gridSize) :
    (⌊((n.val : ℝ) + (0.5 : ℝ))⌋).toNat = n.val := by
  rw [nat_floor_center, Int.toNat_natCast]

theorem locateCell_cellCenter (c : Cell) :
    locateCell (cellCenterX c) (cellCenterY c) = c := by
  apply Prod.ext
  · apply Fin.ext
    simp only [locateCell, clampCellIdx, cellCenterX]
    rw [nat_toNat_floor_center c.1, Nat.min_comm]
    exact Nat.min_eq_left (Nat.le_of_lt_succ c.1.isLt)
  · apply Fin.ext
    simp only [locateCell, clampCellIdx, cellCenterY]
    rw [nat_toNat_floor_center c.2, Nat.min_comm]
    exact Nat.min_eq_left (Nat.le_of_lt_succ c.2.isLt)

structure UavState where
  x : ℝ
  y : ℝ
  psi : ℝ
  v : ℝ
  b : ℝ
  active : Bool

def uavInit : UavState :=
  { x := 0, y := 0, psi := 0, v := 0, b := 10, active := true }

def rtbThreshold : ℝ := 5

noncomputable def rtbTransition (s : UavState) (threshold : ℝ) : UavState :=
  if h : s.b < threshold then { s with active := false } else s

noncomputable def stepUav (s : UavState) : UavState := rtbTransition s rtbThreshold

noncomputable def uav1 : DiscreteSystem UavState Unit Unit :=
  DiscreteSystem.ofTotal (fun s _ => stepUav s) (fun _ => ()) ⟨uavInit⟩

theorem uav1_stateTrajectory_unique (f : ITZW Unit) (g : STZ UavState) (s0 : UavState)
    (h_init : g 0 = s0) (h_valid : IsValidStateTrajectory uav1 f g) :
    ∀ t, g t = generateStateTrajectory uav1 s0 f t :=
  stateTrajectory_unique uav1 f g s0 h_init h_valid

def ActiveAgents {n : Nat} (s : Fin n → UavState) : Finset (Fin n) :=
  Finset.univ.filter fun i => (s i).active

noncomputable def distSq (x1 y1 x2 y2 : ℝ) : ℝ :=
  (x1 - x2) ^ 2 + (y1 - y2) ^ 2

def SwarmSeparation {n : Nat} (s : Fin n → UavState) (d : ℝ) : Prop :=
  ∀ i ∈ ActiveAgents s, ∀ j ∈ ActiveAgents s, i ≠ j →
    distSq (s i).x (s i).y (s j).x (s j).y ≥ d ^ 2

theorem swarmSeparation_trivial_self {n : Nat} (s : Fin n → UavState) (d : ℝ) (i : Fin n)
    (honly : ActiveAgents s = {i}) :
    SwarmSeparation s d := by
  intro i' hi' j' hj' hij
  have hi'eq : i' = i := Finset.mem_singleton.mp (by simpa [honly] using hi')
  have hj'eq : j' = i := Finset.mem_singleton.mp (by simpa [honly] using hj')
  rw [hi'eq, hj'eq] at hij
  exact absurd rfl hij

noncomputable def swarm2Step (s : Fin 2 → UavState) : Fin 2 → UavState :=
  fun i => stepUav (s i)

theorem rtb2_drops_agent0 (s : Fin 2 → UavState)
    (h : (s 0).b < rtbThreshold) :
    ¬ (swarm2Step s 0).active := by
  simp [swarm2Step, stepUav, rtbTransition, h]

theorem swarm2_safety_single_active (s : Fin 2 → UavState) (d : ℝ)
    (honly : ActiveAgents (swarm2Step s) = {1}) :
    SwarmSeparation (swarm2Step s) d :=
  swarmSeparation_trivial_self _ d 1 honly

noncomputable def swarm3Step (s : Fin 3 → UavState) : Fin 3 → UavState :=
  fun i => stepUav (s i)

theorem rtb3_drops_agent (s : Fin 3 → UavState) (k : Fin 3)
    (h : (s k).b < rtbThreshold) :
    ¬ (swarm3Step s k).active := by
  simp [swarm3Step, stepUav, rtbTransition, h]

theorem swarm3_safety_single_active (s : Fin 3 → UavState) (d : ℝ)
    (honly : ActiveAgents (swarm3Step s) = {1}) :
    SwarmSeparation (swarm3Step s) d :=
  swarmSeparation_trivial_self _ d 1 honly

/-- Default initial UAV state (paper: above RTB threshold). -/
abbrev UavState.init := uavInit

end Swarm
