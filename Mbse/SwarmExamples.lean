import Mbse.FiniteWymore

/-!
# UAV swarm case study: mask-based participation

Formal exploration for the INCOSE paper. **Return to Base (RTB):** when battery falls below
threshold, agent becomes inactive in the swarm mask.

- **N=1:** `DiscreteSystem` + trajectory uniqueness.
- **N=2, N=3:** product-state steps with `ActiveAgents` / `SwarmSeparation` (Finset quantifiers).

Finite grid coordinates for tractable proofs; paper uses $\mathbb{R}$.
-/

namespace Swarm

open FSM

abbrev UavState := Fin 10 × Fin 10 × Fin 11 × Bool

namespace UavState

def mk (x y : Fin 10) (b : Fin 11) (active : Bool) : UavState := (x, y, b, active)
def x (s : UavState) : Fin 10 := s.1
def y (s : UavState) : Fin 10 := s.2.1
def b (s : UavState) : Fin 11 := s.2.2.1
def active (s : UavState) : Bool := s.2.2.2
def init : UavState := mk 0 0 ⟨5, by decide⟩ true

end UavState

def rtbThreshold : Nat := 5

def rtbTransition (s : UavState) (threshold : Nat) : UavState :=
  if (UavState.b s).val < threshold then
    UavState.mk (UavState.x s) (UavState.y s) (UavState.b s) false
  else s

def stepUav (s : UavState) : UavState := rtbTransition s rtbThreshold

def uav1 : DiscreteSystem UavState Unit Unit :=
  DiscreteSystem.ofTotal (fun s _ => stepUav s) (fun _ => ()) ⟨UavState.init⟩

theorem uav1_stateTrajectory_unique (f : ITZW Unit) (g : STZ UavState) (s0 : UavState)
    (h_init : g 0 = s0) (h_valid : IsValidStateTrajectory uav1 f g) :
    ∀ t, g t = generateStateTrajectory uav1 s0 f t :=
  stateTrajectory_unique uav1 f g s0 h_init h_valid

def ActiveAgents {n : Nat} (s : Fin n → UavState) : Finset (Fin n) :=
  Finset.univ.filter fun i => UavState.active (s i)

def gridDist (x1 y1 x2 y2 : Fin 10) : Nat :=
  Int.natAbs ((x1.val : Int) - x2.val) + Int.natAbs ((y1.val : Int) - y2.val)

def SwarmSeparation {n : Nat} (s : Fin n → UavState) (d : Nat) : Prop :=
  ∀ i ∈ ActiveAgents s, ∀ j ∈ ActiveAgents s, i ≠ j →
    gridDist (UavState.x (s i)) (UavState.y (s i)) (UavState.x (s j)) (UavState.y (s j)) ≥ d

theorem swarmSeparation_trivial_self {n : Nat} (s : Fin n → UavState) (d : Nat) (i : Fin n)
    (honly : ActiveAgents s = {i}) :
    SwarmSeparation s d := by
  intro i' hi' j' hj' hij
  have hi'eq : i' = i := Finset.mem_singleton.mp (by simpa [honly] using hi')
  have hj'eq : j' = i := Finset.mem_singleton.mp (by simpa [honly] using hj')
  rw [hi'eq, hj'eq] at hij
  exact absurd rfl hij

def swarm2Step (s : Fin 2 → UavState) : Fin 2 → UavState :=
  fun i => stepUav (s i)

theorem rtb2_drops_agent0 (s : Fin 2 → UavState)
    (h : (UavState.b (s 0)).val < rtbThreshold) :
    ¬ UavState.active (swarm2Step s 0) := by
  have hdef : swarm2Step s 0 =
      UavState.mk (UavState.x (s 0)) (UavState.y (s 0)) (UavState.b (s 0)) false := by
    simp [swarm2Step, stepUav, rtbTransition, h]
  rw [hdef, UavState.active]
  intro h
  cases h

theorem swarm2_safety_single_active (s : Fin 2 → UavState) (d : Nat)
    (honly : ActiveAgents (swarm2Step s) = {1}) :
    SwarmSeparation (swarm2Step s) d :=
  swarmSeparation_trivial_self _ d 1 honly

def swarm3Step (s : Fin 3 → UavState) : Fin 3 → UavState :=
  fun i => stepUav (s i)

theorem rtb3_drops_agent (s : Fin 3 → UavState) (k : Fin 3)
    (h : (UavState.b (s k)).val < rtbThreshold) :
    ¬ UavState.active (swarm3Step s k) := by
  have hdef : swarm3Step s k =
      UavState.mk (UavState.x (s k)) (UavState.y (s k)) (UavState.b (s k)) false := by
    simp [swarm3Step, stepUav, rtbTransition, h]
  rw [hdef, UavState.active]
  intro h
  cases h

theorem swarm3_safety_single_active (s : Fin 3 → UavState) (d : Nat)
    (honly : ActiveAgents (swarm3Step s) = {1}) :
    SwarmSeparation (swarm3Step s) d :=
  swarmSeparation_trivial_self _ d 1 honly

end Swarm
