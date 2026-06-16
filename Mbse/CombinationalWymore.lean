import Mbse.Wymore

/-!
# Combinational Wymore Systems

This file implements a parallel line of definitions and theorems based on Wayne Wymore's T3SD,
but specialized to Combinational Logic (the "Single-State Collapse").

In this framework:
- The system's internal state space is forced to be a singleton `{s0}`.
- The next-state transition function is a trivial identity/constant operation.
- The readout function becomes a direct mapping from inputs to outputs (G: IS -> OS).

We compare the expressive and proving power of this combinational logic representation
with the stateful `DiscreteSystem` of Wymore.
-/

/-- The singleton state space containing only `s0`. -/
inductive SingletonState where
  | s0 : SingletonState
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SingletonState where
  elems := {SingletonState.s0}
  complete := by intro x; cases x; exact Finset.mem_singleton_self SingletonState.s0

namespace Combinational

/--
  A combinational system is a system with no memory where the output is a direct
  mapping of the input.
-/
structure CombinationalSystem (IZ : Type) (OZ : Type) where
  /-- Proof that the input space is finite -/
  iz_finite : Fintype IZ

  /-- Proof that the output space is finite -/
  oz_finite : Fintype OZ

  /-- The combinational readout function mapping inputs directly to outputs -/
  RZ : IZ → OZ

variable {IZ OZ : Type}

/-- [textbook/definition2.4/implication/closed_system] A combinational system is closed if both its input and output spaces are empty. -/
def IsClosed (_C : CombinationalSystem IZ OZ) : Prop :=
  IsEmpty IZ ∧ IsEmpty OZ

/-- [textbook/definition2.4/implication/open_system] A combinational system is open if neither its input nor output spaces are empty. -/
def IsOpen (_C : CombinationalSystem IZ OZ) : Prop :=
  Nonempty IZ ∧ Nonempty OZ


/--
  [textbook/definition2.11/definition/finite_system]
  A combinational system is finite if and only if IZ and OZ are finite sets (its state space is
  the singleton, hence trivially finite). `combinationalSystem_isFinite` proves every
  combinational system satisfies this.
-/
def IsFinite (_C : CombinationalSystem IZ OZ) : Prop :=
  Finite IZ ∧ Finite OZ

/-- Every `CombinationalSystem` is finite (its input/output spaces carry `Fintype`). -/
theorem combinationalSystem_isFinite (C : CombinationalSystem IZ OZ) : IsFinite C :=
  have := C.iz_finite
  have := C.oz_finite
  ⟨Finite.of_fintype IZ, Finite.of_fintype OZ⟩

/--
  [textbook/definition2.11/definition/order_vector]
  The combinational system C is finite with order vector (1, m, n) if and only if
  1 = #ST, m = #IZ, n = #OZ.
-/
def HasOrderVector (C : CombinationalSystem IZ OZ) (k m n : Nat) : Prop :=
  have : Fintype IZ := C.iz_finite
  have : Fintype OZ := C.oz_finite
  k = 1 ∧ Fintype.card IZ = m ∧ Fintype.card OZ = n ∧
  m ≥ 1 ∧ n ≥ 1

/--
  [textbook/definition2.14/definition/nontrivial_system]
  A combinational system is nontrivial if and only if its readout has varying outputs
  (the size of the range of the readout function C.RZ is greater than 1).
-/
def IsNontrivial (C : CombinationalSystem IZ OZ) : Prop :=
  have : Fintype IZ := C.iz_finite
  have : DecidableEq OZ := Classical.decEq OZ
  Finset.card (RNG C.RZ) > 1

/--
  [textbook/definition2.14/implication/trivial_system]
  A combinational system is trivial if and only if it is not nontrivial.
-/
def IsTrivial (C : CombinationalSystem IZ OZ) : Prop :=
  ¬ IsNontrivial C

/-- Generates the state trajectory for a combinational system (always constant s0). -/
def generateStateTrajectory (_C : CombinationalSystem IZ OZ) (_s_init : SingletonState) (_f : ITZ IZ) : STZ SingletonState :=
  fun _ => SingletonState.s0

/-- Generates the output trajectory for a combinational system (instantaneous readout). -/
def generateOutputTrajectory (C : CombinationalSystem IZ OZ) (f : ITZ IZ) : OTZ OZ :=
  fun t => C.RZ (f t)

/-- Predicate for a valid state trajectory. -/
def IsValidStateTrajectory (_C : CombinationalSystem IZ OZ) (_f : ITZ IZ) (g : STZ SingletonState) : Prop :=
  ∀ t : Time, g t = SingletonState.s0

/-- Predicate for a valid output trajectory. -/
def IsValidOutputTrajectory (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (h : OTZ OZ) : Prop :=
  ∀ t : Time, h t = C.RZ (f t)

/-! ## Simp Lemmas -/

@[simp]
theorem generateStateTrajectory_val (C : CombinationalSystem IZ OZ) (s_init : SingletonState) (f : ITZ IZ) (t : Time) :
    generateStateTrajectory C s_init f t = SingletonState.s0 := rfl

@[simp]
theorem generateOutputTrajectory_val (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory C f t = C.RZ (f t) := rfl

/-! ## Core Soundness and Uniqueness Theorems -/

theorem generateStateTrajectory_valid (C : CombinationalSystem IZ OZ) (s_init : SingletonState) (f : ITZ IZ) :
    IsValidStateTrajectory C f (generateStateTrajectory C s_init f) := by
  intro t
  rfl

theorem generateOutputTrajectory_valid (C : CombinationalSystem IZ OZ) (f : ITZ IZ) :
    IsValidOutputTrajectory C f (generateOutputTrajectory C f) := by
  intro t
  rfl

theorem stateTrajectory_unique (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (g : STZ SingletonState) (s_init : SingletonState)
    (h_valid : IsValidStateTrajectory C f g) :
    g = generateStateTrajectory C s_init f := by
  funext t
  exact h_valid t

theorem outputTrajectory_unique (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (h : OTZ OZ)
    (h_valid : IsValidOutputTrajectory C f h) :
    h = generateOutputTrajectory C f := by
  funext t
  exact h_valid t

/-! ## System-Theoretic Properties -/

/-- Reachability in a combinational system, mirroring the base file: `s` is reachable from
    `s_init` if some input trajectory drives the (singleton) state trajectory to `s` at some time. -/
def Reachable (C : CombinationalSystem IZ OZ) (s_init s : SingletonState) : Prop :=
  ∃ (f : ITZ IZ) (t : Time), generateStateTrajectory C s_init f t = s

theorem reachable_always (C : CombinationalSystem IZ OZ) [Inhabited IZ] (s_init s : SingletonState) :
    Reachable C s_init s := by
  refine ⟨fun _ => default, 0, ?_⟩
  cases s
  rfl

theorem reachable_self (C : CombinationalSystem IZ OZ) [Inhabited IZ] (s_init : SingletonState) :
    Reachable C s_init s_init :=
  reachable_always C s_init s_init

/-- State equivalence in a combinational system. Because a combinational system's output never
    depends on the (single) internal state, observational equivalence is degenerate, so we use
    the finest sensible relation: equality of states. This is a genuine equivalence relation
    (not a vacuous `True`), and `stateEquiv_always` shows every pair is equivalent because the
    state space is a singleton. -/
def StateEquiv (_C : CombinationalSystem IZ OZ) (s1 s2 : SingletonState) : Prop :=
  s1 = s2

theorem stateEquiv_always (C : CombinationalSystem IZ OZ) (s1 s2 : SingletonState) :
    StateEquiv C s1 s2 := by
  cases s1
  cases s2
  rfl

theorem stateEquiv_refl (C : CombinationalSystem IZ OZ) (s : SingletonState) :
    StateEquiv C s s :=
  rfl

theorem stateEquiv_symm (C : CombinationalSystem IZ OZ) (s1 s2 : SingletonState)
    (h : StateEquiv C s1 s2) : StateEquiv C s2 s1 :=
  h.symm

theorem stateEquiv_trans (C : CombinationalSystem IZ OZ) (s1 s2 s3 : SingletonState)
    (h12 : StateEquiv C s1 s2) (h23 : StateEquiv C s2 s3) :
    StateEquiv C s1 s3 :=
  h12.trans h23

/-! ## Morphisms -/

/-- A morphism of combinational systems maps inputs and outputs, preserving readout. -/
structure SystemMorphism
    {IZ1 OZ1 : Type} {IZ2 OZ2 : Type}
    (C1 : CombinationalSystem IZ1 OZ1)
    (C2 : CombinationalSystem IZ2 OZ2) where
  φI : IZ1 → IZ2
  φO : OZ1 → OZ2
  preserves_readout : ∀ i, φO (C1.RZ i) = C2.RZ (φI i)

/-- Proving that combinational morphisms preserve output trajectories is direct (no induction needed). -/
theorem morphism_preserves_output_trajectory
    {IZ1 OZ1 IZ2 OZ2 : Type}
    {C1 : CombinationalSystem IZ1 OZ1}
    {C2 : CombinationalSystem IZ2 OZ2}
    (m : SystemMorphism C1 C2) (f : ITZ IZ1) :
    ∀ t, m.φO (generateOutputTrajectory C1 f t) =
         generateOutputTrajectory C2 (m.φI ∘ f) t := by
  intro t
  unfold generateOutputTrajectory
  dsimp only [Function.comp]
  exact m.preserves_readout (f t)

/-- A combinational morphism preserves state trajectories. There is no state map (`φS`) because
    both systems share the singleton state space, so the state trajectory of `C1` coincides with
    that of `C2` under the mapped inputs. This mirrors the base-file statement shape rather than
    hardcoding `s0` on the left-hand side. -/
theorem morphism_preserves_state_trajectory
    {IZ1 OZ1 IZ2 OZ2 : Type}
    {C1 : CombinationalSystem IZ1 OZ1}
    {C2 : CombinationalSystem IZ2 OZ2}
    (m : SystemMorphism C1 C2) (s_init : SingletonState) (f : ITZ IZ1) :
    ∀ t, generateStateTrajectory C1 s_init f t =
         generateStateTrajectory C2 SingletonState.s0 (m.φI ∘ f) t := by
  intro t
  rfl


/-! ## Time Invariance and stateless properties -/

theorem stateTrajectory_time_invariance
    (C : CombinationalSystem IZ OZ) (s_init : SingletonState) (f : ITZ IZ) (s t : Time) :
    generateStateTrajectory C (generateStateTrajectory C s_init f s) (translate f s) t =
    generateStateTrajectory C s_init f (s + t) := by
  rfl

theorem outputTrajectory_time_invariance
    (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (s t : Time) :
    generateOutputTrajectory C (translate f s) t =
    generateOutputTrajectory C f (s + t) := by
  unfold generateOutputTrajectory translate
  congr 1
  rw [Nat.add_comm s t]

/-! ## Instantaneous / Stateless Behavior -/

/-- The output of a combinational system at time `t` depends only on the input at time `t`. -/
theorem outputTrajectory_instantaneous
    (C : CombinationalSystem IZ OZ) (f g : ITZ IZ) (t : Time)
    (h_agree : f t = g t) :
    generateOutputTrajectory C f t = generateOutputTrajectory C g t := by
  simp only [generateOutputTrajectory_val, h_agree]

/-- The standard nonanticipatory property holds trivially for combinational systems. -/
theorem outputTrajectory_nonanticipatory
    (C : CombinationalSystem IZ OZ) (f g : ITZ IZ) (t : Time)
    (h_agree : ∀ i ≤ t, f i = g i) :
    generateOutputTrajectory C f t = generateOutputTrajectory C g t := by
  apply outputTrajectory_instantaneous
  exact h_agree t (le_refl t)

/-! ## Projection and Ports -/

/-- Readout for the `op`-th output port of a combinational system. -/
def portReadout {OutPort : Type} {OutPortVal : OutPort → Type}
    (C : CombinationalSystem IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : IZ → OutPortVal op :=
  fun i => PJN op (C.RZ i)

/-- Output trajectory of the `op`-th port of a combinational system. -/
def portOutputTrajectory {OutPort : Type} {OutPortVal : OutPort → Type}
    (ot : OTZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : Time → OutPortVal op :=
  fun t => PJN op (ot t)

/-! ## Parameterization -/

/-- A combinational system parameterization F maps a parameter type `P` to a `CombinationalSystem`. -/
def CombinationalSystemParameterization (P : Type u) (IZ OZ : P → Type) : Type u :=
  (p : P) → CombinationalSystem (IZ p) (OZ p)

/-- Instance of a combinational parameterization. -/
def parameterInstance {P : Type u} {IZ OZ : P → Type}
    (F : CombinationalSystemParameterization P IZ OZ) (r : P) : CombinationalSystem (IZ r) (OZ r) :=
  F r

/-! ## fccsy (Function Computation Combinational System) -/

/--
  The combinational version of a function computation system.
  Directly evaluates F on the input with zero delay.
-/
def fccsy {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ] : CombinationalSystem IZ OZ where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := F

/-- fccsy computes the function immediately (zero delay). -/
theorem fccsy_output_instantaneous {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ]
    (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory (fccsy F) f t = F (f t) := by
  rfl

/-! ## Parallel (Conjunctive) Composition -/

/-- A vector of combinational systems with port-based interfaces. -/
structure PortCombinationalSystemVector (n : Nat) where
  Port : Fin n → Type
  PortVal : (i : Fin n) → Port i → Type
  OutPort : Fin n → Type
  OutPortVal : (i : Fin n) → OutPort i → Type
  C : (i : Fin n) → CombinationalSystem ((p : Port i) → PortVal i p) ((op : OutPort i) → OutPortVal i op)
  Port_finite : (i : Fin n) → Fintype (Port i)
  PortVal_finite : (i : Fin n) → (p : Port i) → Fintype (PortVal i p)
  OutPort_finite : (i : Fin n) → Fintype (OutPort i)
  OutPortVal_finite : (i : Fin n) → (op : OutPort i) → Fintype (OutPortVal i op)
  Port_decidable : (i : Fin n) → DecidableEq (Port i)
  OutPort_decidable : (i : Fin n) → DecidableEq (OutPort i)
  distinct : ∀ (i j : Fin n), i ≠ j → ¬ HEq (C i) (C j)

/-- Parallel composition of combinational systems. -/
def ccsy {n : Nat} (VCS : PortCombinationalSystemVector n) :
    CombinationalSystem
      ((ip : Σ (i : Fin n), VCS.Port i) → VCS.PortVal ip.1 ip.2)
      ((op : Σ (i : Fin n), VCS.OutPort i) → VCS.OutPortVal op.1 op.2) where
  iz_finite := by
    haveI : ∀ i, Fintype (VCS.Port i) := VCS.Port_finite
    haveI : ∀ i, DecidableEq (VCS.Port i) := VCS.Port_decidable
    haveI : ∀ (ip : Σ i, VCS.Port i), Fintype (VCS.PortVal ip.fst ip.snd) := fun ip => VCS.PortVal_finite ip.fst ip.snd
    infer_instance
  oz_finite := by
    haveI : ∀ i, Fintype (VCS.OutPort i) := VCS.OutPort_finite
    haveI : ∀ i, DecidableEq (VCS.OutPort i) := VCS.OutPort_decidable
    haveI : ∀ (op : Σ i, VCS.OutPort i), Fintype (VCS.OutPortVal op.fst op.snd) := fun op => VCS.OutPortVal_finite op.fst op.snd
    infer_instance
  RZ := fun p op => (VCS.C op.1).RZ (fun port => p ⟨op.1, port⟩) op.2

/-- Output trajectory of parallel composition evaluated at port `B'` of system `i`
    is identical to the output trajectory of components under projected input.
    Proven strictly by definition (`rfl`). -/
theorem ccsy_output_trajectory {n : Nat} (VCS : PortCombinationalSystemVector n)
    (f : ITZ ((ip : Σ i, VCS.Port i) → VCS.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) (B' : VCS.OutPort i) :
    generateOutputTrajectory (ccsy VCS) f t ⟨i, B'⟩ =
    generateOutputTrajectory (VCS.C i) (fun t port => f t ⟨i, port⟩) t B' := by
  rfl

/-- ccsy defines a valid combinational system parameterization. -/
def ccsy_parameterization (n : Nat) :
    CombinationalSystemParameterization (PortCombinationalSystemVector n)
      (fun VCS => (ip : Σ i, VCS.Port i) → VCS.PortVal ip.1 ip.2)
      (fun VCS => (op : Σ i, VCS.OutPort i) → VCS.OutPortVal op.1 op.2) :=
  fun VCS => ccsy VCS

end Combinational

/-! ## State Space Limitation Analysis -/

/--
  Theorem: Any Moore-style `DiscreteSystem` restricted to `SingletonState` produces a
  constant output trajectory, completely independent of its input trajectory.
  This highlights the fundamental representation limitation of stateful systems with
  collapsed states.
-/
theorem singleton_state_discrete_system_is_constant {IZ OZ : Type}
    (Z : DiscreteSystem SingletonState IZ OZ) (s_init : SingletonState) (f g : ITZ IZ) (t : Time) :
    generateOutputTrajectory Z s_init f t = generateOutputTrajectory Z s_init g t := by
  unfold generateOutputTrajectory
  cases (generateStateTrajectory Z s_init f t)
  cases (generateStateTrajectory Z s_init g t)
  rfl

/--
  To model a `Combinational.CombinationalSystem` using Wymore's `DiscreteSystem` without losing the
  input dependency, we must introduce a 1-step delay and use `IZ` itself as the state space.
-/
def combinationalToDelaySystem {IZ OZ : Type} (C : Combinational.CombinationalSystem IZ OZ) [Inhabited IZ] : DiscreteSystem IZ IZ OZ where
  sz_nonempty := ⟨default⟩
  sz_finite := C.iz_finite
  iz_finite := C.iz_finite
  oz_finite := C.oz_finite
  NZ := fun _x p => p
  RZ := fun x => C.RZ x

/--
  The output of the delayed system at time `t + 1` corresponds to the combinational output
  for input at time `t`.
-/
theorem delay_system_output {IZ OZ : Type} [Inhabited IZ] (C : Combinational.CombinationalSystem IZ OZ)
    (x : IZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory (combinationalToDelaySystem C) x f (t + 1) = C.RZ (f t) := by
  rfl
