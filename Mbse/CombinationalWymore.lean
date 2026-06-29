import Mbse.Wymore
import Mbse.FiniteWymore

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

## Dual API

Combinational logic is exposed on two layers, both preserved intentionally:

1. **Canonical zero-delay layer** (`CombinationalSystem`, `generateOutputTrajectory`): readout is
   `RZ : IZ → OZ` with output at time `t` equal to `C.RZ (f t)` (`combinational_zero_delay`).
2. **Moore embedding layer** (`combinationalToDelaySystem`): a base `DiscreteSystem` with 1-step delay
   whose output at `t + 1` matches the canonical output at `t` (`delay_system_matches_combinational_trajectory`).
   Uniqueness on the delay side reuses base Wymore (`delaySystem_outputTrajectory_unique`).

## Encoding options (zero-delay I/O)

| Option | Encoding | Input-dependent output at time `t`? |
|---|---|---|
| (A) `CombinationalSystem` | Mealy readout `RZ : IZ → OZ` | Yes: `C.RZ (f t)` |
| (B) `combinationalToDelaySystem` | Moore with state `IZ`, 1-step lag | At `t + 1` only |
| (C) Moore on `SingletonState` | `RZ : SingletonState → OZ` | **No** — output independent of input (`zeroDelayMooreOnSingleton_impossible`) |
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

/-- A concrete closed combinational system: empty input and output.
    Unlike base `DiscreteSystem` (`not_isClosed`), closed systems are representable here
    because readout is `IZ → OZ` with no forced nonempty output space. -/
def closedSystem : CombinationalSystem Empty Empty where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := fun e => e.elim

theorem closedSystem_isClosed : IsClosed closedSystem :=
  ⟨inferInstance, inferInstance⟩

/-- Closed (empty-input, empty-output) combinational systems are constructible.
    Contrast `not_isClosed`, which proves no base `DiscreteSystem` can be closed. -/
theorem exists_closed_combinationalSystem : ∃ (C : CombinationalSystem Empty Empty), IsClosed C :=
  ⟨closedSystem, closedSystem_isClosed⟩

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
  [textbook/definition2.14/definition/nontrivial_system|partial]
  A combinational system is nontrivial if and only if its readout has varying outputs
  (the size of the range of the readout function C.RZ is greater than 1).
  Partial: Def 2.14 also requires state-dependent and active transitions; those clauses
  are vacuous or inapplicable on the singleton state space and are intentionally omitted.
-/
def IsNontrivial (C : CombinationalSystem IZ OZ) : Prop :=
  Finset.card (@FSM.RNG IZ OZ C.iz_finite (Classical.decEq OZ) C.RZ) > 1

/--
  [textbook/definition2.14/implication/trivial_system]
  A combinational system is trivial if and only if it is not nontrivial.
-/
def IsTrivial (C : CombinationalSystem IZ OZ) : Prop :=
  ¬ IsNontrivial C

/-- [textbook/definition2.27/definition/state_trajectory_recurrence]
    Generates the state trajectory for a combinational system (always constant s0). -/
def generateStateTrajectory (_C : CombinationalSystem IZ OZ) (_s_init : SingletonState) (_f : ITZ IZ) : STZ SingletonState :=
  fun _ => SingletonState.s0

/-- [textbook/definition2.30/definition/output_trajectory_composition]
    Generates the output trajectory for a combinational system (instantaneous readout). -/
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

/-- Direct proof on the singleton state space; state is constant regardless of input. -/
theorem stateTrajectory_unique (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (g : STZ SingletonState) (s_init : SingletonState)
    (h_valid : IsValidStateTrajectory C f g) :
    g = generateStateTrajectory C s_init f := by
  funext t
  exact h_valid t

/-- Direct proof; also obtainable via delay embedding (see `delaySystem_outputTrajectory_unique`). -/
theorem outputTrajectory_unique (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (h : OTZ OZ)
    (h_valid : IsValidOutputTrajectory C f h) :
    h = generateOutputTrajectory C f := by
  funext t
  exact h_valid t

/-! ## System-Theoretic Properties -/

/-- [textbook/definition2.51/definition/reachable]
    Reachability in a combinational system, mirroring the base file: `s` is reachable from
    `s_init` if some input trajectory drives the (singleton) state trajectory to `s` at some time.
    Degenerate: on a singleton state space every state is reachable from every state at time 0
    (`reachable_always`); this predicate carries no distinguishing information. -/
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

/-- State equivalence in a combinational system: syntactic equality on the singleton state space.
    This is **not** the base Wymore observational `StateEquiv` (identical output trajectories under
    all inputs). For behavioral equivalence of combinational systems, use `InputObsEquiv`. -/
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

/-! ## Behavioral (input-output) equivalence -/

/-- Two combinational systems are behaviorally equivalent if they agree on every input.
    This is the meaningful observational notion for zero-memory systems; base `StateEquiv`
    on `SingletonState` is degenerate (all states equal). -/
def InputObsEquiv (C1 C2 : CombinationalSystem IZ OZ) : Prop :=
  ∀ i, C1.RZ i = C2.RZ i

theorem inputObsEquiv_refl (C : CombinationalSystem IZ OZ) : InputObsEquiv C C :=
  fun _ => rfl

theorem inputObsEquiv_symm (C1 C2 : CombinationalSystem IZ OZ)
    (h : InputObsEquiv C1 C2) : InputObsEquiv C2 C1 :=
  fun i => (h i).symm

theorem inputObsEquiv_trans (C1 C2 C3 : CombinationalSystem IZ OZ)
    (h12 : InputObsEquiv C1 C2) (h23 : InputObsEquiv C2 C3) : InputObsEquiv C1 C3 :=
  fun i => (h12 i).trans (h23 i)

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

/-! ## System experiments -/

/--
  [textbook/definition2.33/definition/system_experiments]
  System experiments for combinational systems: input trajectory, initial (singleton) state, and time.
  On the singleton state space, experiments reduce to `(f, s0, t)` with output `C.RZ (f t)`.
-/
abbrev CombinationalEXZ (IZ : Type) := EXZ SingletonState IZ

/--
  Run a combinational system experiment: output is the instantaneous readout at the experiment time.
  An experiment `e = (f, s0, t)` produces `C.RZ (f t)`.
-/
def runExperiment (C : CombinationalSystem IZ OZ) (e : CombinationalEXZ IZ) : OZ :=
  C.RZ (e.1 e.2.2)

/-- Experiment output equals the generated output trajectory at the experiment time. -/
theorem experiment_output (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (s_init : SingletonState) (t : Time) :
    runExperiment C (f, s_init, t) = generateOutputTrajectory C f t := rfl

/-- Experiment state trajectory is constant (initial state is irrelevant on a singleton). -/
theorem experiment_state (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (s_init : SingletonState) (t : Time) :
    generateStateTrajectory C s_init f t = s_init := by
  cases s_init
  rfl

/-- All initial states yield the same experiment output (singleton state space). -/
theorem experiment_initial_state_irrelevant (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (s_init s_init' : SingletonState) (t : Time) :
    runExperiment C (f, s_init, t) = runExperiment C (f, s_init', t) := by
  cases s_init
  cases s_init'
  rfl

/-! ## Projection and Ports -/

/--
  [textbook/definition2.55/definition/input_ports]
  Input port index set for combinational systems (thin wrapper over base `IPZ`).
-/
abbrev IPZ (Port : Type) := _root_.IPZ Port

/--
  [textbook/definition2.59/definition/input_port_structure]
  Input port structure for combinational systems (thin wrapper over base `ISZ`).
-/
abbrev ISZ (Port : Type) (PortVal : Port → Type) := _root_.ISZ Port PortVal

/--
  [textbook/definition2.55/definition/port_trajectory]
  The `p`-th input port trajectory for combinational (Mealy) input trajectories.
-/
def portTrajectory {Port : Type} {PortVal : Port → Type}
    (f : ITZ ((p : Port) → PortVal p)) (p : Port) : Time → PortVal p :=
  _root_.portTrajectory f p

@[simp]
theorem portTrajectory_at_time {Port : Type} {PortVal : Port → Type}
    (f : ITZ ((p : Port) → PortVal p)) (p : Port) (t : Time) :
    portTrajectory f p t = f t p := rfl

/-- Readout for the `op`-th output port of a combinational system. -/
def portReadout {OutPort : Type} {OutPortVal : OutPort → Type}
    (C : CombinationalSystem IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : IZ → OutPortVal op :=
  fun i => PJN op (C.RZ i)

/-- Output trajectory of the `op`-th port of a combinational system. -/
def portOutputTrajectory {OutPort : Type} {OutPortVal : OutPort → Type}
    (ot : OTZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : Time → OutPortVal op :=
  fun t => PJN op (ot t)

/-- Port readout at time `t` equals the generated output trajectory on that port. -/
theorem portReadout_at_time {OutPort : Type} {OutPortVal : OutPort → Type} {IZ : Type}
    (C : CombinationalSystem IZ ((op : OutPort) → OutPortVal op)) (op : OutPort)
    (f : ITZ IZ) (t : Time) :
    portReadout C op (f t) = generateOutputTrajectory C f t op := rfl

/-- Zero-delay combinational output: alias for `generateOutputTrajectory_val`. -/
theorem combinational_zero_delay (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory C f t = C.RZ (f t) :=
  generateOutputTrajectory_val C f t

/-! ## Parameterization -/

/--
  [textbook/definition2.82/definition/system_parameterization]
  A combinational system parameterization F maps a parameter type `P` to a `CombinationalSystem`.
-/
def CombinationalSystemParameterization (P : Type u) (IZ OZ : P → Type) : Type u :=
  (p : P) → CombinationalSystem (IZ p) (OZ p)

/--
  [textbook/definition2.82/definition/parameter_instance]
  Instance of a combinational parameterization at parameter value `r`.
-/
def parameterInstance {P : Type u} {IZ OZ : P → Type}
    (F : CombinationalSystemParameterization P IZ OZ) (r : P) : CombinationalSystem (IZ r) (OZ r) :=
  F r

/-! ## fccsy (Function Computation Combinational System) -/

/--
  [textbook/definition2.93/definition/fcnsy]
  The combinational version of a function computation system (zero-delay analogue of `fcnsy`).
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

/-- [textbook/definition2.82/definition/one_parameter]
    `fccsy` is parameterized by a single function `F : IZ → OZ`. -/
theorem fccsy_has_one_parameter {IZ OZ : Type} :
    FSM.HasOneParameter (IZ → OZ) := by
  let ParamType : Fin 1 → Type := fun _ => IZ → OZ
  refine ⟨ParamType, ⟨{
    toFun := fun f _i => f
    invFun := fun g => g ⟨0, by decide⟩
    left_inv := fun _ => rfl
    right_inv := fun g => funext fun i => by
      rw [Subsingleton.elim i ⟨0, by decide⟩]
  }⟩⟩

/-! ## Parallel (Conjunctive) Composition -/

/--
  [textbook/definition3.3/definition/connection_vector]
  A vector of combinational systems with port-based interfaces.
-/
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

/-- [textbook/definition3.40/definition/csy]
    Parallel (conjunctive) composition of combinational systems. -/
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

/-- [textbook/theorem3.45/theorem/trajectories_relation]
    Output trajectory of parallel composition evaluated at port `B'` of system `i`
    is identical to the output trajectory of components under projected input.
    Proven strictly by definition (`rfl`) — intentional zero-proof-power win for combinational logic. -/
theorem ccsy_output_trajectory {n : Nat} (VCS : PortCombinationalSystemVector n)
    (f : ITZ ((ip : Σ i, VCS.Port i) → VCS.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) (B' : VCS.OutPort i) :
    generateOutputTrajectory (ccsy VCS) f t ⟨i, B'⟩ =
    generateOutputTrajectory (VCS.C i) (fun t port => f t ⟨i, port⟩) t B' := by
  rfl

/-- Parallel composition preserves finiteness of input and output spaces. -/
theorem ccsy_isFinite {n : Nat} (VCS : PortCombinationalSystemVector n) :
    IsFinite (ccsy VCS) :=
  combinationalSystem_isFinite (ccsy VCS)

lemma isNontrivial_iff_distinct_readouts {IZ OZ : Type} (C : CombinationalSystem IZ OZ) :
    IsNontrivial C ↔ ∃ (a b : IZ), C.RZ a ≠ C.RZ b := by
  classical
  constructor
  · intro h
    unfold IsNontrivial at h
    rcases Finset.one_lt_card.mp h with ⟨y1, hy1, y2, hy2, hyne⟩
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy2
    exact ⟨a, b, fun heq => hyne (by rw [← ha, heq, hb])⟩
  · intro ⟨a, b, hab⟩
    unfold IsNontrivial
    exact Finset.one_lt_card.mpr ⟨C.RZ a,
      Finset.mem_image.mpr ⟨a, @Finset.mem_univ IZ C.iz_finite a, rfl⟩,
      C.RZ b, Finset.mem_image.mpr ⟨b, @Finset.mem_univ IZ C.iz_finite b, rfl⟩, hab⟩

/--
  Parallel composition is nontrivial if any component is nontrivial: two global inputs that agree
  everywhere except on component `i`'s ports induce different readouts on that component's outputs.
-/
theorem ccsy_isNontrivial_of_component {n : Nat} (VCS : PortCombinationalSystemVector n)
    (i : Fin n) (h : IsNontrivial (VCS.C i))
    [∀ j, Inhabited ((p : VCS.Port j) → VCS.PortVal j p)] :
    IsNontrivial (ccsy VCS) := by
  obtain ⟨a, b, hab⟩ := (isNontrivial_iff_distinct_readouts (VCS.C i)).mp h
  rcases (Function.ne_iff (f₁ := (VCS.C i).RZ a) (f₂ := (VCS.C i).RZ b)).mp hab with ⟨B', hB'⟩
  let defaultVal (j : Fin n) (port : VCS.Port j) : VCS.PortVal j port :=
    (default : (p : VCS.Port j) → VCS.PortVal j p) port
  let extendInput (a : (p : VCS.Port i) → VCS.PortVal i p) (ip : Σ (k : Fin n), VCS.Port k) :
      VCS.PortVal ip.1 ip.2 :=
    if h : ip.1 = i then
      h ▸ a (cast (congrArg VCS.Port h) ip.2)
    else
      defaultVal ip.1 ip.2
  let p_a := extendInput a
  let p_b := extendInput b
  have h_input_a : (fun port => p_a ⟨i, port⟩) = a := by
    funext port
    simp [p_a, extendInput]
  have h_input_b : (fun port => p_b ⟨i, port⟩) = b := by
    funext port
    simp [p_b, extendInput]
  have hRa : (ccsy VCS).RZ p_a ⟨i, B'⟩ = (VCS.C i).RZ a B' := by
    dsimp [ccsy]
    rw [h_input_a]
  have hRb : (ccsy VCS).RZ p_b ⟨i, B'⟩ = (VCS.C i).RZ b B' := by
    dsimp [ccsy]
    rw [h_input_b]
  have hout : (ccsy VCS).RZ p_a ≠ (ccsy VCS).RZ p_b := by
    intro heq
    apply hB'
    rw [← hRa, ← hRb, congr_fun heq ⟨i, B'⟩]
  exact (isNontrivial_iff_distinct_readouts (ccsy VCS)).mpr ⟨p_a, p_b, hout⟩

/--
  [textbook/theorem3.42/theorem/csy_parameterization]
  `ccsy` defines a valid combinational system parameterization.
-/
def ccsy_parameterization (n : Nat) :
    CombinationalSystemParameterization (PortCombinationalSystemVector n)
      (fun VCS => (ip : Σ i, VCS.Port i) → VCS.PortVal ip.1 ip.2)
      (fun VCS => (op : Σ i, VCS.OutPort i) → VCS.OutPortVal op.1 op.2) :=
  fun VCS => ccsy VCS

/-! ## Coupling recipes (Ch. 3) -/

/--
  [textbook/definition3.7/requirement/port_compatibility]
  Port compatibility for combinational coupling: connected ports must have equal value types.
-/
def PortCompatibilityCombinational {n : Nat} (VCS : PortCombinationalSystemVector n)
    (CCSCR : Set ((Σ (i : Fin n), VCS.OutPort i) × (Σ (i : Fin n), VCS.Port i))) : Prop :=
  ∀ (op : Σ (i : Fin n), VCS.OutPort i) (ip : Σ (i : Fin n), VCS.Port i),
    (op, ip) ∈ CCSCR → VCS.OutPortVal op.1 op.2 = VCS.PortVal ip.1 ip.2

/--
  [textbook/definition3.7/definition/connectivity_relation]
  Valid system connectivity for a combinational system vector.
-/
def IsCombinationalSystemConnectivity {n : Nat} (VCS : PortCombinationalSystemVector n)
    (CCSCR : Set ((Σ (i : Fin n), VCS.OutPort i) × (Σ (i : Fin n), VCS.Port i))) : Prop :=
  FSM.IsOneToOneRelation CCSCR ∧
  FSM.IsProperDomain CCSCR ∧
  FSM.IsProperRange CCSCR ∧
  PortCompatibilityCombinational VCS CCSCR

/--
  [textbook/definition3.11/definition/system_coupling_recipe]
  A combinational coupling recipe pairs a connectable vector of combinational systems with a
  connectivity relation. Execution for empty `CCSCR` is `ccsy CCR.VCS`; non-empty coupling is
  classification-only in this module (mirroring base Wymore Ch. 3 scope).
-/
structure CombinationalCouplingRecipe (n : Nat) where
  VCS : PortCombinationalSystemVector n
  CCSCR : Set ((Σ (i : Fin n), VCS.OutPort i) × (Σ (i : Fin n), VCS.Port i))
  connectivity : IsCombinationalSystemConnectivity VCS CCSCR

/--
  [textbook/definition3.7/definition/feedback_connection]
  Feedback connection for combinational coupling recipes (output index ≥ input index).
-/
def IsFeedbackCombinational {n : Nat} {VCS : PortCombinationalSystemVector n}
    (p : (Σ (i : Fin n), VCS.OutPort i) × (Σ (i : Fin n), VCS.Port i)) : Prop :=
  p.1.1 ≥ p.2.1

/--
  [textbook/definition3.11/definition/coscr]
  Output ports connected by the combinational coupling recipe.
-/
def CCOSCR {n : Nat} (CCR : CombinationalCouplingRecipe n) : Set (Σ (i : Fin n), CCR.VCS.OutPort i) :=
  { op | ∃ ip, (op, ip) ∈ CCR.CCSCR }

/--
  [textbook/definition3.11/definition/ciscr]
  Input ports connected by the combinational coupling recipe.
-/
def CCISCR {n : Nat} (CCR : CombinationalCouplingRecipe n) : Set (Σ (i : Fin n), CCR.VCS.Port i) :=
  { ip | ∃ op, (op, ip) ∈ CCR.CCSCR }

/--
  [textbook/definition3.11/definition/uoscr]
  Output ports unconnected by the combinational coupling recipe.
-/
def CUOSCR {n : Nat} (CCR : CombinationalCouplingRecipe n) : Set (Σ (i : Fin n), CCR.VCS.OutPort i) :=
  (CCOSCR CCR)ᶜ

/--
  [textbook/definition3.11/definition/uiscr]
  Input ports unconnected by the combinational coupling recipe.
-/
def CUISCR {n : Nat} (CCR : CombinationalCouplingRecipe n) : Set (Σ (i : Fin n), CCR.VCS.Port i) :=
  (CCISCR CCR)ᶜ

/--
  [textbook/definition3.11/definition/interface]
  Interface between systems `i` and `j` in a combinational coupling recipe.
-/
def CCSCRInterface {n : Nat} (CCR : CombinationalCouplingRecipe n) (i j : Fin n) :
    Set ((Σ (k : Fin n), CCR.VCS.OutPort k) × (Σ (k : Fin n), CCR.VCS.Port k)) :=
  { p ∈ CCR.CCSCR | (p.1.1 = i ∧ p.2.1 = j) ∨ (p.1.1 = j ∧ p.2.1 = i) }

/--
  [textbook/definition3.15/definition/conjunctive_scr]
  A combinational coupling recipe is conjunctive if and only if `CCSCR` is empty.
-/
def IsConjunctiveCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  CCR.CCSCR = ∅

/--
  [textbook/definition3.19/definition/cascade_scr]
  A combinational coupling recipe is cascade if and only if `CCSCR` contains no feedback connections.
-/
def IsCascadeCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  ∀ p ∈ CCR.CCSCR, ¬ IsFeedbackCombinational (VCS := CCR.VCS) p

/--
  [textbook/definition3.19/definition/essentially_cascade_scr]
  A combinational coupling recipe is essentially cascade if a reordering of components yields cascade.
-/
def IsEssentiallyCascadeCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  ∃ (g : Fin n ≃ Fin n), ∀ p ∈ CCR.CCSCR, g p.1.1 < g p.2.1

/--
  [textbook/definition3.26/definition/singular_scr]
  A combinational coupling recipe is singular if and only if `n = 1` and `CCSCR` is empty.
-/
def IsSingularCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  n = 1 ∧ CCR.CCSCR = ∅

/--
  [textbook/definition3.29/definition/pure_feedback_scr]
  A combinational coupling recipe is pure feedback if and only if `n = 1` and `CCSCR` is nonempty.
-/
def IsPureFeedbackCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  n = 1 ∧ CCR.CCSCR ≠ ∅

/--
  [textbook/theorem3.31/theorem/class_in_themselves]
  Pure feedback combinational coupling recipes are neither singular, conjunctive, nor cascade.
-/
theorem pure_feedback_combinational_not_other {n : Nat} (CCR : CombinationalCouplingRecipe n)
    (h : IsPureFeedbackCombinational CCR) :
    ¬ IsSingularCombinational CCR ∧ ¬ IsConjunctiveCombinational CCR ∧ ¬ IsCascadeCombinational CCR := by
  have hn : n = 1 := h.1
  have hne : CCR.CCSCR ≠ ∅ := h.2
  constructor
  · intro hs
    exact hne hs.2
  · constructor
    · intro hc
      exact hne hc
    · intro h_cas
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have : Subsingleton (Fin n) := by
        rw [hn]
        infer_instance
      have heq : p.1.1 = p.2.1 := Subsingleton.elim p.1.1 p.2.1
      have h_feed : IsFeedbackCombinational (VCS := CCR.VCS) p := by
        unfold IsFeedbackCombinational
        rw [heq]
      have h_not_feed := h_cas p hp
      exact h_not_feed h_feed

/--
  [textbook/definition3.33/definition/mixed_scr]
  A combinational coupling recipe is mixed if it is not singular, conjunctive, cascade,
  essentially cascade, or pure feedback.
-/
def IsMixedCombinational {n : Nat} (CCR : CombinationalCouplingRecipe n) : Prop :=
  ¬ IsSingularCombinational CCR ∧ ¬ IsConjunctiveCombinational CCR ∧ ¬ IsCascadeCombinational CCR ∧
  ¬ IsEssentiallyCascadeCombinational CCR ∧ ¬ IsPureFeedbackCombinational CCR

/-- Alias for `generateOutputTrajectory_val` documenting the zero-delay readout composition. -/
theorem outputTrajectory_eq_RZ_comp (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory C f t = C.RZ (f t) :=
  generateOutputTrajectory_val C f t

end Combinational

/-! ## State Space Limitation Analysis -/

/--
  Theorem: Any Moore-style `DiscreteSystem` restricted to `SingletonState` produces a
  constant output trajectory, completely independent of its input trajectory.

  Moore readout `RZ : SingletonState → OZ` cannot depend on the current input; the output at
  every time is determined solely by the (unique) state visited. For non-constant input-dependent
  maps, use `Combinational.CombinationalSystem` (zero-delay Mealy readout) or
  `combinationalToDelaySystem` (Moore with 1-step lag).
-/
theorem singleton_state_discrete_system_is_constant {IZ OZ : Type}
    (Z : FSM.FSMSystem SingletonState IZ OZ) (s_init : SingletonState) (f g : ITZ IZ) (t : Time) :
    FSM.generateOutputTrajectory Z s_init f t = FSM.generateOutputTrajectory Z s_init g t := by
  unfold FSM.generateOutputTrajectory
  cases (FSM.generateStateTrajectory Z s_init f t)
  cases (FSM.generateStateTrajectory Z s_init g t)
  rfl

/--
  Corollary in I/O language: zero-delay Moore encoding on `SingletonState` cannot distinguish
  input trajectories. See module doc "Encoding options" for the three viable encodings.
-/
theorem zeroDelayMooreOnSingleton_impossible {IZ OZ : Type}
    (Z : FSM.FSMSystem SingletonState IZ OZ) (s : SingletonState) (f g : ITZ IZ) (t : Time) :
    FSM.generateOutputTrajectory Z s f t = FSM.generateOutputTrajectory Z s g t :=
  singleton_state_discrete_system_is_constant Z s f g t

/--
  To model a `Combinational.CombinationalSystem` using Wymore's `DiscreteSystem` without losing the
  input dependency, we must introduce a 1-step delay and use `IZ` itself as the state space.
-/
def combinationalToDelaySystem {IZ OZ : Type} (C : Combinational.CombinationalSystem IZ OZ) [Inhabited IZ] : FSM.FSMSystem IZ IZ OZ where
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
    FSM.generateOutputTrajectory (combinationalToDelaySystem C) x f (t + 1) = C.RZ (f t) := by
  rfl

/-- At `t = 0` the delayed Moore system outputs `C.RZ x` (the initial state as readout),
    not the combinational response to `f 0`. The 1-step offset begins at `t + 1`. -/
theorem delay_system_initial_output {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ) :
    FSM.generateOutputTrajectory (combinationalToDelaySystem C) x f 0 = C.RZ x := by
  rfl

/-- Full trajectory correspondence: delayed Moore output at `t + 1` equals instantaneous
    combinational output at `t`. -/
theorem delay_system_matches_combinational_trajectory {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ) (t : Time) :
    FSM.generateOutputTrajectory (combinationalToDelaySystem C) x f (t + 1) =
      Combinational.generateOutputTrajectory C f t := by
  rfl

/--
  Summary: input-dependent zero-delay output requires either combinational readout or a delayed
  Moore system with nontrivial state. Moore on a singleton cannot express non-constant I/O.
-/
theorem zeroDelayRequiresCombinationalOrDelay {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) :
    Combinational.generateOutputTrajectory C f t = C.RZ (f t) ∧
    FSM.generateOutputTrajectory (combinationalToDelaySystem C) default f (t + 1) =
      Combinational.generateOutputTrajectory C f t :=
  ⟨Combinational.generateOutputTrajectory_val C f t, delay_system_matches_combinational_trajectory C default f t⟩

/-- State of the delayed Moore embedding at `t + 1` holds the input at time `t`. -/
theorem delaySystem_state_at_time {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ) (t : Time) :
    FSM.generateStateTrajectory (combinationalToDelaySystem C) x f (t + 1) = f t := by
  induction t with
  | zero => simp [FSM.generateStateTrajectory_succ, FSM.generateStateTrajectory_zero, combinationalToDelaySystem]
  | succ t _ =>
    simp [FSM.generateStateTrajectory_succ, combinationalToDelaySystem]

/-- Delay-system output at `t + 1` derives combinational output at `t` via the embedding bridge. -/
theorem delaySystem_derives_combinational_output {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ) (t : Time) :
    FSM.generateOutputTrajectory (combinationalToDelaySystem C) x f (t + 1) =
      C.RZ (f t) := by
  rw [delay_system_matches_combinational_trajectory, Combinational.generateOutputTrajectory_val]

/--
  Output trajectory uniqueness for the delay embedding at each time step, derived from base Wymore
  `FSM.outputTrajectory_unique` and the combinational bridge.
-/
theorem delaySystem_outputTrajectory_unique {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ)
    (h : OTZ OZ) (h_valid : FSM.IsValidOutputTrajectory (combinationalToDelaySystem C)
      (FSM.generateStateTrajectory (combinationalToDelaySystem C) x f) h) (t : Time) :
    h t = FSM.generateOutputTrajectory (combinationalToDelaySystem C) x f t := by
  rw [FSM.outputTrajectory_unique (combinationalToDelaySystem C)
    (FSM.generateStateTrajectory (combinationalToDelaySystem C) x f) h h_valid t]
  rfl

/--
  Valid delay-system output at `t + 1` equals combinational output at `t`.
-/
theorem delaySystem_valid_implies_combinational_valid {IZ OZ : Type} [Inhabited IZ]
    (C : Combinational.CombinationalSystem IZ OZ) (x : IZ) (f : ITZ IZ) (h : OTZ OZ)
    (h_valid : FSM.IsValidOutputTrajectory (combinationalToDelaySystem C)
      (FSM.generateStateTrajectory (combinationalToDelaySystem C) x f) h) (t : Time) :
    h (t + 1) = Combinational.generateOutputTrajectory C f t := by
  rw [h_valid (t + 1), Combinational.generateOutputTrajectory_val, delaySystem_state_at_time]
  rfl
