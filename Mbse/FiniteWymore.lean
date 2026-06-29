import Mbse.Wymore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Basic

/-!
# Finite Moore FSM Wymore Systems (Definition 2.11)

Finite discrete systems: `FSMSystem` carries `Fintype` on state, input, and output spaces.
This module preserves the original finite Moore-machine development (`Z2`, `csy`, Ch. 3
coupling, order vectors) and bridges to the general `DiscreteSystem` of [`Wymore`](Wymore.lean)
via `FSMSystem.toDiscreteSystem`. See [`Wymore`](Wymore.lean) for the general Definition 2.4 base.
-/

namespace FSM

variable {SZ IZ OZ : Type}

/--
  [textbook/definition2.4/component/Z] [textbook/definition2.4/component/SZ] [textbook/definition2.4/component/IZ] [textbook/definition2.4/component/OZ]
  [textbook/definition2.11/definition/finite_system]
  A finite Moore machine within Wymore's framework: Definition 2.4 quintuple with finite
  state, input, and output spaces (Definition 2.11).
-/
structure FSMSystem (SZ : Type) (IZ : Type) (OZ : Type) where
  /-- [textbook/definition2.4/constraint/sz_nonempty] Proof that the state space SZ is not empty -/
  sz_nonempty : Nonempty SZ
  /-- Proof that the state space is finite (Definition 2.11) -/
  sz_finite : Fintype SZ
  /-- Proof that the input space is finite (Definition 2.11) -/
  iz_finite : Fintype IZ
  /-- Proof that the output space is finite (Definition 2.11) -/
  oz_finite : Fintype OZ
  /-- [textbook/definition2.4/component/NZ] [textbook/definition2.4/constraint/nz_signature|partial] -/
  NZ : SZ → IZ → SZ
  /-- [textbook/definition2.4/component/RZ] [textbook/definition2.4/constraint/rz_signature|partial] -/
  RZ : SZ → OZ

/-- Embed a finite Moore machine into a general `DiscreteSystem` (Definition 2.4). -/
def FSMSystem.toDiscreteSystem (F : FSMSystem SZ IZ OZ) : DiscreteSystem SZ IZ OZ :=
  DiscreteSystem.ofTotal F.NZ F.RZ F.sz_nonempty

theorem fsm_alwaysOutputs (F : FSMSystem SZ IZ OZ) : AlwaysOutputs F.toDiscreteSystem :=
  ofTotal_alwaysOutputs F.NZ F.RZ F.sz_nonempty

abbrev liftInput (f : ITZ IZ) : ITZW IZ := _root_.liftInput f

/-- [textbook/definition2.11/definition/finite_system] Every `FSMSystem` is finite. -/
theorem fsm_isFinite (F : FSMSystem SZ IZ OZ) : IsFinite F.toDiscreteSystem := by
  have : Fintype SZ := F.sz_finite
  have : Fintype IZ := F.iz_finite
  have : Fintype OZ := F.oz_finite
  exact ⟨Finite.of_fintype SZ, Finite.of_fintype IZ, Finite.of_fintype OZ⟩


/-! ## Trajectory engine (finite systems) -/

def generateStateTrajectory (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : STZ SZ :=
  _root_.generateStateTrajectory F.toDiscreteSystem s0 (liftInput f)

def generateOutputTrajectory (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : OTZ OZ :=
  _root_.generateOutputTrajectory F.toDiscreteSystem s0 (liftInput f)

def IsValidStateTrajectory (F : FSMSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) : Prop :=
  _root_.IsValidStateTrajectory F.toDiscreteSystem (liftInput f) g

def IsValidOutputTrajectory (F : FSMSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ) : Prop :=
  _root_.IsValidOutputTrajectory F.toDiscreteSystem g h

def Reachable (F : FSMSystem SZ IZ OZ) (s0 s : SZ) : Prop :=
  ∃ (f : ITZ IZ) (t : Time), generateStateTrajectory F s0 f t = s

def StateEquiv (F : FSMSystem SZ IZ OZ) (s1 s2 : SZ) : Prop :=
  ∀ (f : ITZ IZ) (t : Time),
    generateOutputTrajectory F s1 f t = generateOutputTrajectory F s2 f t

structure SystemMorphism
    {SZ1 IZ1 OZ1 : Type} {SZ2 IZ2 OZ2 : Type}
    (F1 : FSMSystem SZ1 IZ1 OZ1)
    (F2 : FSMSystem SZ2 IZ2 OZ2) where
  φS : SZ1 → SZ2
  φI : IZ1 → IZ2
  φO : OZ1 → OZ2
  preserves_transition : ∀ s i, φS (F1.NZ s i) = F2.NZ (φS s) (φI i)
  preserves_readout : ∀ s, φO (F1.RZ s) = F2.RZ (φS s)

def SystemMorphism.toDiscreteSystem
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {F1 : FSMSystem SZ1 IZ1 OZ1} {F2 : FSMSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism F1 F2) : _root_.SystemMorphism F1.toDiscreteSystem F2.toDiscreteSystem where
  φS := m.φS
  φI := m.φI
  φO := m.φO
  preserves_transition := fun s oi => by
    cases oi with
    | none => simp [FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    | some i => simp [FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal, m.preserves_transition]
  preserves_readout := fun s => by
    simp [FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal, m.preserves_readout, Option.map_some]

theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {F1 : FSMSystem SZ1 IZ1 OZ1} {F2 : FSMSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism F1 F2) (s0 : SZ1) (f : ITZ IZ1) :
    ∀ t, m.φS (generateStateTrajectory F1 s0 f t) =
         generateStateTrajectory F2 (m.φS s0) (m.φI ∘ f) t :=
  _root_.morphism_preserves_state_trajectory m.toDiscreteSystem s0 (liftInput f)

theorem morphism_preserves_output_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {F1 : FSMSystem SZ1 IZ1 OZ1} {F2 : FSMSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism F1 F2) (s0 : SZ1) (f : ITZ IZ1) :
    ∀ t, (generateOutputTrajectory F1 s0 f t).map m.φO =
         generateOutputTrajectory F2 (m.φS s0) (m.φI ∘ f) t :=
  _root_.morphism_preserves_output_trajectory m.toDiscreteSystem s0 (liftInput f)

theorem stateTrajectory_unique (F : FSMSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) (s0 : SZ)
    (h_init : g 0 = s0) (h_valid : IsValidStateTrajectory F f g) :
    ∀ t, g t = generateStateTrajectory F s0 f t :=
  _root_.stateTrajectory_unique F.toDiscreteSystem (liftInput f) g s0 h_init h_valid

theorem generateStateTrajectory_valid (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    IsValidStateTrajectory F f (generateStateTrajectory F s0 f) :=
  _root_.generateStateTrajectory_valid F.toDiscreteSystem s0 (liftInput f)

theorem generateOutputTrajectory_valid (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    IsValidOutputTrajectory F (generateStateTrajectory F s0 f) (generateOutputTrajectory F s0 f) :=
  _root_.generateOutputTrajectory_valid F.toDiscreteSystem s0 (liftInput f)

theorem outputTrajectory_unique (F : FSMSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ)
    (h_valid : IsValidOutputTrajectory F g h) (t : Time) :
    h t = some (F.RZ (g t)) :=
  h_valid t

/-! ## Bridge corollaries -/

theorem toDiscreteSystem_state_trajectory (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateStateTrajectory F s0 f t =
      _root_.generateStateTrajectory F.toDiscreteSystem s0 (liftInput f) t := rfl

theorem toDiscreteSystem_output_trajectory (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory F s0 f t =
      _root_.generateOutputTrajectory F.toDiscreteSystem s0 (liftInput f) t := rfl

theorem generateOutputTrajectory_eq (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory F s0 f t = some (F.RZ (generateStateTrajectory F s0 f t)) := by
  unfold generateOutputTrajectory generateStateTrajectory liftInput
  simp only [_root_.generateOutputTrajectory, _root_.generateStateTrajectory,
    FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]

theorem reachable_iff (F : FSMSystem SZ IZ OZ) (s0 s : SZ) :
    Reachable F s0 s ↔ ∃ (f : ITZ IZ) (t : Time), generateStateTrajectory F s0 f t = s :=
  Iff.rfl

theorem stateEquiv_iff (F : FSMSystem SZ IZ OZ) (s1 s2 : SZ) :
    StateEquiv F s1 s2 ↔ ∀ (f : ITZ IZ) (t : Time),
      generateOutputTrajectory F s1 f t = generateOutputTrajectory F s2 f t :=
  Iff.rfl

@[simp] theorem generateStateTrajectory_zero (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    generateStateTrajectory F s0 f 0 = s0 := rfl

@[simp] theorem generateStateTrajectory_succ (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateStateTrajectory F s0 f (t + 1) = F.NZ (generateStateTrajectory F s0 f t) (f t) := by
  simp [generateStateTrajectory, _root_.generateStateTrajectory_succ,
    FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal, liftInput]

def HasOrderVector {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) (k m n : Nat) : Prop :=
  have : Fintype SZ := Z.sz_finite
  have : Fintype IZ := Z.iz_finite
  have : Fintype OZ := Z.oz_finite
  Fintype.card SZ = k ∧ Fintype.card IZ = m ∧ Fintype.card OZ = n ∧
  k ≥ 1 ∧ m ≥ 1 ∧ n ≥ 1

/--
  [textbook/definition_a1.218/definition/range]
  The range (RNG) of a function `f : A → B` (with finite domain A and decidable equality on B)
  is the image of the domain under `f` as a Finset.
-/
def RNG {A B : Type} [Fintype A] [DecidableEq B] (f : A → B) : Finset B :=
  Finset.image f Finset.univ

/--
  [textbook/definition2.14/definition/nontrivial_system]
  [textbook/definition2.14/requirement/state_dependent_transition]
  [textbook/definition2.14/requirement/active_transition]
  [textbook/definition2.14/requirement/varying_output]
  A Wymorian discrete system Z is nontrivial if and only if:
  1. State-dependent transition: there exist x1, x2 : SZ and p : IZ such that Z.NZ x1 p ≠ Z.NZ x2 p
  2. Active transition: there exist x : SZ and p : IZ such that Z.NZ x p ≠ x
  3. Varying output: the size of the range of the readout function Z.RZ is greater than 1.
-/
def IsNontrivial {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) : Prop :=
  have : Fintype SZ := Z.sz_finite
  have : DecidableEq OZ := Classical.decEq OZ
  (∃ (x1 x2 : SZ) (p : IZ), Z.NZ x1 p ≠ Z.NZ x2 p) ∧
  (∃ (x : SZ) (p : IZ), Z.NZ x p ≠ x) ∧
  (Finset.card (RNG Z.RZ) > 1)

/--
  [textbook/definition2.14/implication/trivial_system]
  A system Z is trivial if and only if it is not nontrivial.
-/
def IsTrivial {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) : Prop :=
  ¬ IsNontrivial Z

/-! ## FSM port readout (via general layer) -/

def portReadout {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (F : FSMSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : SZ → Option (OutPortVal op) :=
  _root_.portReadout F.toDiscreteSystem op

def IsProperlyAlignedReadout {IZ I : Type} {Val : I → Type}
    (F : FSMSystem ((i : I) → Val i) IZ ((i : I) → Val i)) : Prop :=
  _root_.IsProperlyAlignedReadout F.toDiscreteSystem

def IsProjectiveReadout {IZ OutPort StateFactor : Type} {OutPortVal : OutPort → Type}
    {StateFactorVal : StateFactor → Type}
    (F : FSMSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op)) : Prop :=
  _root_.IsProjectiveReadout F.toDiscreteSystem

def HasStateReadout {SZ IZ : Type} (F : FSMSystem SZ IZ SZ) : Prop :=
  _root_.HasStateReadout F.toDiscreteSystem

open Z2State in
/--
  [textbook/theorem2.78/theorem/system_construction]
  Finite wrapper: NZ/RZ agree with [`_root_.Z2`](Wymore.lean) on `toDiscreteSystem`.
-/
noncomputable def Z2RZ (Z : FSMSystem SZ IZ OZ) : SZ → Option OZ := fun s => some (Z.RZ s)

noncomputable def Z2 (Z : FSMSystem SZ IZ OZ) : FSMSystem (Z2State SZ OZ (Z2RZ Z)) IZ OZ where
  sz_nonempty := Z.sz_nonempty.map (Z2State.equivSZ (Z2RZ Z) (fun s => ⟨Z.RZ s, rfl⟩)).symm
  sz_finite := by
    haveI : Fintype SZ := Z.sz_finite
    exact Fintype.ofEquiv SZ (Z2State.equivSZ (Z2RZ Z) (fun s => ⟨Z.RZ s, rfl⟩)).symm
  iz_finite := Z.iz_finite
  oz_finite := Z.oz_finite
  NZ := fun s2 p => ⟨Z.RZ (Z.NZ s2.state p), Z.NZ s2.state p, rfl⟩
  RZ := fun s2 => s2.out

theorem z2_readout_projective {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : FSMSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort)
    (s2 : Z2State SZ ((op : OutPort) → OutPortVal op) (Z2RZ Z)) :
    portReadout (Z2 Z) op s2 = some (s2.out op) :=
  _root_.z2_readout_projective Z.toDiscreteSystem (fsm_alwaysOutputs Z) op s2

def Z2.exz_map {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) :
    EXZ SZ IZ → EXZ (Z2State SZ OZ (Z2RZ Z)) IZ :=
  _root_.Z2.exz_map Z.toDiscreteSystem (fsm_alwaysOutputs Z)

theorem z2_state_trajectory_equivalence {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) (x : SZ)
    (f : ITZ IZ) (t : Time) :
    (generateStateTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t).state = generateStateTrajectory Z x f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [generateStateTrajectory_succ, Z2, Z2State.state]
    exact congr_arg (fun s => Z.NZ s (f t)) ih

theorem z2_output_trajectory_equivalence {SZ IZ OZ : Type} (Z : FSMSystem SZ IZ OZ) (x : SZ)
    (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t =
    generateOutputTrajectory Z x f t := by
  rw [generateOutputTrajectory_eq, generateOutputTrajectory_eq]
  set s2 := generateStateTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t
  have hst := z2_state_trajectory_equivalence Z x f t
  have ho : s2.out = Z.RZ (generateStateTrajectory Z x f t) := by
    have heq : some (Z.RZ s2.state) = some s2.out := by simpa [Z2RZ] using s2.eq
    rw [hst] at heq
    exact Option.some_injective _ heq.symm
  exact congrArg some ho

/-! ## System Parameterization -/

/--
  [textbook/definition2.82/definition/system_parameterization]
  A system parameterization F maps a parameter type `P` to a `FSMSystem`.
  To allow system spaces to depend on parameters, we define it as a structure
  where the state, input, and output spaces are functions of `P`.
-/
def FSMSystemParameterization (P : Type u) (SZ IZ OZ : P → Type) : Type u :=
  (p : P) → FSMSystem (SZ p) (IZ p) (OZ p)

/--
  [textbook/definition2.82/definition/parameter_instance]
  An instance of a system parameterization `F` for a parameter value `r : P`
  is simply the system `F r`.
-/
def parameterInstance {P : Type u} {SZ IZ OZ : P → Type}
    (F : FSMSystemParameterization P SZ IZ OZ) (r : P) : FSMSystem (SZ r) (IZ r) (OZ r) :=
  F r

/--
  [textbook/definition2.82/definition/multiple_parameters]
  A parameterization has `n` parameters if its parameter domain type is (equivalent to) a
  product type indexed by `Fin n`. Stated via an explicit type equivalence so the predicate
  carries real content rather than restating its own hypothesis.
-/
def HasNParameters (P : Type) (n : Nat) (ParamType : Fin n → Type) : Prop :=
  _root_.HasNParameters P n ParamType

def HasOneParameter (P : Type) : Prop :=
  _root_.HasOneParameter P

def fcnsy {IZ SZ : Type} (F : IZ → SZ) (n : Nat) [Fintype SZ] [Fintype IZ] [Inhabited SZ] :
    FSMSystem SZ IZ (Fin n → SZ) :=
  { sz_nonempty := ⟨default⟩
    sz_finite := inferInstance
    iz_finite := inferInstance
    oz_finite := inferInstance
    NZ := fun _ i => F i
    RZ := fun x _j => x }

theorem fcnsy_output_one_time_unit {IZ SZ : Type} (F : IZ → SZ) [Fintype SZ] [Fintype IZ]
    [Inhabited SZ] (x : SZ) (f : ITZ IZ) (t : Time) :
    (generateOutputTrajectory (fcnsy F 1) x f (t + 1)).map (fun r => r 0) = some (F (f t)) := by
  simpa [generateOutputTrajectory, fcnsy, liftInput] using
    _root_.fcnsy_output_one_time_unit F x (liftInput f) t (f t) rfl

/-! ## Chapter 3: System Coupling Recipes and Connectivity -/

/--
  [textbook/definition3.3/definition/connection_vector]
  [textbook/definition3.3/requirement/pairwise_distinct]
  A connectable vector of systems of length `n`.
  Each component `i` is a discrete system with structured input and output ports.
  All component systems are pairwise distinct under heterogeneous equality (HEq).
-/
structure PortSystemVector (n : Nat) where
  SZ : Fin n → Type
  Port : Fin n → Type
  PortVal : (i : Fin n) → Port i → Type
  OutPort : Fin n → Type
  OutPortVal : (i : Fin n) → OutPort i → Type
  Z : (i : Fin n) → FSMSystem (SZ i) ((p : Port i) → PortVal i p) ((op : OutPort i) → OutPortVal i op)
  Port_finite : (i : Fin n) → Fintype (Port i)
  PortVal_finite : (i : Fin n) → (p : Port i) → Fintype (PortVal i p)
  OutPort_finite : (i : Fin n) → Fintype (OutPort i)
  OutPortVal_finite : (i : Fin n) → (op : OutPort i) → Fintype (OutPortVal i op)
  Port_decidable : (i : Fin n) → DecidableEq (Port i)
  OutPort_decidable : (i : Fin n) → DecidableEq (OutPort i)
  distinct : ∀ (i j : Fin n), i ≠ j → ¬ HEq (Z i) (Z j)

/--
  [textbook/definition3.7/definition/connectivity_relation]
  A relation R is a 1-to-1 function if it is single-valued and injective.
-/
def IsOneToOneRelation {α β : Type} (R : Set (α × β)) : Prop :=
  (∀ (x : α) (y1 y2 : β), (x, y1) ∈ R → (x, y2) ∈ R → y1 = y2) ∧
  (∀ (x1 x2 : α) (y : β), (x1, y) ∈ R → (x2, y) ∈ R → x1 = x2)

/--
  [textbook/definition3.7/requirement/domain_subset]
  The domain of CSCR is a proper subset of all output ports (modeled as not equal to Set.univ).
-/
def IsProperDomain {α β : Type} (R : Set (α × β)) : Prop :=
  { x : α | ∃ y, (x, y) ∈ R } ≠ Set.univ

/-- [textbook/definition3.7/requirement/range_subset] The range of CSCR is a proper subset of all input ports. -/
def IsProperRange {α β : Type} (R : Set (α × β)) : Prop :=
  { y : β | ∃ x, (x, y) ∈ R } ≠ Set.univ

def PortCompatibility {n : Nat} (VSCR : PortSystemVector n)
    (CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))) : Prop :=
  ∀ (op : Σ (i : Fin n), VSCR.OutPort i) (ip : Σ (i : Fin n), VSCR.Port i),
    (op, ip) ∈ CSCR → VSCR.OutPortVal op.1 op.2 = VSCR.PortVal ip.1 ip.2

def IsSystemConnectivity {n : Nat} (VSCR : PortSystemVector n)
    (CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))) : Prop :=
  IsOneToOneRelation CSCR ∧
  IsProperDomain CSCR ∧
  IsProperRange CSCR ∧
  PortCompatibility VSCR CSCR

/--
  [textbook/definition3.7/definition/feedforward_connection]
  A connection is feedforward if the output port belongs to system `i`
  and the input port belongs to system `j` such that `i < j`.
-/
def IsFeedforward {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 < p.2.1

/--
  [textbook/definition3.7/definition/feedback_connection]
  A connection is feedback if the output port belongs to system `i`
  and the input port belongs to system `j` such that `i ≥ j`.
-/
def IsFeedback {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 ≥ p.2.1

/--
  [textbook/definition3.11/definition/system_coupling_recipe]
  [textbook/definition3.11/interpretation/vscr]
  [textbook/definition3.11/interpretation/cscr]
  A system coupling recipe is a pair SCR = (VSCR, CSCR) where VSCR is a connectable
  vector of systems and CSCR is a system connectivity for VSCR.
-/
structure SystemCouplingRecipe (n : Nat) where
  VSCR : PortSystemVector n
  CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))
  connectivity : IsSystemConnectivity VSCR CSCR

/--
  [textbook/definition3.11/definition/coscr]
  The set of output ports connected by the coupling recipe SCR.
-/
def COSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  { op | ∃ ip, (op, ip) ∈ SCR.CSCR }

/--
  [textbook/definition3.11/definition/ciscr]
  The set of input ports connected by the coupling recipe SCR.
-/
def CISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  { ip | ∃ op, (op, ip) ∈ SCR.CSCR }

/--
  [textbook/definition3.11/definition/uoscr]
  The set of output ports unconnected by the coupling recipe SCR.
-/
def UOSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  (COSCR SCR)ᶜ

/--
  [textbook/definition3.11/definition/uiscr]
  The set of input ports unconnected by the coupling recipe SCR.
-/
def UISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  (CISCR SCR)ᶜ

/--
  [textbook/definition3.11/definition/interface]
  The interface between system `i` and system `j` specified by SCR
  is the set of connections in CSCR involving only ports of system `i` and system `j`.
-/
def SCRInterface {n : Nat} (SCR : SystemCouplingRecipe n) (i j : Fin n) :
    Set ((Σ (k : Fin n), SCR.VSCR.OutPort k) × (Σ (k : Fin n), SCR.VSCR.Port k)) :=
  { p ∈ SCR.CSCR | (p.1.1 = i ∧ p.2.1 = j) ∨ (p.1.1 = j ∧ p.2.1 = i) }

/--
  [textbook/definition3.15/definition/conjunctive_scr]
  A system coupling recipe is conjunctive if and only if CSCR is empty.
-/
def IsConjunctive {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  SCR.CSCR = ∅

/--
  [textbook/definition3.19/definition/cascade_scr]
  A system coupling recipe is cascade if and only if CSCR contains no feedback connections.
-/
def IsCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∀ p ∈ SCR.CSCR, ¬ IsFeedback p

/--
  [textbook/definition3.19/definition/essentially_cascade_scr]
  A system coupling recipe is essentially cascade if there exists a permutation of the
  component systems such that the reordered recipe is cascade.
-/
def IsEssentiallyCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∃ (g : Fin n ≃ Fin n), ∀ p ∈ SCR.CSCR, g p.1.1 < g p.2.1

/--
  [textbook/definition3.26/definition/singular_scr]
  A system coupling recipe is singular if and only if:
  1. VSCR contains only a single system component (length n = 1)
  2. CSCR is empty
-/
def IsSingular {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR = ∅

/--
  [textbook/definition3.29/definition/pure_feedback_scr]
  A system coupling recipe is pure feedback if and only if:
  1. VSCR contains only a single system component (length n = 1)
  2. CSCR is not empty
-/
def IsPureFeedback {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR ≠ ∅

/--
  [textbook/theorem3.31/theorem/class_in_themselves]
  [textbook/theorem3.31/proof/not_singular_conjunctive]
  [textbook/theorem3.31/proof/not_cascade]
  Pure feedback coupling recipes are neither singular, conjunctive, nor cascade.
-/
theorem pure_feedback_not_other {n : Nat} (SCR : SystemCouplingRecipe n) (h : IsPureFeedback SCR) :
    ¬ IsSingular SCR ∧ ¬ IsConjunctive SCR ∧ ¬ IsCascade SCR := by
  have hn : n = 1 := h.1
  have hne : SCR.CSCR ≠ ∅ := h.2
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
      have h_feed : IsFeedback p := by
        unfold IsFeedback
        rw [heq]
      have h_not_feed := h_cas p hp
      exact h_not_feed h_feed

/--
  [textbook/definition3.33/definition/mixed_scr]
  A system coupling recipe is mixed if it is not singular, conjunctive, cascade,
  essentially cascade, or pure feedback.
-/
def IsMixed {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ¬ IsSingular SCR ∧ ¬ IsConjunctive SCR ∧ ¬ IsCascade SCR ∧
  ¬ IsEssentiallyCascade SCR ∧ ¬ IsPureFeedback SCR

/--
  [textbook/definition3.40/definition/csy]
  [textbook/definition3.40/definition/sz]
  [textbook/definition3.40/definition/iz]
  [textbook/definition3.40/definition/oz]
  [textbook/definition3.40/definition/nz]
  [textbook/definition3.40/definition/rz]
  The parallel (conjunctive) composition of a connectable vector of systems.
  Returns a new FSMSystem where:
  - State space is the product of the component state spaces.
  - Input space is the product of the input sets of all component input ports.
  - Output space is the product of the output sets of all component output ports.
  - NZ transitions each component system independently.
  - RZ reads out each component port independently.
-/
def csy {n : Nat} (VSCR : PortSystemVector n) :
    FSMSystem
      ((i : Fin n) → VSCR.SZ i)
      ((ip : Σ (i : Fin n), VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      ((op : Σ (i : Fin n), VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) where
  sz_nonempty := by
    have h_non : ∀ i, Nonempty (VSCR.SZ i) := fun i => (VSCR.Z i).sz_nonempty
    exact ⟨fun i => Classical.choice (h_non i)⟩
  sz_finite := by
    haveI : ∀ i, Fintype (VSCR.SZ i) := fun i => (VSCR.Z i).sz_finite
    infer_instance
  iz_finite := by
    haveI : ∀ i, Fintype (VSCR.Port i) := VSCR.Port_finite
    haveI : ∀ i, DecidableEq (VSCR.Port i) := VSCR.Port_decidable
    haveI : ∀ (ip : Σ i, VSCR.Port i), Fintype (VSCR.PortVal ip.fst ip.snd) :=
      fun ip => VSCR.PortVal_finite ip.fst ip.snd
    infer_instance
  oz_finite := by
    haveI : ∀ i, Fintype (VSCR.OutPort i) := VSCR.OutPort_finite
    haveI : ∀ i, DecidableEq (VSCR.OutPort i) := VSCR.OutPort_decidable
    haveI : ∀ (op : Σ i, VSCR.OutPort i), Fintype (VSCR.OutPortVal op.fst op.snd) :=
      fun op => VSCR.OutPortVal_finite op.fst op.snd
    infer_instance
  NZ := fun x po i => (VSCR.Z i).NZ (x i) (fun port => po ⟨i, port⟩)
  RZ := fun x op => (VSCR.Z op.1).RZ (x op.1) op.2

/--
  [textbook/definition3.40/definition/ip_map]
  Function mapping the input ports of the conjunctive system to the input ports
  of the component systems (modeled as the identity function since they share the same type).
-/
def csy_IP_map {n : Nat} (VSCR : PortSystemVector n) :
    (Σ (i : Fin n), VSCR.Port i) → (Σ (i : Fin n), VSCR.Port i) :=
  ID _

/--
  [textbook/definition3.40/definition/inip_map]
  The inverse mapping of the conjunctive system input ports to component input ports.
-/
def csy_INIP_map {n : Nat} (VSCR : PortSystemVector n) :
    (Σ (i : Fin n), VSCR.Port i) → (Σ (i : Fin n), VSCR.Port i) :=
  ID _

/--
  [textbook/definition3.40/definition/is_map]
  The input port structure function of the conjunctive system (returns the value type of each port).
-/
def csy_IS_map {n : Nat} (VSCR : PortSystemVector n) (ip : Σ (i : Fin n), VSCR.Port i) : Type :=
  VSCR.PortVal ip.1 ip.2

/--
  [textbook/definition3.40/definition/op_map]
  Function mapping the output ports of the conjunctive system to the output ports
  of the component systems (modeled as the identity function since they share the same type).
-/
def csy_OP_map {n : Nat} (VSCR : PortSystemVector n) :
    (Σ (i : Fin n), VSCR.OutPort i) → (Σ (i : Fin n), VSCR.OutPort i) :=
  ID _

/--
  [textbook/definition3.40/definition/inop_map]
  The inverse mapping of the conjunctive system output ports to component output ports.
-/
def csy_INOP_map {n : Nat} (VSCR : PortSystemVector n) :
    (Σ (i : Fin n), VSCR.OutPort i) → (Σ (i : Fin n), VSCR.OutPort i) :=
  ID _

/--
  [textbook/definition3.40/definition/os_map]
  The output port structure function of the conjunctive system (returns the value type of each port).
-/
def csy_OS_map {n : Nat} (VSCR : PortSystemVector n) (op : Σ (i : Fin n), VSCR.OutPort i) : Type :=
  VSCR.OutPortVal op.1 op.2

/--
  [textbook/theorem_a1.219/theorem/vector_value_fns]
  The product function of a family of functions, mapping the product domain
  to the product codomain.
-/
def product_fun {I : Type} {A B : I → Type} (f : (i : I) → A i → B i) :
    ((i : I) → A i) → ((i : I) → B i) :=
  fun x i => f i (x i)

/--
  [textbook/theorem3.42/theorem/csy_parameterization]
  [textbook/theorem3.42/proof/dsystems]
  [textbook/theorem3.42/proof/existence]
  [textbook/theorem3.42/proof/uniqueness]
  The parallel composition `csy` defines a valid system parameterization.
-/
def csy_parameterization (n : Nat) :
    FSMSystemParameterization (PortSystemVector n)
      (fun VSCR => (i : Fin n) → VSCR.SZ i)
      (fun VSCR => (ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      (fun VSCR => (op : Σ i, VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) :=
  fun VSCR => csy VSCR

/--
  [textbook/theorem3.45/theorem/trajectories_relation]
  [textbook/theorem3.45/proof/state_zero]
  [textbook/theorem3.45/proof/state_induction]
  The state trajectory of a conjunctive (parallel) system evaluated at component `i`
  is equal to the state trajectory of the `i`-th component system running under projected inputs.
-/
theorem csy_state_trajectory {n : Nat} (VSCR : PortSystemVector n) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZ ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) :
    generateStateTrajectory (csy VSCR) x f t i =
    generateStateTrajectory (VSCR.Z i) (x i) (fun t port => f t ⟨i, port⟩) t := by
  induction t generalizing i with
  | zero => simp [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ, csy]
    congr 1
    exact ih i

theorem csy_output_trajectory {n : Nat} (VSCR : PortSystemVector n) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZ ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n)
    (B' : VSCR.OutPort i) :
    (generateOutputTrajectory (csy VSCR) x f t).map (fun r => r ⟨i, B'⟩) =
    (generateOutputTrajectory (VSCR.Z i) (x i) (fun t port => f t ⟨i, port⟩) t).map (fun r => r B') := by
  have hst := csy_state_trajectory VSCR x f t i
  rw [generateOutputTrajectory_eq, generateOutputTrajectory_eq]
  dsimp [csy] at hst ⊢
  rw [hst]

end FSM

export FSM (FSMSystem generateStateTrajectory generateOutputTrajectory StateEquiv Reachable
  IsValidStateTrajectory IsValidOutputTrajectory SystemMorphism outputTrajectory_unique
  generateStateTrajectory_zero generateStateTrajectory_succ generateOutputTrajectory_eq reachable_iff stateEquiv_iff)

