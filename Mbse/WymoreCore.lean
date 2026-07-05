import Mathlib.Data.Fintype.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Basic



/-!
# General Wymore Discrete Systems (Definition 2.4)

Faithful encoding of Wayne Wymore's discrete system quintuple `Z = (SZ, IZ, OZ, NZ, RZ)` from
Definition 2.4: `SZ` is any nonempty type (infinite state spaces allowed). Definition 2.11
finiteness is a derived predicate (`IsFinite`), not a construction rule.

* `NZ : SZ → Option IZ → SZ` — `some i` is an input-driven step; `none` is autonomous (empty-input
  systems evolve via `fun _ => none`).
* `RZ : SZ → Option OZ` — `none` models no output (closed systems).

Open Moore machines use `DiscreteSystem.ofTotal`. For finite Moore development (Def 2.11, Ch. 3,
`Z2`, `csy`), see [`FiniteWymore`](FiniteWymore.lean).
-/

/--
  [textbook/definition2.4/component/Z] [textbook/definition2.4/component/SZ] [textbook/definition2.4/component/IZ] [textbook/definition2.4/component/OZ]
  A discrete system is a quintuple: Z = (SZ, IZ, OZ, NZ, RZ) where:
  - Z is the name of the system
  - SZ is the set of states of the discrete system Z
  - IZ is the set of inputs of the discrete system Z
  - OZ is the set of outputs of the discrete system Z
-/
structure DiscreteSystem (SZ : Type) (IZ : Type) (OZ : Type) where
    /-- [textbook/definition2.4/constraint/sz_nonempty] Proof that the state space SZ is not empty -/
    sz_nonempty : Nonempty SZ

    /-- [textbook/definition2.4/component/NZ] [textbook/definition2.4/constraint/nz_signature]
        Next State Function: NZ ∈ FNS(SZ × IZ, SZ) when inputs are present (`some i`), and
        NZ ∈ FNS(SZ, SZ) for autonomous steps (`none`) when IZ is empty. -/
    NZ : SZ → Option IZ → SZ

    /-- [textbook/definition2.4/component/RZ] [textbook/definition2.4/constraint/rz_signature]
        Readout Function: RZ ∈ FNS(SZ, OZ) on states that produce output (`some o`); `none` when OZ is empty. -/
    RZ : SZ → Option OZ

/-- Open Moore fragment: total NZ/RZ wrapped in `some`; autonomous steps stutter. -/
def DiscreteSystem.ofTotal {SZ IZ OZ : Type} (NZ : SZ → IZ → SZ) (RZ : SZ → OZ) (hNE : Nonempty SZ) :
    DiscreteSystem SZ IZ OZ where
  sz_nonempty := hNE
  NZ := fun s oi => match oi with | some i => NZ s i | none => s
  RZ := fun s => some (RZ s)

/-- [textbook/definition2.4/component/TZ] The time scale TZ of the discrete system defined as IJS++ (natural numbers). -/
abbrev Time := Nat

/--
  The graph relation of a function `f : A → B`, i.e. `{(a, b) | b = f a} ⊆ A × B`.
-/
def FunctionGraph {A B : Type} (f : A → B) : Set (A × B) :=
  { p | p.2 = f p.1 }

/--
  [textbook/definition_a1.155/requirement/relation]
  [textbook/definition_a1.155/requirement/totality]
  [textbook/definition_a1.155/requirement/single_valuedness]
  A function `f : A → B` satisfies the FNS (function space) properties of Definition A1.155,
  stated explicitly over its graph relation `{(a, b) | b = f a}`:
  1. Relation: the graph is a subset of `A × B` (carried by the type of `FunctionGraph`).
  2. Totality: for every `a : A` there is a `b : B` with `(a, b)` in the graph.
  3. Single-valuedness: if `(a, b₁)` and `(a, b₂)` are in the graph, then `b₁ = b₂`.
-/
def SatisfiesFNS {A B : Type} (f : A → B) : Prop :=
  (∀ a : A, ∃ b : B, (a, b) ∈ FunctionGraph f) ∧
  (∀ (a : A) (b₁ b₂ : B), (a, b₁) ∈ FunctionGraph f → (a, b₂) ∈ FunctionGraph f → b₁ = b₂)

/-- Every Lean function satisfies the FNS properties (totality and single-valuedness). -/
theorem satisfiesFNS_of_function {A B : Type} (f : A → B) : SatisfiesFNS f := by
  constructor
  · intro a
    exact ⟨f a, rfl⟩
  · intro a b₁ b₂ h₁ h₂
    simp only [FunctionGraph, Set.mem_setOf_eq] at h₁ h₂
    rw [h₁, h₂]

/-- [textbook/definition2.4/implication/closed_system] A system is closed if both its input and output spaces are empty. -/
def IsClosed {SZ IZ OZ : Type} (_Z : DiscreteSystem SZ IZ OZ) : Prop :=
  IsEmpty IZ ∧ IsEmpty OZ

/-- [textbook/definition2.4/implication/open_system] A system is open if neither its input nor output spaces are empty. -/
def IsOpen {SZ IZ OZ : Type} (_Z : DiscreteSystem SZ IZ OZ) : Prop :=
  Nonempty IZ ∧ Nonempty OZ

/--
  [textbook/definition2.11/definition/finite_system]
  A Wymorian discrete system Z is finite if and only if SZ, IZ, and OZ are finite sets.
  On the general base this is a nontrivial classification predicate; every `FSMSystem`
  (see `FiniteWymore`) satisfies it via `fsm_isFinite`.
-/
def IsFinite {SZ IZ OZ : Type} (_Z : DiscreteSystem SZ IZ OZ) : Prop :=
  Finite SZ ∧ Finite IZ ∧ Finite OZ

/--
  [textbook/definition_a1.218/definition/range]
  The range (RNG) of a function with finite domain and decidable equality on the codomain.
  Used for the finite `#RNG(RZ) > 1` formulation of nontriviality (see `IsNontrivial` in `FSM`).
-/
def RNG {A B : Type} [Fintype A] [DecidableEq B] (f : A → B) : Finset B :=
  Finset.image f Finset.univ

/--
  [textbook/definition_a1.218/definition/domain]
  The domain (DMN) of a function `f : A → B` is the type `A`.
-/
abbrev DMN {A B : Type} (_f : A → B) : Type := A

/--
  [textbook/definition2.14/definition/nontrivial_system]
  [textbook/definition2.14/requirement/state_dependent_transition]
  [textbook/definition2.14/requirement/active_transition]
  [textbook/definition2.14/requirement/varying_output]
  A Wymorian discrete system Z is nontrivial if and only if:
  1. State-dependent transition: there exist x1, x2 : SZ and p : IZ such that Z.NZ x1 p ≠ Z.NZ x2 p
  2. Active transition: there exist x : SZ and p : IZ such that Z.NZ x p ≠ x
  3. Varying output: the readout takes at least two distinct values.

  Clause (iii) is stated without `Fintype` so it applies on infinite state spaces. The finite
  `#RNG(RZ) > 1` formulation lives in `FiniteWymore.FSM.IsNontrivial`.
-/
def IsNontrivial {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  (∃ (x1 x2 : SZ) (p : IZ), Z.NZ x1 (some p) ≠ Z.NZ x2 (some p)) ∧
  (∃ (x : SZ) (p : IZ), Z.NZ x (some p) ≠ x) ∧
  (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ Z.RZ s1 = some o1 ∧ Z.RZ s2 = some o2)

/--
  [textbook/definition2.14/implication/trivial_system]
  A system Z is trivial if and only if it is not nontrivial.
-/
def IsTrivial {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ¬ IsNontrivial Z

/--
  [textbook/definition_a1.185/definition/strings]
  The set of strings of elements of C is formalized as `List C`,
  representing finite sequences of elements of C.
-/
abbrev STRINGS (C : Type) : Type := List C

/--
  [textbook/definition_a1.185/definition/length]
  The length of a string LTH(f) is formalized as `List.length s` in Lean.
-/
def LTH {C : Type} (s : STRINGS C) : Nat := s.length

/--
  [textbook/definition2.23/definition/input_trajectory]
  An input trajectory (a finite segment of input) is any nonempty string of elements of IZ.
-/
def InputTrajectory (IZ : Type) := { s : STRINGS IZ // s ≠ [] }

-- We use variables here so we don't have to rewrite {SZ IZ OZ} for every definition
variable {SZ IZ OZ : Type}

/-- [textbook/definition2.23/definition/complete_input_trajectory] Complete input trajectories ITZ = FNS(TZ, IZ). -/
abbrev ITZ (IZ : Type) := Time → IZ

/-- [textbook/definition2.23/definition/complete_input_trajectory]
    Complete input trajectory with autonomous (`none`) steps: ITZW = FNS(TZ, Option IZ). -/
abbrev ITZW (IZ : Type) := Time → Option IZ

/-- Lift a total input trajectory to the generalized form (always `some`). -/
abbrev liftInput {IZ : Type} (f : ITZ IZ) : ITZW IZ := fun t => some (f t)

abbrev STZ (SZ : Type) := Time → SZ

/-- Output trajectories: partial readout along time. -/
abbrev OTZ (OZ : Type) := Time → Option OZ

/--
  [textbook/definition2.27/definition/state_trajectory_recurrence]
  State trajectory generated by recurrence on `NZ` from initial state `s0`.
-/
def generateStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : STZ SZ
  | 0 => s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)

/--
  [textbook/definition2.27/definition/state_at_time_t]
  The state of the system at time `t` under input trajectory `f` and initial state `s0`.
-/
theorem state_at_time (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (t : Time) :
    generateStateTrajectory Z s0 f t = generateStateTrajectory Z s0 f t := rfl

def StateTrajectoryGraph {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ) (s0 : SZ) :
    Set (Time × SZ) :=
  { p | p.2 = generateStateTrajectory Z s0 f p.1 }

/--
  [textbook/theorem2.29/proof/subset]
  The state trajectory graph is a subset of `TZ × SZ`.
-/
theorem stateTrajectoryGraph_subset {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ)
    (s0 : SZ) {t : Time} {y : SZ} (h : (t, y) ∈ StateTrajectoryGraph Z f s0) :
    y = generateStateTrajectory Z s0 f t := h

/--
  [textbook/theorem2.29/proof/totality]
  For every time `t`, the state trajectory graph contains a pair `(t, y)`.
-/
theorem stateTrajectoryGraph_total {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ)
    (s0 : SZ) (t : Time) :
    ∃ y : SZ, (t, y) ∈ StateTrajectoryGraph Z f s0 :=
  ⟨generateStateTrajectory Z s0 f t, rfl⟩

/--
  [textbook/theorem2.29/proof/single_valuedness]
  If two states appear at the same time in the graph, they are equal.
-/
theorem stateTrajectoryGraph_singleValued {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (f : ITZW IZ) (s0 : SZ) {t : Time} {y₁ y₂ : SZ}
    (h₁ : (t, y₁) ∈ StateTrajectoryGraph Z f s0)
    (h₂ : (t, y₂) ∈ StateTrajectoryGraph Z f s0) :
    y₁ = y₂ := by
  simp only [StateTrajectoryGraph, Set.mem_setOf_eq] at h₁ h₂
  exact h₁.trans h₂.symm

/--
  [textbook/theorem2.29/theorem/trajectory_fns]
  The generated state trajectory satisfies the FNS properties on `Time → SZ`.
-/
theorem generateStateTrajectory_satisfiesFNS (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SatisfiesFNS (generateStateTrajectory Z s0 f) :=
  satisfiesFNS_of_function _

def generateOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : OTZ OZ :=
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)

/--
  [textbook/theorem2.32/theorem/trajectory_value]
  The output at time `t` equals the readout of the state at time `t`.
-/
theorem generateOutputTrajectory_val (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (t : Time) :
    generateOutputTrajectory Z s0 f t = Z.RZ (generateStateTrajectory Z s0 f t) := rfl

/--
  [textbook/theorem2.32/theorem/trajectory_fns]
  The generated output trajectory satisfies the FNS properties on `Time → Option OZ`.
-/
theorem generateOutputTrajectory_satisfiesFNS (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SatisfiesFNS (generateOutputTrajectory Z s0 f) :=
  satisfiesFNS_of_function _

def IsValidStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ) (g : STZ SZ) : Prop :=
  ∀ t : Time, g (t + 1) = Z.NZ (g t) (f t)

def IsValidOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ) : Prop :=
  ∀ t : Time, h t = Z.RZ (g t)

/-! ## Simp lemmas for trajectory unfolding -/

@[simp]
theorem generateStateTrajectory_zero (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    generateStateTrajectory Z s0 f 0 = s0 := rfl

@[simp]
theorem generateStateTrajectory_succ (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (t : Time) :
    generateStateTrajectory Z s0 f (t + 1) = Z.NZ (generateStateTrajectory Z s0 f t) (f t) := rfl

theorem generateStateTrajectory_valid (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    IsValidStateTrajectory Z f (generateStateTrajectory Z s0 f) := by
  intro t; rfl

theorem generateOutputTrajectory_valid (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    IsValidOutputTrajectory Z (generateStateTrajectory Z s0 f) (generateOutputTrajectory Z s0 f) := by
  intro t; rfl

/--
  [textbook/theorem2.29/proof/single_valuedness]
  Given an initial state and input trajectory, the state trajectory is unique.
-/
theorem stateTrajectory_unique (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ) (g : STZ SZ) (s0 : SZ)
    (h_init : g 0 = s0) (h_valid : IsValidStateTrajectory Z f g) :
    ∀ t, g t = generateStateTrajectory Z s0 f t := by
  intro t
  induction t with
  | zero => exact h_init
  | succ n ih => rw [generateStateTrajectory_succ, h_valid n, ih]

theorem outputTrajectory_unique (Z : DiscreteSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ)
    (h_valid : IsValidOutputTrajectory Z g h) :
    ∀ t, h t = Z.RZ (g t) :=
  h_valid

def Reachable (Z : DiscreteSystem SZ IZ OZ) (s0 s : SZ) : Prop :=
  ∃ (f : ITZW IZ) (t : Time), generateStateTrajectory Z s0 f t = s

/--
  [textbook/definition2.51/terminology/by_means_of]
  State `s` is reachable from `s0` by means of input trajectory `f` at time `t`.
-/
def ReachableBy (Z : DiscreteSystem SZ IZ OZ) (s0 s : SZ) (f : ITZW IZ) (t : Time) : Prop :=
  generateStateTrajectory Z s0 f t = s

theorem reachable_iff_reachableBy (Z : DiscreteSystem SZ IZ OZ) (s0 s : SZ) :
    Reachable Z s0 s ↔ ∃ (f : ITZW IZ) (t : Time), ReachableBy Z s0 s f t :=
  Iff.rfl

theorem reachable_self (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) : Reachable Z s0 s0 :=
  ⟨fun _ => none, 0, rfl⟩

def StateEquiv (Z : DiscreteSystem SZ IZ OZ) (s1 s2 : SZ) : Prop :=
  ∀ (f : ITZW IZ) (t : Time),
    generateOutputTrajectory Z s1 f t = generateOutputTrajectory Z s2 f t

/-- State equivalence is reflexive. -/
theorem stateEquiv_refl (Z : DiscreteSystem SZ IZ OZ) (s : SZ) :
    StateEquiv Z s s := by
  intro _ _
  rfl

/-- State equivalence is symmetric. -/
theorem stateEquiv_symm (Z : DiscreteSystem SZ IZ OZ) (s1 s2 : SZ)
    (h : StateEquiv Z s1 s2) : StateEquiv Z s2 s1 := by
  intro f t
  exact (h f t).symm

/-- State equivalence is transitive. -/
theorem stateEquiv_trans (Z : DiscreteSystem SZ IZ OZ) (s1 s2 s3 : SZ)
    (h12 : StateEquiv Z s1 s2) (h23 : StateEquiv Z s2 s3) :
    StateEquiv Z s1 s3 := by
  intro f t
  exact (h12 f t).trans (h23 f t)

/-- A system morphism maps one system's components to another's while preserving
    the transition and readout structure. This is the foundation for system
    composition and refinement in T3SD. -/
structure SystemMorphism
    {SZ1 IZ1 OZ1 : Type} {SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1)
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) where
  φS : SZ1 → SZ2
  φI : IZ1 → IZ2
  φO : OZ1 → OZ2
  preserves_transition : ∀ s oi, φS (Z1.NZ s oi) = Z2.NZ (φS s) (oi.map φI)
  preserves_readout : ∀ s, (Z1.RZ s).map φO = Z2.RZ (φS s)

def translate {A : Type} (f : Time → A) (r : Time) : Time → A :=
  fun t => f (t + r)

def RSN {A B : Type} (f : A → B) (S : Set A) : {a : A // a ∈ S} → B :=
  fun ⟨a, _⟩ => f a

theorem rsn_eq_iff {A B : Type} (f g : A → B) (S : Set A) :
    RSN f S = RSN g S ↔ ∀ a ∈ S, f a = g a := by
  constructor
  · intro h a ha
    have h_app := congr_fun h ⟨a, ha⟩
    exact h_app
  · intro h
    funext ⟨a, ha⟩
    exact h a ha

def AlwaysOutputs {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ s, ∃ o, Z.RZ s = some o

theorem alwaysOutputs_not_none {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (s : SZ) (h : Z.RZ s = none) : False := by
  obtain ⟨o, ho⟩ := hOut s
  rw [h] at ho
  exact nomatch ho
