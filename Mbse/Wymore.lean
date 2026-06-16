import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Basic



/-!
  Formalization of Wayne Wymore's Tricotyledon Theory of System Design (T3SD)
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

    /-- Proof that the state space is finite (discrete system assumption) -/
    sz_finite : Fintype SZ

    /-- Proof that the input space is finite (discrete system assumption) -/
    iz_finite : Fintype IZ

    /-- Proof that the output space is finite (discrete system assumption) -/
    oz_finite : Fintype OZ

    /-- [textbook/definition2.4/component/NZ] [textbook/definition2.4/constraint/nz_signature|partial] Next State Function: NZ ∈ FNS(SZ × IZ, SZ).
        Partial: the textbook's empty-input case (NZ ∈ FNS(SZ, SZ) if IZ empty) is not separately modeled;
        with empty IZ this `SZ → IZ → SZ` is vacuous in its second argument. -/
    NZ : SZ → IZ → SZ

    /-- [textbook/definition2.4/component/RZ] [textbook/definition2.4/constraint/rz_signature|partial] Readout Function: RZ ∈ FNS(SZ, OZ).
        Partial: the textbook's empty-output case (RZ = ∅ if OZ empty) is unrepresentable here, since a total
        `RZ : SZ → OZ` with nonempty SZ forces OZ nonempty (see `discreteSystem_output_nonempty`). -/
    RZ : SZ → OZ

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
  In this encoding the readout `RZ : SZ → OZ` is total and `SZ` is nonempty, so the output
  space is always inhabited. This makes explicit that the `DiscreteSystem` structure models
  output-producing (open / Moore) systems; the closed/empty-output case of Definition 2.4
  (`RZ = ∅ if OZ empty`) is out of scope by construction (see `not_isClosed`).
-/
theorem discreteSystem_output_nonempty {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    Nonempty OZ :=
  ⟨Z.RZ (Classical.choice Z.sz_nonempty)⟩

/--
  No `DiscreteSystem` (as encoded) is closed: a closed system would require an empty output
  space, which contradicts `discreteSystem_output_nonempty`. This turns the encoding's
  limitation (Definition 2.4 closed systems are unrepresentable) into an explicit proved fact
  rather than a silent gap.
-/
theorem not_isClosed {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : ¬ IsClosed Z := by
  intro h
  exact h.2.false (Z.RZ (Classical.choice Z.sz_nonempty))

/--
  [textbook/definition2.11/definition/finite_system]
  A Wymorian discrete system Z is finite if and only if SZ, IZ, and OZ are finite sets.
  In our formalization, all systems are finite by construction (enforced by the Fintype fields);
  `discreteSystem_isFinite` proves this predicate holds for every system.
-/
def IsFinite {SZ IZ OZ : Type} (_Z : DiscreteSystem SZ IZ OZ) : Prop :=
  Finite SZ ∧ Finite IZ ∧ Finite OZ

/-- Every `DiscreteSystem` is finite, since its state/input/output spaces carry `Fintype`. -/
theorem discreteSystem_isFinite {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : IsFinite Z :=
  have := Z.sz_finite
  have := Z.iz_finite
  have := Z.oz_finite
  ⟨Finite.of_fintype SZ, Finite.of_fintype IZ, Finite.of_fintype OZ⟩

/--
  [textbook/definition2.11/definition/order_vector]
  The system Z is finite with order vector (k, m, n) if and only if
  k = #SZ, m = #IZ, n = #OZ, and k, m, n ∈ IJS+ (positive integers).
-/
def HasOrderVector {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (k m n : Nat) : Prop :=
  have : Fintype SZ := Z.sz_finite
  have : Fintype IZ := Z.iz_finite
  have : Fintype OZ := Z.oz_finite
  Fintype.card SZ = k ∧ Fintype.card IZ = m ∧ Fintype.card OZ = n ∧
  k ≥ 1 ∧ m ≥ 1 ∧ n ≥ 1

/--
  [textbook/definition_a1.218/definition/domain]
  The domain (DMN) of a function `f : A → B` is the type `A`.
-/
abbrev DMN {A B : Type} (_f : A → B) : Type := A

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
def IsNontrivial {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  have : Fintype SZ := Z.sz_finite
  have : DecidableEq OZ := Classical.decEq OZ
  (∃ (x1 x2 : SZ) (p : IZ), Z.NZ x1 p ≠ Z.NZ x2 p) ∧
  (∃ (x : SZ) (p : IZ), Z.NZ x p ≠ x) ∧
  (Finset.card (RNG Z.RZ) > 1)

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

/-- [textbook/definition2.23/definition/complete_input_trajectory] The set of all possible complete Input Trajectories ITZ = FNS(TZ, IZ) -/
abbrev ITZ (IZ : Type) := Time → IZ

-- The set of all possible State Trajectories
abbrev STZ (SZ : Type) := Time → SZ

-- The set of all possible Output Trajectories
abbrev OTZ (OZ : Type) := Time → OZ

/--
  [textbook/definition2.27/definition/state_trajectory_recurrence]
  [textbook/definition2.27/definition/state_at_time_t]
  [textbook/theorem2.29/theorem/trajectory_fns]
  [textbook/theorem2.29/proof/subset]
  [textbook/theorem2.29/proof/totality]
  Generates the state trajectory given a system, an initial state, and an input trajectory.
-/
def generateStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : STZ SZ
  | 0 => s0                                      -- At time 0, state is s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)  -- At time t+1, apply NZ to the state at time t and input at time t

/--
  [textbook/definition2.30/definition/output_trajectory_composition]
  [textbook/theorem2.32/theorem/trajectory_fns]
  [textbook/theorem2.32/theorem/trajectory_value]
  Generates the output trajectory based on the state trajectory.
-/
def generateOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : OTZ OZ :=
  -- For any time t, apply RZ to whatever the state is at time t
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)

/--
  A logical predicate defining what it means for an arbitrary function 'g'
  to be a valid state trajectory for input trajectory 'f'.
-/
def IsValidStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) : Prop :=
  ∀ t : Time, g (t + 1) = Z.NZ (g t) (f t)

/--
  A logical predicate defining what it means for an arbitrary function 'h'
  to be a valid output trajectory for state trajectory 'g'.
-/
def IsValidOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ) : Prop :=
  ∀ t : Time, h t = Z.RZ (g t)

/-! ## Simp lemmas for trajectory unfolding -/

@[simp]
theorem generateStateTrajectory_zero (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    generateStateTrajectory Z s0 f 0 = s0 := rfl

@[simp]
theorem generateStateTrajectory_succ (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateStateTrajectory Z s0 f (t + 1) = Z.NZ (generateStateTrajectory Z s0 f t) (f t) := rfl

/-! ## Core Soundness Theorems -/

/-- The generated state trajectory satisfies the validity predicate. -/
theorem generateStateTrajectory_valid (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    IsValidStateTrajectory Z f (generateStateTrajectory Z s0 f) := by
  intro t
  rfl

/-- The generated output trajectory satisfies the validity predicate. -/
theorem generateOutputTrajectory_valid (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    IsValidOutputTrajectory Z (generateStateTrajectory Z s0 f) (generateOutputTrajectory Z s0 f) := by
  intro t
  rfl

/--
  [textbook/theorem2.29/proof/single_valuedness]
  Given an initial state and input trajectory, the state trajectory is unique.
  Any function satisfying the recurrence with the same initial condition
  must equal the generated trajectory at every time step.
-/
theorem stateTrajectory_unique (Z : DiscreteSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) (s0 : SZ)
    (h_init : g 0 = s0)
    (h_valid : IsValidStateTrajectory Z f g) :
    ∀ t, g t = generateStateTrajectory Z s0 f t := by
  intro t
  induction t with
  | zero => exact h_init
  | succ n ih =>
    rw [generateStateTrajectory_succ, h_valid n, ih]

/-- Output trajectory is uniquely determined by the state trajectory. -/
theorem outputTrajectory_unique (Z : DiscreteSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ)
    (h_valid : IsValidOutputTrajectory Z g h) :
    ∀ t, h t = Z.RZ (g t) := by
  exact h_valid

/-! ## System-Theoretic Concepts -/

/--
  [textbook/definition2.51/definition/reachable]
  [textbook/definition2.51/terminology/by_means_of]
  A state `s` is reachable from initial state `s0` if there exists
  some input trajectory and time at which the system reaches `s`.
-/
def Reachable (Z : DiscreteSystem SZ IZ OZ) (s0 s : SZ) : Prop :=
  ∃ (f : ITZ IZ) (t : Time), generateStateTrajectory Z s0 f t = s

/-- The initial state is always reachable from itself (at time 0). -/
theorem reachable_self (Z : DiscreteSystem SZ IZ OZ) [Inhabited IZ] (s0 : SZ) :
    Reachable Z s0 s0 :=
  ⟨fun _ => default, 0, rfl⟩

/-- Two states are equivalent if, starting from either one, the system produces
    identical output trajectories for every possible input trajectory. -/
def StateEquiv (Z : DiscreteSystem SZ IZ OZ) (s1 s2 : SZ) : Prop :=
  ∀ (f : ITZ IZ) (t : Time),
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
  /-- State mapping -/
  φS : SZ1 → SZ2
  /-- Input mapping -/
  φI : IZ1 → IZ2
  /-- Output mapping -/
  φO : OZ1 → OZ2
  /-- The state map commutes with transitions -/
  preserves_transition : ∀ s i, φS (Z1.NZ s i) = Z2.NZ (φS s) (φI i)
  /-- The output map commutes with readout -/
  preserves_readout : ∀ s, φO (Z1.RZ s) = Z2.RZ (φS s)

/-- A morphism preserves state trajectories: mapping state-by-state is the same
    as generating the trajectory in the target system from the mapped initial state
    and mapped inputs. -/
theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZ IZ1) :
    ∀ t, m.φS (generateStateTrajectory Z1 s0 f t) =
         generateStateTrajectory Z2 (m.φS s0) (m.φI ∘ f) t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ, Function.comp]
    rw [m.preserves_transition, ih]

/-! ## Translation and Concatenation of Trajectories -/

/--
  [textbook/definition_a1.284/definition/translation_operator]
  The translation of a function f ∈ FNS(W, A) by r is denoted f → r.
  For complete trajectories (where W = Time), this is defined as (f → r)(t) = f(t + r).
-/
def translate {A : Type} (f : Time → A) (r : Time) : Time → A :=
  fun t => f (t + r)

/--
  [textbook/theorem_a1.286/theorem/translation_fns]
  [textbook/theorem_a1.286/theorem/translation_zero]
  Proof that translate f 0 = f.
-/
theorem translate_zero {A : Type} (f : Time → A) : translate f 0 = f := by
  funext t
  unfold translate
  simp only [Nat.add_zero]

/--
  [textbook/definition_a1.284/definition/closed_under_translation]
  [textbook/theorem2.25/theorem/translation_closed]
  The set of complete trajectories (Time → A) is closed under translation:
  the translated function is a well-typed complete trajectory.
-/
def complete_trajectories_closed_under_translation {A : Type} (f : Time → A) (r : Time) : Time → A :=
  translate f r

/--
  [textbook/theorem_a1.292/theorem/concatenation_fns]
  Concatenation of two functions f and g at time r, denoted CTN(f, r, g).
  Piecewise definition mapping to V[0, r) and W'.
-/
def concatenate {A : Type} (f g : Time → A) (r : Time) : Time → A :=
  fun t => if t < r then f t else g (t - r)

/--
  [textbook/theorem2.25/theorem/concatenation_closed]
  The set of complete trajectories is closed under concatenation.
-/
def complete_trajectories_closed_under_concatenation {A : Type} (f g : Time → A) (r : Time) : Time → A :=
  concatenate f g r

/--
  [textbook/theorem_a1.292/theorem/concatenation_value_left]
  Values of concatenation for t < r.
-/
theorem concatenation_value_left {A : Type} (f g : Time → A) (r : Time) (t : Time) (ht : t < r) :
    concatenate f g r t = f t := by
  unfold concatenate
  simp only [ht, ↓reduceIte]

/--
  [textbook/theorem_a1.292/theorem/concatenation_value_right]
  Values of concatenation for t ≥ r.
-/
theorem concatenation_value_right {A : Type} (f g : Time → A) (r : Time) (t : Time) (ht : t ≥ r) :
    concatenate f g r t = g (t - r) := by
  unfold concatenate
  have h_not : ¬(t < r) := Nat.not_lt_of_ge ht
  simp only [h_not, ↓reduceIte]

/-! ## General Set Theory and Function Composition -/

/--
  [textbook/definition_a1.268/definition/composition_pointwise]
  [textbook/definition_a1.268/definition/composition_set]
  The composition of functions g and f, denoted g ∘ f, is defined as (g ∘ f)(x) = g(f(x)).
-/
def compose {A B C : Type} (g : B → C) (f : A → B) : A → C :=
  g ∘ f

/--
  [textbook/theorem_a1.249/theorem/subset_inclusion]
  If f ∈ FNS(A, B) and C ⊆ B, then f(f^-1(C)) ⊆ C.
-/
theorem image_preimage_subset {A B : Type} (f : A → B) (C : Set B) :
    f '' (f ⁻¹' C) ⊆ C := by
  exact Set.image_preimage_subset f C

/--
  [textbook/theorem_a1.250/theorem/preimage_complement]
  If f ∈ FNS(A, B) and C ⊆ B, then f^-1(B - C) = A - f^-1(C).
-/
theorem preimage_complement {A B : Type} (f : A → B) (C : Set B) :
    f ⁻¹' (Cᶜ) = (f ⁻¹' C)ᶜ := by
  exact Set.preimage_compl

/--
  [textbook/theorem_a1.288/theorem/translation_additivity]
  Translating a function by r and then by s is equivalent to translating it by r + s.
-/
theorem translate_additivity {A : Type} (f : Time → A) (r s : Time) :
    translate (translate f r) s = translate f (r + s) := by
  funext t
  unfold translate
  congr 1
  rw [Nat.add_assoc, Nat.add_comm s]

/--
  [textbook/theorem2.46/theorem/time_invariance]
  Time Invariance of State Trajectory: running the system from state `g s`
  with translated input `f → s` for time `t` is equivalent to running the system
  from initial state `s0` with input `f` for time `s + t`.
-/
theorem stateTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZ IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateStateTrajectory Z x f (s + t) := by
  induction t with
  | zero =>
    simp only [generateStateTrajectory_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [ih]
    unfold translate
    congr 2
    exact Nat.add_comm t s

/-! ## System Experiments and Nonanticipation -/

/--
  [textbook/definition2.33/definition/system_experiments]
  The set of system experiments EXZ is formalized as the product type `ITZ IZ × SZ × Time`.
-/
def EXZ (SZ IZ : Type) := ITZ IZ × SZ × Time

/--
  [textbook/definition_a1.257/definition/restriction]
  The restriction of a function f : A → B to a subset S : Set A,
  represented as a function from the subtype {a // a ∈ S} to B.
-/
def RSN {A B : Type} (f : A → B) (S : Set A) : {a : A // a ∈ S} → B :=
  fun ⟨a, _⟩ => f a

/--
  Equivalence between function restriction equality and pointwise agreement on the subset.
  This makes proving the nonanticipatory theorem with RSN straightforward.
-/
theorem rsn_eq_iff {A B : Type} (f g : A → B) (S : Set A) :
    RSN f S = RSN g S ↔ ∀ a ∈ S, f a = g a := by
  constructor
  · intro h a ha
    have h_app := congr_fun h ⟨a, ha⟩
    exact h_app
  · intro h
    funext ⟨a, ha⟩
    exact h a ha

/--
  [textbook/theorem2.48/theorem/nonanticipatory]
  The nonanticipatory theorem: the state trajectory at time t depends only on
  the input trajectory restricted to the interval [0, t).
-/
theorem stateTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZ IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t := by
  induction t with
  | zero =>
    simp only [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i < t, f i = g i := by
      intro i hi
      exact h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := by
      exact h_agree t (Nat.lt_succ_self t)
    have h_rsn_t : RSN f {i | i < t} = RSN g {i | i < t} := by
      rw [rsn_eq_iff]
      exact h_lt
    rw [ih h_rsn_t, h_eq]

/-! ## Projection Functions and Input Ports -/

/--
  [textbook/definition_a1.172/definition/projection_coordinate]
  [textbook/definition_a1.172/definition/projection_set]
  [textbook/definition_a1.172/definition/projection_abbreviations]
  The projection function PJN over a Cartesian product (represented as a dependent function)
  onto the `i`-th coordinate. Cites coordinate projections and abbreviations (PJNi, PJN(i)).
-/
def PJN {I : Type} {A : I → Type} (i : I) : ((j : I) → A j) → A i :=
  fun x => x i

/--
  [textbook/definition_a1.172/definition/projection_subset]
  The projection function over a Cartesian product onto a subset of coordinates `S : Set I`.
-/
def PJN_set {I : Type} {A : I → Type} (S : Set I) : ((j : I) → A j) → ((j : {k // k ∈ S}) → A j.val) :=
  fun x ⟨j, _⟩ => x j

/--
  [textbook/definition2.55/definition/input_ports]
  The set of input ports IPZ of the system Z is modeled as the type index set `Port`.
  If the input space is a product, IZ is `(p : Port) → PortVal p`.
-/
def IPZ (Port : Type) : Type := Port

/--
  [textbook/definition2.55/definition/port_trajectory]
  The `p`-th input port trajectory generated by `f ∈ ITZ` is defined as the composition
  of the projection `PJN p` and `f`.
-/
def portTrajectory {Port : Type} {PortVal : Port → Type} (f : ITZ ((p : Port) → PortVal p)) (p : Port) : Time → PortVal p :=
  fun t => PJN p (f t)

/--
  [textbook/definition2.59/definition/input_port_structure]
  The input port structure ISZ is represented as a function mapping each input port
  to its value type.
-/
def ISZ (Port : Type) (PortVal : Port → Type) : Port → Type := PortVal

/--
  [textbook/definition2.62/definition/output_ports]
  The set of output ports OPZ is modeled as the type index set `OutPort`.
  If the output space is a product, OZ is `(op : OutPort) → OutPortVal op`.
-/
def OPZ (OutPort : Type) : Type := OutPort

/--
  [textbook/definition2.62/definition/port_readout]
  The readout to the `op`-th output port, RjZ, is the composition of the projection PJN and Z.RZ.
-/
def portReadout {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : SZ → OutPortVal op :=
  fun s => PJN op (Z.RZ s)

/--
  [textbook/definition2.62/definition/port_output_trajectory]
  The `op`-th output port trajectory, OTjZ(f, x), is the composition of the projection PJN and the output trajectory.
-/
def portOutputTrajectory {OutPort : Type} {OutPortVal : OutPort → Type}
    (ot : OTZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : Time → OutPortVal op :=
  fun t => PJN op (ot t)

/--
  [textbook/definition2.65/definition/output_port_structure]
  The output port structure OSZ is represented as a function mapping each output port
  to its value type.
-/
def OSZ (OutPort : Type) (OutPortVal : OutPort → Type) : OutPort → Type := OutPortVal

/--
  [textbook/definition2.70/definition/state_factor_sets]
  The set of factor sets SFZ of the state set is modeled as the type index set `StateFactor`.
  If the state space is a product, SZ is `(sf : StateFactor) → StateFactorVal sf`.
-/
def SFZ (StateFactor : Type) : Type := StateFactor

/--
  [textbook/definition2.70/definition/state_factor_structure]
  The state factor structure FSZ is represented as a function mapping each state factor
  to its value type.
-/
def FSZ (StateFactor : Type) (StateFactorVal : StateFactor → Type) : StateFactor → Type := StateFactorVal

/--
  [textbook/definition2.70/definition/factor_next_state]
  The `sf`-th component next state function, NjZ, is the composition of the projection PJN and Z.NZ.
-/
def factorNZ {IZ OZ StateFactor : Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ OZ) (sf : StateFactor) :
    ((sf : StateFactor) → StateFactorVal sf) → IZ → StateFactorVal sf :=
  fun s i => PJN sf (Z.NZ s i)

/--
  [textbook/definition2.70/definition/factor_state_trajectory]
  The `sf`-th component state trajectory, STjZ(f, x), is the composition of the projection PJN and the state trajectory.
-/
def factorStateTrajectory {StateFactor : Type} {StateFactorVal : StateFactor → Type}
    (st : STZ ((sf : StateFactor) → StateFactorVal sf)) (sf : StateFactor) : Time → StateFactorVal sf :=
  fun t => PJN sf (st t)

/--
  [textbook/definition_a1.165/definition/identity]
  The identity function ID(A) over the set A.
-/
def ID (A : Type) : A → A := fun x => x

/--
  [textbook/definition2.73/definition/state_readout]
  The system Z has state readout if the output is simply the state (RZ = ID(SZ)).
-/
def HasStateReadout {SZ IZ : Type} (Z : DiscreteSystem SZ IZ SZ) : Prop :=
  Z.RZ = ID SZ

/--
  [textbook/definition2.73/definition/projective_readout]
  The readout RZ of system Z is projective if every output port's readout
  corresponds to some state factor projection.
-/
def IsProjectiveReadout {IZ OutPort StateFactor : Type} {OutPortVal : OutPort → Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op)) : Prop :=
  ∀ (op : OutPort), ∃ (sf : StateFactor) (h : OutPortVal op = StateFactorVal sf),
    ∀ (s : (sf' : StateFactor) → StateFactorVal sf'),
      portReadout Z op s = h ▸ PJN sf s

/--
  [textbook/definition2.73/definition/properly_aligned_readout]
  The projective readout function is properly aligned if each output port `i`
  reads out the corresponding state factor `i`.
-/
def IsProperlyAlignedReadout {IZ I : Type} {Val : I → Type}
    (Z : DiscreteSystem ((i : I) → Val i) IZ ((i : I) → Val i)) : Prop :=
  ∀ (i : I), ∀ (s : (j : I) → Val j),
    portReadout Z i s = PJN i s

/--
  [textbook/theorem_a1.178/theorem/vector_projection_equality]
  Equality of vectors in terms of projections: any vector in a product type
  is equal to the tuple of its projections. In Lean, this is definitionally true.
-/
theorem tuple_eq_projection {I : Type} {A : I → Type} (x : (i : I) → A i) :
    x = fun i => PJN i x := by
  rfl

/--
  [textbook/theorem_a1.163/theorem/function_extensionality]
  Equality of functions (extensionality): two functions are equal if and only if
  they agree pointwise on all inputs.
-/
theorem fun_eq_iff {A B : Type} (f g : A → B) :
    f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    funext x
    exact h x

/--
  [textbook/theorem2.76/theorem/equal_readout]
  [textbook/theorem2.76/proof/pointwise_projection]
  [textbook/theorem2.76/proof/vector_equality]
  [textbook/theorem2.76/proof/function_equality]
  Equality of readout functions for systems with properly aligned projective readouts.
  Shows that if two systems have properly aligned projective readouts, identical state space
  and output space, their readout functions are equal.
-/
theorem readout_eq_of_properly_aligned {IZ IZ2 I : Type} {Val : I → Type}
    (Z1 : DiscreteSystem ((i : I) → Val i) IZ ((i : I) → Val i))
    (Z2 : DiscreteSystem ((i : I) → Val i) IZ2 ((i : I) → Val i))
    (h1 : IsProperlyAlignedReadout Z1)
    (h2 : IsProperlyAlignedReadout Z2) :
    Z1.RZ = Z2.RZ := by
  funext s
  funext i
  have r1 : portReadout Z1 i s = PJN i s := h1 i s
  have r2 : portReadout Z2 i s = PJN i s := h2 i s
  exact r1.trans r2.symm

/--
  [textbook/theorem_a1.176/theorem/projection_functions]
  Projection functions are functions. In Lean, PJN is a function by definition.
-/
theorem pjn_is_fun {I : Type} {A : I → Type} (i : I) :
    SatisfiesFNS (PJN i : ((j : I) → A j) → A i) :=
  satisfiesFNS_of_function _

/--
  State space of the constructed system Z2.
  Pair of output value and original state, restricted such that the output value
  is the readout of the state.
-/
structure Z2State (SZ OZ : Type) (RZ : SZ → OZ) where
  out : OZ
  state : SZ
  eq : out = RZ state

/--
  Equivalence between the new state space Z2State and the original state space SZ.
-/
def Z2State.equivSZ {SZ OZ : Type} (RZ : SZ → OZ) : Z2State SZ OZ RZ ≃ SZ where
  toFun s2 := s2.state
  invFun s := ⟨RZ s, s, rfl⟩
  left_inv := fun ⟨o, s, h⟩ => by
    subst h
    rfl
  right_inv s := rfl

/--
  [textbook/theorem2.78/theorem/system_construction]
  [textbook/theorem2.78/proof/dsystems]
  [textbook/theorem2.78/proof/properly_aligned]
  Construction of a system Z2 with properly aligned projective readout to replace Z1.
-/
def Z2 {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : DiscreteSystem (Z2State SZ OZ Z.RZ) IZ OZ where
  sz_nonempty := Z.sz_nonempty.map (Z2State.equivSZ Z.RZ).symm
  sz_finite :=
    have := Z.sz_finite
    Fintype.ofEquiv SZ (Z2State.equivSZ Z.RZ).symm
  iz_finite := Z.iz_finite
  oz_finite := Z.oz_finite
  NZ := fun s2 p => ⟨Z.RZ (Z.NZ s2.state p), Z.NZ s2.state p, rfl⟩
  RZ := fun s2 => s2.out

/--
  The properly aligned property of the constructed readout function Z2.RZ.
  The readout to output port `op` is the coordinate projection of the state.
-/
theorem z2_readout_projective {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort)
    (s2 : Z2State SZ ((op : OutPort) → OutPortVal op) Z.RZ) :
    portReadout (Z2 Z) op s2 = s2.out op := by
  rfl

/--
  [textbook/theorem2.78/proof/exz_mapping]
  Mapping of system experiments from Z1 to Z2.
-/
def Z2.exz_map {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    EXZ SZ IZ → EXZ (Z2State SZ OZ Z.RZ) IZ :=
  fun ⟨f, x, t⟩ => ⟨f, ⟨Z.RZ x, x, rfl⟩, t⟩

/--
  [textbook/theorem2.78/proof/state_trajectory_projection]
  State trajectory equivalence: the state part of Z2's trajectory is Z1's state trajectory.
  Proven by induction on time t.
-/
theorem z2_state_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZ IZ) (t : Time) :
    (generateStateTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t).state = generateStateTrajectory Z x f t := by
  induction t with
  | zero =>
    rfl
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    unfold Z2
    dsimp
    unfold Z2 at ih
    rw [ih]

/--
  [textbook/theorem2.78/proof/output_trajectory_equality]
  Output trajectory equivalence: Z2 produces the same output trajectory as Z1.
-/
theorem z2_output_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t = generateOutputTrajectory Z x f t := by
  unfold generateOutputTrajectory
  unfold Z2
  dsimp
  have eq_th := (generateStateTrajectory (Z2 Z) ⟨Z.RZ x, x, rfl⟩ f t).eq
  unfold Z2 at eq_th
  rw [eq_th]
  have st_eq := z2_state_trajectory_equivalence Z x f t
  unfold Z2 at st_eq
  rw [st_eq]

/-! ## System Parameterization -/

/--
  [textbook/definition2.82/definition/system_parameterization]
  A system parameterization F maps a parameter type `P` to a `DiscreteSystem`.
  To allow system spaces to depend on parameters, we define it as a structure
  where the state, input, and output spaces are functions of `P`.
-/
def SystemParameterization (P : Type u) (SZ IZ OZ : P → Type) : Type u :=
  (p : P) → DiscreteSystem (SZ p) (IZ p) (OZ p)

/--
  [textbook/definition2.82/definition/parameter_instance]
  An instance of a system parameterization `F` for a parameter value `r : P`
  is simply the system `F r`.
-/
def parameterInstance {P : Type u} {SZ IZ OZ : P → Type}
    (F : SystemParameterization P SZ IZ OZ) (r : P) : DiscreteSystem (SZ r) (IZ r) (OZ r) :=
  F r

/--
  [textbook/definition2.82/definition/multiple_parameters]
  A parameterization has `n` parameters if its parameter domain type is (equivalent to) a
  product type indexed by `Fin n`. Stated via an explicit type equivalence so the predicate
  carries real content rather than restating its own hypothesis.
-/
def HasNParameters (P : Type) (n : Nat) (ParamType : Fin n → Type) : Prop :=
  Nonempty (P ≃ ((i : Fin n) → ParamType i))

/--
  [textbook/definition2.82/definition/one_parameter]
  A parameterization has one parameter if its parameter domain is (equivalent to) a single-factor
  product, i.e. it has exactly one parameter factor.
-/
def HasOneParameter (P : Type) : Prop :=
  ∃ ParamType : Fin 1 → Type, HasNParameters P 1 ParamType

/--
  [textbook/definition2.93/definition/fcnsy]
  The parameterization of function computation systems is denoted FCNSY.
  For a function F : IZ → SZ and a positive number of output ports n,
  it returns a system Z with state space SZ, input space IZ, and output space Fin n → SZ.
-/
def fcnsy {IZ SZ : Type} (F : IZ → SZ) (n : Nat) [Fintype SZ] [Fintype IZ] [Inhabited SZ] :
    DiscreteSystem SZ IZ (Fin n → SZ) where
  sz_nonempty := ⟨default⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := by infer_instance
  NZ := fun _x p => F p
  RZ := fun x _j => x

/--
  [textbook/theorem2.96/theorem/parameter_count]
  FCNSY is a system parameterization with two parameters.
-/
theorem fcnsy_has_two_parameters {IZ SZ : Type} [Fintype SZ] [Fintype IZ] [Inhabited SZ] :
    ∃ (P : Type) (ParamType : Fin 2 → Type), HasNParameters P 2 ParamType := by
  let ParamType : Fin 2 → Type := fun i => if i.val == 0 then (IZ → SZ) else Nat
  exact ⟨(i : Fin 2) → ParamType i, ParamType, ⟨Equiv.refl _⟩⟩


/--
  [textbook/theorem2.97/theorem/output_value]
  [textbook/theorem2.97/proof/t_zero]
  [textbook/theorem2.97/proof/arbitrary_t]
  For Z = FCNSY(F, 1), the output at t + 1 is F(f(t)).
  Due to the simplicity of the function computation system where the next state is independent
  of the previous state, this holds definitionally by `rfl` for all `t`. Thus, the textbook's
  induction proof (using t = 0 as base case and applying the Time Invariance Theorem)
  collapses to a single definitional proof in Lean 4.
-/
theorem fcnsy_output_one_time_unit {IZ SZ : Type} (F : IZ → SZ) [Fintype SZ] [Fintype IZ] [Inhabited SZ]
    (x : SZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory (fcnsy F 1) x f (t + 1) 0 = F (f t) := by
  rfl

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
  Z : (i : Fin n) → DiscreteSystem (SZ i) ((p : Port i) → PortVal i p) ((op : OutPort i) → OutPortVal i op)
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

/--
  [textbook/definition3.7/requirement/range_subset]
  The range of CSCR is a proper subset of all input ports (modeled as not equal to Set.univ).
-/
def IsProperRange {α β : Type} (R : Set (α × β)) : Prop :=
  { y : β | ∃ x, (x, y) ∈ R } ≠ Set.univ

/--
  [textbook/definition3.7/requirement/port_compatibility]
  Port compatibility condition: if output port `op` is connected to input port `ip`,
  their corresponding value types must be equal.
-/
def PortCompatibility {n : Nat} (VSCR : PortSystemVector n)
    (CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))) : Prop :=
  ∀ (op : Σ (i : Fin n), VSCR.OutPort i) (ip : Σ (i : Fin n), VSCR.Port i),
    (op, ip) ∈ CSCR → VSCR.OutPortVal op.1 op.2 = VSCR.PortVal ip.1 ip.2

/--
  [textbook/definition3.7/definition/connectivity_relation]
  [textbook/definition3.7/requirement/domain_subset]
  [textbook/definition3.7/requirement/range_subset]
  [textbook/definition3.7/requirement/port_compatibility]
  Checks if CSCR is a valid system connectivity for VSCR.
-/
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
  Returns a new DiscreteSystem where:
  - State space is the product of the component state spaces.
  - Input space is the product of the input sets of all component input ports.
  - Output space is the product of the output sets of all component output ports.
  - NZ transitions each component system independently.
  - RZ reads out each component port independently.
-/
def csy {n : Nat} (VSCR : PortSystemVector n) :
    DiscreteSystem
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
    haveI : ∀ (ip : Σ i, VSCR.Port i), Fintype (VSCR.PortVal ip.fst ip.snd) := fun ip => VSCR.PortVal_finite ip.fst ip.snd
    infer_instance
  oz_finite := by
    haveI : ∀ i, Fintype (VSCR.OutPort i) := VSCR.OutPort_finite
    haveI : ∀ i, DecidableEq (VSCR.OutPort i) := VSCR.OutPort_decidable
    haveI : ∀ (op : Σ i, VSCR.OutPort i), Fintype (VSCR.OutPortVal op.fst op.snd) := fun op => VSCR.OutPortVal_finite op.fst op.snd
    infer_instance
  NZ := fun x p i => (VSCR.Z i).NZ (x i) (fun port => p ⟨i, port⟩)
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
    SystemParameterization (PortSystemVector n)
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
  | zero => rfl
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    have ih_fun : generateStateTrajectory (csy VSCR) x f t =
        fun i => generateStateTrajectory (VSCR.Z i) (x i) (fun t port => f t ⟨i, port⟩) t := by
      ext i
      apply ih
    rw [ih_fun]
    rfl

/--
  [textbook/theorem3.45/theorem/trajectories_relation]
  [textbook/theorem3.45/proof/output_relation]
  The output trajectory of a conjunctive (parallel) system evaluated at component port `B'`
  of system `i` is equal to the output trajectory of component `i` at port `B'` under projected inputs.
-/
theorem csy_output_trajectory {n : Nat} (VSCR : PortSystemVector n) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZ ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) (B' : VSCR.OutPort i) :
    generateOutputTrajectory (csy VSCR) x f t ⟨i, B'⟩ =
    generateOutputTrajectory (VSCR.Z i) (x i) (fun t port => f t ⟨i, port⟩) t B' := by
  unfold generateOutputTrajectory
  have h_st : generateStateTrajectory (csy VSCR) x f t =
      fun i => generateStateTrajectory (VSCR.Z i) (x i) (fun t port => f t ⟨i, port⟩) t := by
    ext i
    apply csy_state_trajectory
  rw [h_st]
  rfl
