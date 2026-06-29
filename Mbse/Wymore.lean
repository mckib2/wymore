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
  On finite systems, clause (iii) of nontriviality (`∃` two distinct outputs) is equivalent to
  `#RNG(RZ) > 1`. DTT strategy (proof comparison §13): forward via `Finset.insert`;
  backward via `Finset.card_le_two` / two-element witness from `card > 1`.
-/
theorem varyingOutput_iff_card_rng {SZ OZ : Type} [Fintype SZ] [Fintype OZ] [DecidableEq OZ]
    (RZ : SZ → OZ) :
    (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ RZ s1 = o1 ∧ RZ s2 = o2) ↔
    Finset.card (RNG RZ) > 1 := by
  constructor
  · rintro ⟨o1, o2, s1, s2, ho, h1, h2⟩
    refine (Finset.one_lt_card_iff).2 ⟨o1, o2, ?_, ?_, ho⟩
    · exact Finset.mem_image.mpr ⟨s1, Finset.mem_univ _, h1⟩
    · exact Finset.mem_image.mpr ⟨s2, Finset.mem_univ _, h2⟩
  · intro h
    obtain ⟨o1, o2, hm1, hm2, ho⟩ := (Finset.one_lt_card_iff).1 h
    obtain ⟨s1, _, hs1⟩ := Finset.mem_image.mp hm1
    obtain ⟨s2, _, hs2⟩ := Finset.mem_image.mp hm2
    exact ⟨o1, o2, s1, s2, ho, hs1, hs2⟩

/--
  On a finite discrete system, general `IsNontrivial` clause (iii) matches the textbook
  `#RNG(RZ) > 1` formulation.
-/
theorem isNontrivial_varyingOutput_iff_ofTotal {SZ IZ OZ : Type} [Fintype SZ] [Fintype OZ] [DecidableEq OZ]
    (NZ : SZ → IZ → SZ) (RZ : SZ → OZ) (hNE : Nonempty SZ) :
    let Z := DiscreteSystem.ofTotal NZ RZ hNE
    (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ Z.RZ s1 = some o1 ∧ Z.RZ s2 = some o2) ↔
    Finset.card (RNG RZ) > 1 := by
  constructor
  · intro h
    rcases h with ⟨o1, o2, s1, s2, ho, h1, h2⟩
    simp [DiscreteSystem.ofTotal] at h1 h2
    exact (varyingOutput_iff_card_rng RZ).mp ⟨o1, o2, s1, s2, ho, h1, h2⟩
  · intro h
    rcases (varyingOutput_iff_card_rng RZ).mpr h with ⟨o1, o2, s1, s2, ho, h1, h2⟩
    exact ⟨o1, o2, s1, s2, ho, by simp [DiscreteSystem.ofTotal, h1], by simp [DiscreteSystem.ofTotal, h2]⟩

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

def generateStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : STZ SZ
  | 0 => s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)

def generateOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : OTZ OZ :=
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)

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

theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, m.φS (generateStateTrajectory Z1 s0 f t) =
         generateStateTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ]
    rw [m.preserves_transition, ih]

theorem morphism_preserves_output_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, (generateOutputTrajectory Z1 s0 f t).map m.φO =
         generateOutputTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t := by
  intro t
  unfold generateOutputTrajectory
  rw [m.preserves_readout, morphism_preserves_state_trajectory m s0 f t]

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
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateStateTrajectory Z x f (s + t) := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [ih]
    unfold translate
    congr 2
    exact Nat.add_comm t s

theorem outputTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateOutputTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateOutputTrajectory Z x f (s + t) := by
  unfold generateOutputTrajectory
  rw [stateTrajectory_time_invariance Z x f s t]

def EXZ (SZ IZ : Type) := ITZW IZ × SZ × Time

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
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i < t, f i = g i := fun i hi =>
      h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := h_agree t (Nat.lt_succ_self t)
    have h_rsn_t : RSN f {i | i < t} = RSN g {i | i < t} := by
      rw [rsn_eq_iff]; exact h_lt
    rw [ih h_rsn_t, h_eq]

theorem outputTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateOutputTrajectory Z x f t = generateOutputTrajectory Z x g t := by
  unfold generateOutputTrajectory
  rw [stateTrajectory_nonanticipatory Z x f g t h_agree]

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
def portTrajectory {Port : Type} {PortVal : Port → Type} (f : ITZW ((p : Port) → PortVal p)) (p : Port) :
    Time → Option (PortVal p) :=
  fun t => (f t).map (PJN p)

def portReadout {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) :
    SZ → Option (OutPortVal op) :=
  fun s => (Z.RZ s).map (PJN op)

def portOutputTrajectory {OutPort : Type} {OutPortVal : OutPort → Type}
    (ot : OTZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : Time → Option (OutPortVal op) :=
  fun t => (ot t).map (PJN op)

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
    ((sf : StateFactor) → StateFactorVal sf) → Option IZ → StateFactorVal sf :=
  fun s oi => PJN sf (Z.NZ s oi)

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
  Z.RZ = fun s => some s

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
    portReadout Z i s = some (PJN i s)

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
theorem readout_eq_of_properly_aligned {IZ IZ2 I : Type} {Val : I → Type} [Inhabited I]
    (Z1 : DiscreteSystem ((i : I) → Val i) IZ ((i : I) → Val i))
    (Z2 : DiscreteSystem ((i : I) → Val i) IZ2 ((i : I) → Val i))
    (h1 : IsProperlyAlignedReadout Z1)
    (h2 : IsProperlyAlignedReadout Z2) :
    Z1.RZ = Z2.RZ := by
  funext s
  have hproj1 : ∀ i, (Z1.RZ s).map (PJN i) = some (PJN i s) := fun i => h1 i s
  have hproj2 : ∀ i, (Z2.RZ s).map (PJN i) = some (PJN i s) := fun i => h2 i s
  match hz1 : Z1.RZ s, hz2 : Z2.RZ s with
  | some o1, some o2 =>
    apply Option.some_inj.mpr
    funext i
    have h1i := hproj1 i; rw [hz1, Option.map_some] at h1i
    have h2i := hproj2 i; rw [hz2, Option.map_some] at h2i
    exact Option.some_injective _ (h1i.trans h2i.symm)
  | none, _ => exact absurd (hproj1 default) (by rw [hz1]; simp)
  | some _, none => exact absurd (hproj2 default) (by rw [hz2]; simp)

/--
  [textbook/theorem_a1.176/theorem/projection_functions]
  Projection functions are functions. In Lean, PJN is a function by definition.
-/
theorem pjn_is_fun {I : Type} {A : I → Type} (i : I) :
    SatisfiesFNS (PJN i : ((j : I) → A j) → A i) :=
  satisfiesFNS_of_function _

/-! ## Z2 Construction (Theorem 2.78) -/

structure Z2State (SZ OZ : Type) (RZ : SZ → Option OZ) where
  out : OZ
  state : SZ
  eq : RZ state = some out

noncomputable def Z2State.mkFrom {SZ OZ : Type} (RZ : SZ → Option OZ)
    (h : ∀ s, ∃ o, RZ s = some o) (s : SZ) : Z2State SZ OZ RZ :=
  ⟨Classical.choose (h s), s, Classical.choose_spec (h s)⟩

noncomputable def Z2State.equivSZ {SZ OZ : Type} (RZ : SZ → Option OZ) (h : ∀ s, ∃ o, RZ s = some o) :
    Z2State SZ OZ RZ ≃ SZ where
  toFun s2 := s2.state
  invFun s := Z2State.mkFrom RZ h s
  left_inv := fun ⟨o, s, ho⟩ => by
    simp [Z2State.mkFrom, ho]
  right_inv _ := rfl

def AlwaysOutputs {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ s, ∃ o, Z.RZ s = some o

theorem alwaysOutputs_not_none {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (s : SZ) (h : Z.RZ s = none) : False := by
  obtain ⟨o, ho⟩ := hOut s
  rw [h] at ho
  exact nomatch ho

theorem ofTotal_alwaysOutputs {SZ IZ OZ : Type} (NZ : SZ → IZ → SZ) (RZ : SZ → OZ) (hNE : Nonempty SZ) :
    AlwaysOutputs (DiscreteSystem.ofTotal NZ RZ hNE) := by
  intro s; exact ⟨RZ s, rfl⟩

def Z2 {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    DiscreteSystem (Z2State SZ OZ Z.RZ) IZ OZ where
  sz_nonempty := Z.sz_nonempty.map (Z2State.equivSZ Z.RZ hOut).symm
  NZ := fun s2 oi =>
    let ns := Z.NZ s2.state oi
    match hrz : Z.RZ ns with
    | some o => ⟨o, ns, hrz⟩
    | none => (alwaysOutputs_not_none Z hOut ns hrz).elim
  RZ := fun s2 => some s2.out

theorem z2_readout_projective {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (hOut : AlwaysOutputs Z) (op : OutPort)
    (s2 : Z2State SZ ((op : OutPort) → OutPortVal op) Z.RZ) :
    portReadout (Z2 Z hOut) op s2 = some (s2.out op) := rfl

def Z2.exz_map {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    EXZ SZ IZ → EXZ (Z2State SZ OZ Z.RZ) IZ :=
  fun ⟨f, x, t⟩ =>
    match hrz : Z.RZ x with
    | some o => ⟨f, ⟨o, x, hrz⟩, t⟩
    | none => (alwaysOutputs_not_none Z hOut x hrz).elim

theorem z2_nz_state {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (s2 : Z2State SZ OZ Z.RZ) (oi : Option IZ) :
    ((Z2 Z hOut).NZ s2 oi).state = Z.NZ s2.state oi := by
  dsimp [Z2, Z2State.state]
  split
  · rfl
  · exact (alwaysOutputs_not_none Z hOut (Z.NZ s2.state oi) ‹_›).elim

theorem z2_state_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (x : SZ) (o : OZ) (f : ITZW IZ) (t : Time) (hrz : Z.RZ x = some o) :
    (generateStateTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t).state =
    generateStateTrajectory Z x f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [z2_nz_state Z hOut, ih]

theorem z2_output_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (x : SZ) (o : OZ) (f : ITZW IZ) (t : Time) (hrz : Z.RZ x = some o) :
    generateOutputTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t =
    generateOutputTrajectory Z x f t := by
  set s2t := generateStateTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t
  unfold generateOutputTrajectory
  rw [← z2_state_trajectory_equivalence Z hOut x o f t hrz]
  show (Z2 Z hOut).RZ s2t = Z.RZ s2t.state
  simp [Z2]
  exact s2t.eq.symm

/-! ## System Parameterization -/

/--
  [textbook/definition2.82/definition/system_parameterization]
  A system parameterization maps a parameter type `P` to a `DiscreteSystem`.
-/
def DiscreteSystemParameterization (P : Type) (SZ IZ OZ : P → Type) : Type :=
  (p : P) → DiscreteSystem (SZ p) (IZ p) (OZ p)

/--
  [textbook/definition2.82/definition/parameter_instance]
  An instance of a system parameterization `F` for a parameter value `r : P` is the system `F r`.
-/
def parameterInstance {P : Type} {SZ IZ OZ : P → Type}
    (F : DiscreteSystemParameterization P SZ IZ OZ) (r : P) :
    DiscreteSystem (SZ r) (IZ r) (OZ r) :=
  F r

def HasNParameters (P : Type) (n : Nat) (ParamType : Fin n → Type) : Prop :=
  Nonempty (P ≃ ((i : Fin n) → ParamType i))

/--
  [textbook/definition2.82/definition/one_parameter]
  A parameterization has one parameter if its parameter domain is equivalent to a single-factor product.
-/
def HasOneParameter (P : Type) : Prop :=
  ∃ ParamType : Fin 1 → Type, HasNParameters P 1 ParamType

/--
  [textbook/definition2.93/definition/fcnsy]
  The parameterization of function computation systems FCNSY.
-/
def fcnsy {IZ SZ : Type} (F : IZ → SZ) (n : Nat) [Inhabited SZ] :
    DiscreteSystem SZ IZ (Fin n → SZ) where
  sz_nonempty := ⟨default⟩
  NZ := fun _x oi => match oi with | some p => F p | none => default
  RZ := fun x => some (fun _j => x)

/--
  [textbook/theorem2.96/theorem/parameter_count]
  FCNSY is a system parameterization with two parameters.
-/
theorem fcnsy_has_two_parameters {IZ SZ : Type} [Inhabited SZ] :
    ∃ (P : Type) (ParamType : Fin 2 → Type), HasNParameters P 2 ParamType := by
  let ParamType : Fin 2 → Type := fun i => if i.val == 0 then (IZ → SZ) else Nat
  exact ⟨(i : Fin 2) → ParamType i, ParamType, ⟨Equiv.refl _⟩⟩

/--
  [textbook/theorem2.97/theorem/output_value]
  [textbook/theorem2.97/proof/t_zero]
  [textbook/theorem2.97/proof/arbitrary_t]
  For Z = FCNSY(F, 1), the output at t + 1 is F(f(t)).
  DTT strategy (proof comparison §9): state-independent NZ collapses to `rfl`.
-/
theorem fcnsy_output_one_time_unit {IZ SZ : Type} (F : IZ → SZ) [Inhabited SZ]
    (x : SZ) (f : ITZW IZ) (t : Time) (i : IZ) (hi : f t = some i) :
    (generateOutputTrajectory (fcnsy F 1) x f (t + 1)).map (fun a => a 0) = some (F i) := by
  simp [generateOutputTrajectory, generateStateTrajectory_succ, fcnsy, hi, Option.map_some]

/-! ## Chapter 3: System Coupling Recipes and Connectivity -/

/--
  [textbook/definition3.3/definition/connection_vector]
  [textbook/definition3.3/requirement/pairwise_distinct]
  A connectable vector of systems of length `n` (components may have infinite state spaces).
-/
structure PortSystemVector (n : Nat) where
  SZ : Fin n → Type
  Port : Fin n → Type
  PortVal : (i : Fin n) → Port i → Type
  OutPort : Fin n → Type
  OutPortVal : (i : Fin n) → OutPort i → Type
  Z : (i : Fin n) → DiscreteSystem (SZ i) ((p : Port i) → PortVal i p) ((op : OutPort i) → OutPortVal i op)
  distinct : ∀ (i j : Fin n), i ≠ j → ¬ HEq (Z i) (Z j)

def IsOneToOneRelation {α β : Type} (R : Set (α × β)) : Prop :=
  (∀ (x : α) (y1 y2 : β), (x, y1) ∈ R → (x, y2) ∈ R → y1 = y2) ∧
  (∀ (x1 x2 : α) (y : β), (x1, y) ∈ R → (x2, y) ∈ R → x1 = x2)

def IsProperDomain {α β : Type} (R : Set (α × β)) : Prop :=
  { x : α | ∃ y, (x, y) ∈ R } ≠ Set.univ

/--
  [textbook/definition3.7/requirement/range_subset]
  The range of CSCR is a proper subset of all input ports.
-/
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

def IsFeedforward {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 < p.2.1

def IsFeedback {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 ≥ p.2.1

structure SystemCouplingRecipe (n : Nat) where
  VSCR : PortSystemVector n
  CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))
  connectivity : IsSystemConnectivity VSCR CSCR

def COSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  { op | ∃ ip, (op, ip) ∈ SCR.CSCR }

def CISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  { ip | ∃ op, (op, ip) ∈ SCR.CSCR }

def UOSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  (COSCR SCR)ᶜ

def UISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  (CISCR SCR)ᶜ

def SCRInterface {n : Nat} (SCR : SystemCouplingRecipe n) (i j : Fin n) :
    Set ((Σ (k : Fin n), SCR.VSCR.OutPort k) × (Σ (k : Fin n), SCR.VSCR.Port k)) :=
  { p ∈ SCR.CSCR | (p.1.1 = i ∧ p.2.1 = j) ∨ (p.1.1 = j ∧ p.2.1 = i) }

def IsConjunctive {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  SCR.CSCR = ∅

def IsCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∀ p ∈ SCR.CSCR, ¬ IsFeedback p

def IsEssentiallyCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∃ (g : Fin n ≃ Fin n), ∀ p ∈ SCR.CSCR, g p.1.1 < g p.2.1

def IsSingular {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR = ∅

def IsPureFeedback {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR ≠ ∅

/--
  [textbook/theorem3.31/theorem/class_in_themselves]
  [textbook/theorem3.31/proof/not_singular_conjunctive]
  [textbook/theorem3.31/proof/not_cascade]
  DTT strategy (proof comparison §10): `obtain` + `Subsingleton.elim` on `Fin 1`.
-/
theorem pure_feedback_not_other {n : Nat} (SCR : SystemCouplingRecipe n) (h : IsPureFeedback SCR) :
    ¬ IsSingular SCR ∧ ¬ IsConjunctive SCR ∧ ¬ IsCascade SCR := by
  have hn : n = 1 := h.1
  have hne : SCR.CSCR ≠ ∅ := h.2
  constructor
  · intro hs; exact hne hs.2
  · constructor
    · intro hc; exact hne hc
    · intro h_cas
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have : Subsingleton (Fin n) := by rw [hn]; infer_instance
      have heq : p.1.1 = p.2.1 := Subsingleton.elim p.1.1 p.2.1
      have h_feed : IsFeedback p := by unfold IsFeedback; rw [heq]
      exact h_cas p hp h_feed

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
  Parallel (conjunctive) composition of a connectable vector of systems.
-/
noncomputable def csyOut {n : Nat} (VSCR : PortSystemVector n) (hOut : ∀ i, AlwaysOutputs (VSCR.Z i))
    (x : (i : Fin n) → VSCR.SZ i) (op : Σ i, VSCR.OutPort i) : VSCR.OutPortVal op.1 op.2 :=
  Classical.choose (hOut op.1 (x op.1)) op.2

noncomputable def csy {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) :
    DiscreteSystem
      ((i : Fin n) → VSCR.SZ i)
      ((ip : Σ (i : Fin n), VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      ((op : Σ (i : Fin n), VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) where
  sz_nonempty := by
    have h_non : ∀ i, Nonempty (VSCR.SZ i) := fun i => (VSCR.Z i).sz_nonempty
    exact ⟨fun i => Classical.choice (h_non i)⟩
  NZ := fun x po i => (VSCR.Z i).NZ (x i) (po.map (fun full port => full ⟨i, port⟩))
  RZ := fun x => some (fun op => csyOut VSCR hOut x op)

def csy_IP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.Port i) → (Σ (i : Fin n), _VSCR.Port i) := ID _

def csy_INIP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.Port i) → (Σ (i : Fin n), _VSCR.Port i) := ID _

def csy_IS_map {n : Nat} (VSCR : PortSystemVector n) (ip : Σ (i : Fin n), VSCR.Port i) : Type :=
  VSCR.PortVal ip.1 ip.2

def csy_OP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.OutPort i) → (Σ (i : Fin n), _VSCR.OutPort i) := ID _

def csy_INOP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.OutPort i) → (Σ (i : Fin n), _VSCR.OutPort i) := ID _

def csy_OS_map {n : Nat} (VSCR : PortSystemVector n) (op : Σ (i : Fin n), VSCR.OutPort i) : Type :=
  VSCR.OutPortVal op.1 op.2

def product_fun {I : Type} {A B : I → Type} (f : (i : I) → A i → B i) :
    ((i : I) → A i) → ((i : I) → B i) :=
  fun x i => f i (x i)

noncomputable def csy_parameterization (n : Nat) (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) :
    DiscreteSystem
      ((i : Fin n) → VSCR.SZ i)
      ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      ((op : Σ i, VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) :=
  csy VSCR hOut

theorem csy_state_trajectory {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZW ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) :
    (generateStateTrajectory (csy VSCR hOut) x f t i) =
    generateStateTrajectory (VSCR.Z i) (x i) (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t := by
  induction t generalizing i with
  | zero => simp [generateStateTrajectory_zero]
  | succ t ih =>
    rw [generateStateTrajectory_succ]
    simp only [csy]
    exact congr_arg (fun s => (VSCR.Z i).NZ s ((f t).map (fun full port => full ⟨i, port⟩))) (ih i)

theorem csy_output_trajectory {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZW ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n)
    (B' : VSCR.OutPort i) :
    (generateOutputTrajectory (csy VSCR hOut) x f t).map (fun r => r ⟨i, B'⟩) =
    (generateOutputTrajectory (VSCR.Z i) (x i)
      (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t).map (fun r => r B') := by
  have hst := csy_state_trajectory VSCR hOut x f t i
  let s := generateStateTrajectory (VSCR.Z i) (x i)
    (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t
  obtain ⟨o, ho⟩ := hOut i s
  have hchoose : Classical.choose (hOut i s) B' = o B' := by
    have heq : Classical.choose (hOut i s) = o :=
      Option.some_injective _ ((Classical.choose_spec (hOut i s)).symm.trans ho)
    exact congrArg (fun g => g B') heq
  have hmain : Classical.choose (hOut i (generateStateTrajectory (csy VSCR hOut) x f t i)) B' = o B' := by
    rw [hst, hchoose]
  simp only [generateOutputTrajectory, csy, csyOut, Option.map_some]
  rw [ho]
  exact congrArg some hmain

/-! ## Closed, autonomous, and infinite-state examples -/

def closedSystem : DiscreteSystem Unit Empty Empty where
  sz_nonempty := ⟨()⟩
  NZ := fun s _ => s
  RZ := fun _ => none

theorem closedSystem_isClosed : IsClosed closedSystem :=
  ⟨inferInstance, inferInstance⟩

theorem exists_closed_discreteSystem :
    ∃ (Z : DiscreteSystem Unit Empty Empty), IsClosed Z :=
  ⟨closedSystem, closedSystem_isClosed⟩

def toggleSystem : DiscreteSystem Bool Empty Bool where
  sz_nonempty := ⟨true⟩
  NZ := fun s _ => !s
  RZ := fun s => some s

theorem toggle_step (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 1 = !s0 := rfl

theorem toggle_period_two (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 2 = s0 := by
  cases s0 <;> rfl

def counterSystem : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal (fun n (_ : Bool) => n + 1) id ⟨0⟩

theorem counterSystem_not_finite : ¬ IsFinite counterSystem := by
  intro h
  exact Infinite.not_finite (α := Nat) h.1

theorem counterSystem_alwaysOutputs : AlwaysOutputs counterSystem :=
  ofTotal_alwaysOutputs (fun n (_ : Bool) => n + 1) id ⟨0⟩

theorem counterSystem_z2_not_finite :
    ¬ IsFinite (Z2 counterSystem counterSystem_alwaysOutputs) := by
  intro ⟨hSZ, _, _⟩
  have hNat : Finite Nat :=
    (Z2State.equivSZ counterSystem.RZ counterSystem_alwaysOutputs).symm.finite_iff.mpr hSZ
  exact Infinite.not_finite (α := Nat) hNat
