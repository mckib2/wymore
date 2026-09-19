import Mbse.Wymore
import Mbse.Isomorphism

/-!
# Wymore Chapter 5: system modes

This file gives a typed, witness-carrying reconstruction of the system-mode
material in Chapter 5.  Wymore writes inclusions such as `SZ₁ ⊆ SZ₂` even
though the two state sets belong to different systems.  Here those inclusions
are represented by explicit injective maps.  This both records the intended
coercions and prevents accidental identification of unrelated types.

The base `DiscreteSystem` permits autonomous (`none`) inputs.  Chapter 5 mode
transitions are indexed by actual mode inputs, so the equations below concern
`some p`; no claim is made about the mode's autonomous transition.
-/

namespace WymoreSystemModes

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {S₁ I₁ O₁ S₂ I₂ O₂ S₃ I₃ O₃ : Type}
variable {Z₁ : DiscreteSystem S₁ I₁ O₁}
  {Z₂ : DiscreteSystem S₂ I₂ O₂}
  {Z₃ : DiscreteSystem S₃ I₃ O₃}

/--
  [textbook/definition5.6/source/definition]
  [textbook/definition5.6/lean/SystemMode]
`SMBF` from Definition 5.6.  The positive-duration field reflects `TZ₂⁺`.
Total input trajectories are used, exactly as in the chapter; they are lifted
to the repository's optional-input trajectory only when run.
-/
structure BehaviorWitness (S I J : Type) where
  input : S → I → ITZ J
  duration : S → I → Time
  duration_pos : ∀ x p, 0 < duration x p

/--
  [textbook/definition5.6/lean/SystemMode]
Definition 5.6, corrected to typed embeddings.  Besides the SMBF transition
equation, `readout` is the typed version of `RZ₁ ⊆ RZ₂`.  The textbook's
`OZ₁ ⊆ OZ₂` alone does not force readouts to agree; the graph-inclusion clause
does, and is stated explicitly here.
-/
structure SystemMode
    (Z₁ : DiscreteSystem S₁ I₁ O₁) (Z₂ : DiscreteSystem S₂ I₂ O₂) where
  stateMap : S₁ → S₂
  inputMap : I₁ → I₂
  outputMap : O₁ → O₂
  stateMap_injective : Function.Injective stateMap
  inputMap_injective : Function.Injective inputMap
  outputMap_injective : Function.Injective outputMap
  behavior : BehaviorWitness S₁ I₁ I₂
  behavior_initial : ∀ x p, behavior.input x p 0 = inputMap p
  transition : ∀ x p,
    stateMap (Z₁.NZ x (some p)) =
      generateStateTrajectory Z₂ (stateMap x) (liftInput (behavior.input x p))
        (behavior.duration x p)
  readout : ∀ x, (Z₁.RZ x).map outputMap = Z₂.RZ (stateMap x)

/-- Definition 5.6 as an existence relation when the SMBF need not be named. -/
def IsSystemMode (Z₁ : DiscreteSystem S₁ I₁ O₁) (Z₂ : DiscreteSystem S₂ I₂ O₂) : Prop :=
  Nonempty (SystemMode Z₁ Z₂)

/-- [textbook/definition5.6/lean/SystemMode_inputIndex]
The input index `SMB1F`. -/
abbrev SystemMode.inputIndex {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂} (M : SystemMode Z₁ Z₂) :=
  M.behavior.input

/-- [textbook/definition5.6/lean/SystemMode_timeIndex]
The time index `SMB2F`. -/
abbrev SystemMode.timeIndex {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂} (M : SystemMode Z₁ Z₂) :=
  M.behavior.duration

/-- [textbook/definition5.11/source/definition]
[textbook/definition5.11/lean/SystemMode_Manifest]
Definition 5.11: direct manifestation at a time in an experiment. -/
def ManifestAt (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t s : Time) : Prop :=
  s ≤ t ∧ ∃ x₁ : S₁, generateStateTrajectory Z₂ x f s = M.stateMap x₁

/--
  [textbook/definition5.45/source/definition]
  [textbook/definition5.45/lean/SystemMode_InevitableAt]
The inevitable branch of Definition 5.11 needs a precise transition notion;
this is Definition 5.45.  It quantifies over all total exhibitor trajectories
having the required initial input.
-/
def InevitableAt (M : SystemMode Z₁ Z₂) (x : S₁) (p : I₁) : Prop :=
  ∀ g : ITZ I₂, g 0 = M.inputMap p →
    generateStateTrajectory Z₂ (M.stateMap x) (liftInput g) (M.timeIndex x p) =
      M.stateMap (Z₁.NZ x (some p))

/-- [textbook/definition5.45/lean/SystemMode_HasInevitableTransitions]
Definition 5.45: every mode transition is inevitable. -/
def HasInevitableTransitions (M : SystemMode Z₁ Z₂) : Prop :=
  ∀ x p, InevitableAt M x p

/--
  [textbook/definition5.11/lean/SystemMode_InMode]
Definition 5.11, “in a mode”.  The second disjunct records an anchor
manifestation, the mode input at that anchor, and that the current time lies
strictly before the promised next manifestation.  Prefix agreement is stated
pointwise after translating the experiment to the anchor.  The inevitable
alternative is retained verbatim.
-/
def InModeAt (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t s : Time) : Prop :=
  ManifestAt M f x t s ∨
    ∃ (r : Time) (x₁ : S₁) (p₁ : I₁),
      r ≤ s ∧ s ≤ t ∧
      generateStateTrajectory Z₂ x f r = M.stateMap x₁ ∧
      f r = some (M.inputMap p₁) ∧
      s - r < M.timeIndex x₁ p₁ ∧
      ((∀ u, u < s - r → f (r + u) = some (M.inputIndex x₁ p₁ u)) ∨
        InevitableAt M x₁ p₁)

/-- “On its way” means in the mode but not directly manifest. -/
def OnWayAt (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t s : Time) : Prop :=
  InModeAt M f x t s ∧ ¬ ManifestAt M f x t s

/-- [textbook/definition5.11/lean/SystemMode_Enters]
Definition 5.11: entry at a positive discrete time. -/
def EntersAt (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t s : Time) : Prop :=
  0 < s ∧ s ≤ t ∧ ¬ InModeAt M f x t (s - 1) ∧ ManifestAt M f x t s

/-- [textbook/definition5.11/lean/SystemMode_Exits]
Definition 5.11: exit at a positive discrete time. -/
def ExitsAt (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t s : Time) : Prop :=
  0 < s ∧ s ≤ t ∧ InModeAt M f x t (s - 1) ∧ ¬ InModeAt M f x t s

/-- [textbook/definition5.14/source/definition]
[textbook/definition5.14/lean/SystemMode_IsTrivial]
Definition 5.14. -/
def IsTrivialMode (_M : SystemMode Z₁ Z₂) : Prop := IsTrivial Z₁

/--
  [textbook/definition5.16/source/definition]
  [textbook/definition5.16/lean/SystemMode_IsProper]
Definition 5.16.  With heterogeneous state/input/output types, raw equality
`Z₁ ≠ Z₂` is ill-typed.  Properness is therefore the defensible subset reading:
the state embedding is not onto.
-/
def IsProperMode (M : SystemMode Z₁ Z₂) : Prop := ¬ Function.Surjective M.stateMap

/-- [textbook/definition5.40/source/definition]
[textbook/definition5.40/lean/SystemMode_HasConstantTimeIndex]
Definition 5.40: constant time index `d`. -/
def HasConstantTimeIndex (M : SystemMode Z₁ Z₂) (d : Time) : Prop :=
  0 < d ∧ ∀ x p, M.timeIndex x p = d

/-- [textbook/definition5.40/lean/SystemMode_HasVariableTimeIndex]
Definition 5.40: no positive constant time index exists. -/
def HasVariableTimeIndex (M : SystemMode Z₁ Z₂) : Prop :=
  ¬ ∃ d, HasConstantTimeIndex M d

/-- [textbook/definition5.42/source/definition]
[textbook/definition5.42/lean/SystemMode_HasConstantInput]
Definition 5.42: the SMBF trajectory is the constant embedded input. -/
def HasConstantInput (M : SystemMode Z₁ Z₂) : Prop :=
  ∀ x p t, M.inputIndex x p t = M.inputMap p

/-- [textbook/definition5.18/source/definition]
[textbook/definition5.18/lean/SystemMode_IsPrimary]
Definition 5.18: a primary mode has constant time index one. -/
def IsPrimaryMode (M : SystemMode Z₁ Z₂) : Prop :=
  HasConstantTimeIndex M 1

/--
  [textbook/theorem5.20/source/theorem]
  [textbook/theorem5.20/lean/primary_iff_componentwise_subset]
Valid necessary direction of Theorem 5.20.  Its converse for a *fixed*
arbitrary SMBF is false: a stuttering exhibitor has witnesses of duration two
that still preserve one-step transitions.  The corrected existential
converse is supplied by `primaryModeOfMaps`.
-/
theorem primary_preserves_transition (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M) :
    ∀ x p, M.stateMap (Z₁.NZ x (some p)) =
      Z₂.NZ (M.stateMap x) (some (M.inputMap p)) := by
  intro x p
  rw [M.transition x p]
  have hd := h.2 x p
  change M.behavior.duration x p = 1 at hd
  rw [hd]
  simp only [generateStateTrajectory_succ, generateStateTrajectory_zero]
  change Z₂.NZ (M.stateMap x) (some (M.behavior.input x p 0)) =
    Z₂.NZ (M.stateMap x) (some (M.inputMap p))
  rw [M.behavior_initial]

/--
  [textbook/corollary5.136/paragraph/primary_constant_behavior]
Paragraph 5.135.  A primary mode has time index one, so constant output on
`[0, 1)` is only the initial readout.  Replacing the behavior function by the
one-step constant input preserves the mode equations.
-/
def primaryConstantInputMode (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M) :
    SystemMode Z₁ Z₂ where
  stateMap := M.stateMap
  inputMap := M.inputMap
  outputMap := M.outputMap
  stateMap_injective := M.stateMap_injective
  inputMap_injective := M.inputMap_injective
  outputMap_injective := M.outputMap_injective
  behavior :=
    { input := fun _ p _ => M.inputMap p
      duration := fun _ _ => 1
      duration_pos := fun _ _ => Nat.zero_lt_one }
  behavior_initial := fun _ _ => rfl
  transition := by
    intro x p
    rw [primary_preserves_transition M h x p, generateStateTrajectory_succ,
      generateStateTrajectory_zero]
  readout := M.readout

theorem primaryConstantInputMode_constantInput (M : SystemMode Z₁ Z₂)
    (h : IsPrimaryMode M) : HasConstantInput (primaryConstantInputMode M h) :=
  fun _ _ _ => rfl

theorem primaryConstantInputMode_time (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M) :
    HasConstantTimeIndex (primaryConstantInputMode M h) 1 :=
  ⟨Nat.zero_lt_one, fun _ _ => rfl⟩

/-- Primary mode from the shared step/readout core plus injectivity. -/
def primaryModeOfStepReadout {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (M : Homomorphism.StepReadoutMaps Z₁ Z₂)
    (hS : Function.Injective M.HS) (hI : Function.Injective M.HI)
    (hO : Function.Injective M.HO) :
    SystemMode Z₁ Z₂ where
  stateMap := M.HS
  inputMap := M.HI
  outputMap := M.HO
  stateMap_injective := hS
  inputMap_injective := hI
  outputMap_injective := hO
  behavior :=
    { input := fun _ p _ => M.HI p
      duration := fun _ _ => 1
      duration_pos := fun _ _ => Nat.zero_lt_one }
  behavior_initial := fun _ _ => rfl
  transition := by
    intro x p
    simpa [generateStateTrajectory_succ] using M.preserves_step_some x p
  readout := M.preserves_readout

/--
  [textbook/theorem5.20/lean/primary_iff_componentwise_subset]
Corrected converse of 5.20: explicit embeddings preserving transition and
readout generate a primary SMBF (the constant embedded input, duration one).
-/
def primaryModeOfMaps (Z₁ : DiscreteSystem S₁ I₁ O₁) (Z₂ : DiscreteSystem S₂ I₂ O₂)
    (eS : S₁ → S₂) (eI : I₁ → I₂) (eO : O₁ → O₂)
    (hS : Function.Injective eS) (hI : Function.Injective eI)
    (hO : Function.Injective eO)
    (hN : ∀ x p, eS (Z₁.NZ x (some p)) = Z₂.NZ (eS x) (some (eI p)))
    (hR : ∀ x, (Z₁.RZ x).map eO = Z₂.RZ (eS x)) :
    SystemMode Z₁ Z₂ :=
  primaryModeOfStepReadout
    { HS := eS, HI := eI, HO := eO
      preserves_step_some := hN, preserves_readout := hR }
    hS hI hO

theorem primaryModeOfMaps_isPrimary
    (hS : Function.Injective (eS : S₁ → S₂))
    (hI : Function.Injective (eI : I₁ → I₂))
    (hO : Function.Injective (eO : O₁ → O₂))
    (hN : ∀ x p, eS (Z₁.NZ x (some p)) = Z₂.NZ (eS x) (some (eI p)))
    (hR : ∀ x, (Z₁.RZ x).map eO = Z₂.RZ (eS x)) :
    IsPrimaryMode (primaryModeOfMaps Z₁ Z₂ eS eI eO hS hI hO hN hR) :=
  ⟨Nat.zero_lt_one, fun _ _ => rfl⟩

/-! ## Reachable, isolated, transient, and absorbing modes -/

/-- Definition 5.23: states reachable from a nonempty generating set. -/
def ReachableFromSet (Z : DiscreteSystem S₂ I₂ O₂) (A : Set S₂) (y : S₂) : Prop :=
  ∃ x ∈ A, Reachable Z x y

theorem reachableFromSet_step (Z : DiscreteSystem S₂ I₂ O₂) (A : Set S₂)
    {x : S₂} (hx : ReachableFromSet Z A x) (p : I₂) :
    ReachableFromSet Z A (Z.NZ x (some p)) := by
  rcases hx with ⟨a, ha, f, t, hfx⟩
  let g : ITZW I₂ := fun n => if n = t then some p else f n
  refine ⟨a, ha, g, t + 1, ?_⟩
  rw [generateStateTrajectory_succ]
  have hprefix : generateStateTrajectory Z a g t = generateStateTrajectory Z a f t := by
    apply stateTrajectory_nonanticipatory
    rw [rsn_eq_iff]
    intro n hn
    simp only [g]
    simp [Nat.ne_of_lt hn]
  rw [hprefix, hfx]
  simp [g]

/--
  [textbook/definition5.23/source/definition]
  [textbook/definition5.23/lean/reachableSystemMode]
Definition 5.23 construction.  Outputs retain the exhibitor output type; this
avoids the source's untyped `RNG(RSN(...))` codomain restriction while keeping
exactly the restricted readout.
-/
def reachableModeSystem (Z : DiscreteSystem S₂ I₂ O₂) (A : Set S₂)
    (hA : A.Nonempty) :
    DiscreteSystem {x // ReachableFromSet Z A x} I₂ O₂ where
  sz_nonempty := by
    rcases hA with ⟨x, hx⟩
    exact ⟨⟨x, x, hx, reachable_self Z x⟩⟩
  NZ := fun x oi =>
    match oi with
    | none => x
    | some p => ⟨Z.NZ x.val (some p), reachableFromSet_step Z A x.property p⟩
  RZ := fun x => Z.RZ x.val

/-- The reachable construction is a primary system mode (Definition 5.23). -/
def reachableMode (Z : DiscreteSystem S₂ I₂ O₂) (A : Set S₂) (hA : A.Nonempty) :
    SystemMode (reachableModeSystem Z A hA) Z :=
  primaryModeOfMaps _ _ Subtype.val id id Subtype.val_injective
    Function.injective_id Function.injective_id (fun _ _ => rfl)
    (fun _ => by simp [reachableModeSystem])

/-- [textbook/definition5.34/source/definition]
[textbook/definition5.34/lean/SystemMode_IsAbsorbing]
Definition 5.34, corrected semantic core: the embedded state set is closed. -/
def IsAbsorbingMode (M : SystemMode Z₁ Z₂) : Prop :=
  IsPrimaryMode M ∧ IsProperMode M ∧ Function.Surjective M.inputMap

/--
  [textbook/theorem5.37/source/statement]
  [textbook/theorem5.37/lean/reachableSystemMode_isAbsorbing]
Theorem 5.37.  A proper reachable mode is absorbing: its input map is the
identity and its state set is closed under all exhibitor inputs.
-/
theorem proper_reachableMode_absorbing (Z : DiscreteSystem S₂ I₂ O₂)
    (A : Set S₂) (hA : A.Nonempty) (hproper : IsProperMode (reachableMode Z A hA)) :
    IsAbsorbingMode (reachableMode Z A hA) := by
  refine ⟨⟨Nat.zero_lt_one, fun _ _ => rfl⟩, hproper, ?_⟩
  intro p
  exact ⟨p, rfl⟩

/-- Absorbing primary modes are closed under exhibitor inputs. -/
theorem absorbing_closed_under_NZ
    (M : SystemMode Z₁ Z₂) (h : IsAbsorbingMode M)
    (x : S₁) (p : I₂) :
    ∃ x', Z₂.NZ (M.stateMap x) (some p) = M.stateMap x' := by
  obtain ⟨q, hq⟩ := h.2.2 p
  refine ⟨Z₁.NZ x (some q), ?_⟩
  rw [← hq]
  exact (primary_preserves_transition M h.1 x q).symm

/-- [textbook/definition5.26/source/definition]
[textbook/definition5.26/lean/SystemMode_IsIsolated]
Definition 5.26: primary, proper, full-input, and impossible to enter from outside. -/
def IsIsolatedMode (M : SystemMode Z₁ Z₂) : Prop :=
  IsAbsorbingMode M ∧
    ∀ y : S₂, (∀ x, y ≠ M.stateMap x) → ∀ p : I₂,
      ∀ x, Z₂.NZ y (some p) ≠ M.stateMap x

/-- Isolated modes are absorbing (Definition 5.26 projects onto 5.34). -/
theorem isolated_isAbsorbing (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M) :
    IsAbsorbingMode M :=
  h.1

/-! ## Definition 5.23 parameterization `RSYSMO` -/

/-- Parameter bundle for the reachable system-mode construction. -/
structure ReachableModeParam where
  {S I O : Type}
  Z : DiscreteSystem S I O
  A : Set S
  hA : A.Nonempty

/--
  [textbook/definition5.23/lean/RSYSMO]
  `RSYSMO(Z, S)` as a system parameterization over nonempty generating sets.
-/
def rsysmo : DiscreteSystemParameterization ReachableModeParam
    (fun p => {x // ReachableFromSet p.Z p.A x})
    (fun p => p.I) (fun p => p.O) :=
  fun p => reachableModeSystem p.Z p.A p.hA

theorem rsysmo_eq (p : ReachableModeParam) :
    rsysmo p = reachableModeSystem p.Z p.A p.hA :=
  rfl

/-- The reachable construction is always a primary mode. -/
theorem reachableMode_isPrimary (Z : DiscreteSystem S₂ I₂ O₂) (A : Set S₂)
    (hA : A.Nonempty) : IsPrimaryMode (reachableMode Z A hA) :=
  ⟨Nat.zero_lt_one, fun _ _ => rfl⟩

/-! ## Complement of an isolated mode -/

/-- States outside the image of an isolated mode embedding. -/
def OutsideMode (M : SystemMode Z₁ Z₂) : Set S₂ :=
  {y | ∀ x, y ≠ M.stateMap x}

theorem OutsideMode_nonempty_of_proper (M : SystemMode Z₁ Z₂)
    (hproper : IsProperMode M) : (OutsideMode M).Nonempty := by
  unfold IsProperMode Function.Surjective at hproper
  push Not at hproper
  obtain ⟨y, hy⟩ := hproper
  exact ⟨y, fun x => (hy x).symm⟩

theorem outside_closed_of_isolated (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M)
    {y : S₂} (hy : y ∈ OutsideMode M) (p : I₂) :
    Z₂.NZ y (some p) ∈ OutsideMode M := by
  intro x
  exact h.2 y hy p x

/--
Complement system on `SZ₂ \ RNG(stateMap)` for an isolated mode.  Autonomous
steps stutter so the complement stays closed without assuming exhibitor
autonomous behavior.
-/
def complementModeSystem (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M)
    (hproper : IsProperMode M) :
    DiscreteSystem {y // y ∈ OutsideMode M} I₂ O₂ where
  sz_nonempty := by
    obtain ⟨y, hy⟩ := OutsideMode_nonempty_of_proper M hproper
    exact ⟨⟨y, hy⟩⟩
  NZ := fun x oi =>
    match oi with
    | none => x
    | some p => ⟨Z₂.NZ x.val (some p), outside_closed_of_isolated M h x.property p⟩
  RZ := fun x => Z₂.RZ x.val

def complementMode (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M)
    (hproper : IsProperMode M) :
    SystemMode (complementModeSystem M h hproper) Z₂ :=
  primaryModeOfMaps _ _ Subtype.val id id Subtype.val_injective
    Function.injective_id Function.injective_id (fun _ _ => rfl)
    (fun _ => by simp [complementModeSystem])

theorem complementMode_isIsolated (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M)
    (hproper : IsProperMode M) :
    IsIsolatedMode (complementMode M h hproper) := by
  refine ⟨⟨⟨Nat.zero_lt_one, fun _ _ => rfl⟩, ?_, fun p => ⟨p, rfl⟩⟩, ?_⟩
  · intro hsurj
    obtain ⟨x₁⟩ := Z₁.sz_nonempty
    obtain ⟨y, hy⟩ := hsurj (M.stateMap x₁)
    exact y.property x₁ hy
  · intro y hyOut p z
    have hyIn : ∃ x₁, y = M.stateMap x₁ := by
      by_contra hnone
      push Not at hnone
      exact hyOut ⟨y, hnone⟩ rfl
    obtain ⟨x₁, rfl⟩ := hyIn
    obtain ⟨x', hx'⟩ := absorbing_closed_under_NZ M h.1 x₁ p
    rw [hx']
    exact (z.property x').symm

/-- [textbook/definition5.30/source/definition]
[textbook/definition5.30/lean/SystemMode_IsTransient]
Definition 5.30: transient mode, using proper input embedding for `IZ₁ ≠ IZ₂`. -/
def IsTransientMode (M : SystemMode Z₁ Z₂) : Prop :=
  IsPrimaryMode M ∧ IsProperMode M ∧
    ¬ Function.Surjective M.inputMap ∧
    (∀ y : S₂, (∀ x, y ≠ M.stateMap x) → ∀ p : I₂,
      ∀ x, Z₂.NZ y (some p) ≠ M.stateMap x) ∧
    ∀ x : S₁, ∃ f : ITZW I₂, ∃ t,
      ∀ y : S₁, generateStateTrajectory Z₂ (M.stateMap x) f t ≠ M.stateMap y

/-- [textbook/definition5.30/lean/System_IsTransientState]
Definition 5.30: a transient state. -/
def IsTransientState (Z : DiscreteSystem S₂ I₂ O₂) (x : S₂) : Prop :=
  (∃ p, Z.NZ x (some p) ≠ x) ∧
  ∀ y, y ≠ x → ∀ p, Z.NZ y (some p) ≠ x

/-- [textbook/definition5.34/lean/System_IsAbsorbingState]
Definition 5.34: an absorbing state. -/
def IsAbsorbingState (Z : DiscreteSystem S₂ I₂ O₂) (x : S₂) : Prop :=
  ∀ p, Z.NZ x (some p) = x

/-- Inputs that leave a state fixed for one step. -/
def StayInput (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂) : Type :=
  {p : I₂ // Z.NZ x' (some p) = x'}

/-- Singleton mode system generated by a transient state (Exercise 5.165). -/
def transientStateSystem (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (_hne : Nonempty (StayInput Z x')) :
    DiscreteSystem Unit (StayInput Z x') O₂ where
  sz_nonempty := ⟨()⟩
  NZ := fun _ oi =>
    match oi with
    | none => ()
    | some _ => ()
  RZ := fun _ => Z.RZ x'

/-- Primary mode embedding of a transient-state singleton. -/
def transientStateMode (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (hne : Nonempty (StayInput Z x')) :
    SystemMode (transientStateSystem Z x' hne) Z :=
  primaryModeOfMaps _ _ (fun _ => x') Subtype.val id
    (fun _ _ _ => rfl) Subtype.val_injective Function.injective_id
    (fun _ p => by
      change x' = Z.NZ x' (some p.val)
      exact p.property.symm)
    (fun _ => by simp [transientStateSystem])

theorem transientState_generates_transientMode
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (htrans : IsTransientState Z x')
    (hne : Nonempty (StayInput Z x'))
    (hproper : ∃ y : S₂, y ≠ x') :
    IsTransientMode (transientStateMode Z x' hne) := by
  refine ⟨⟨Nat.zero_lt_one, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro hsurj
    obtain ⟨y, hy⟩ := hproper
    obtain ⟨u, hEq⟩ := hsurj y
    cases u
    exact hy hEq.symm
  · intro hsurj
    obtain ⟨p, hp⟩ := htrans.1
    obtain ⟨q, hq⟩ := hsurj p
    have : Z.NZ x' (some p) = x' := by
      rw [← hq]; exact q.property
    exact hp this
  · intro y hyOut p u
    cases u
    exact htrans.2 y (hyOut ()) p
  · intro u
    cases u
    obtain ⟨p, hp⟩ := htrans.1
    refine ⟨fun _ => some p, 1, ?_⟩
    intro v
    cases v
    change Z.NZ x' (some p) ≠ x'
    exact hp

/-- Singleton system generated by an absorbing state (Exercise 5.166). -/
def absorbingStateSystem (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (_habs : IsAbsorbingState Z x') :
    DiscreteSystem Unit I₂ O₂ where
  sz_nonempty := ⟨()⟩
  NZ := fun _ _ => ()
  RZ := fun _ => Z.RZ x'

def absorbingStateMode (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') :
    SystemMode (absorbingStateSystem Z x' habs) Z :=
  primaryModeOfMaps _ _ (fun _ => x') id id
    (fun _ _ _ => rfl) Function.injective_id Function.injective_id
    (fun _ p => (habs p).symm) (fun _ => by simp [absorbingStateSystem])

/-- Under absorbing + autonomous stutter, trajectories from `x'` stay at `x'`. -/
theorem trajectory_stays_at_absorbing (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') (haut : Z.NZ x' none = x')
    (f : ITZW I₂) (t : Time) :
    generateStateTrajectory Z x' f t = x' := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [generateStateTrajectory_succ, ih]
    cases hf : f t with
    | none => simpa [hf] using haut
    | some p => simpa [hf] using habs p

theorem reachableFromSet_of_absorbing (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') (haut : Z.NZ x' none = x') (y : S₂) :
    ReachableFromSet Z {x'} y ↔ y = x' := by
  constructor
  · rintro ⟨a, ha, f, t, htraj⟩
    have ha' : a = x' := Set.mem_singleton_iff.mp ha
    rw [ha'] at htraj
    have hstay := trajectory_stays_at_absorbing Z x' habs haut f t
    exact (hstay.symm.trans htraj).symm
  · intro hy
    rw [hy]
    exact ⟨x', Set.mem_singleton x', fun _ => none, 0, rfl⟩

theorem absorbingStateMode_isAbsorbing
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') (hproper : ∃ y : S₂, y ≠ x') :
    IsAbsorbingMode (absorbingStateMode Z x' habs) := by
  refine ⟨⟨Nat.zero_lt_one, fun _ _ => rfl⟩, ?_, fun p => ⟨p, rfl⟩⟩
  · intro hsurj
    obtain ⟨y, hy⟩ := hproper
    obtain ⟨u, hEq⟩ := hsurj y
    cases u
    exact hy hEq.symm

theorem absorbingStateMode_isTrivial
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') :
    IsTrivialMode (absorbingStateMode Z x' habs) := by
  intro hnt
  rcases hnt with ⟨hNZ, _, _⟩
  rcases hNZ with ⟨u₁, u₂, p, hp⟩
  cases u₁; cases u₂
  exact hp rfl

theorem absorbing_reachableMode_properties
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') (haut : Z.NZ x' none = x')
    (hproper : ∃ y : S₂, y ≠ x') :
    IsAbsorbingMode (reachableMode Z ({x'} : Set S₂) ⟨x', rfl⟩) ∧
      IsTrivialMode (reachableMode Z ({x'} : Set S₂) ⟨x', rfl⟩) := by
  have hProperMode : IsProperMode (reachableMode Z ({x'} : Set S₂) ⟨x', rfl⟩) := by
    intro hsurj
    obtain ⟨y, hy⟩ := hproper
    obtain ⟨⟨z, hz⟩, hEq⟩ := hsurj y
    have hz' : ReachableFromSet Z {x'} y := hEq ▸ hz
    have : y = x' := (reachableFromSet_of_absorbing Z x' habs haut y).mp hz'
    exact hy this
  refine ⟨proper_reachableMode_absorbing Z {x'} ⟨x', rfl⟩ hProperMode, ?_⟩
  intro hnt
  rcases hnt with ⟨hNZ, _, _⟩
  rcases hNZ with ⟨⟨a, ha⟩, ⟨b, hb⟩, p, hp⟩
  have ha' : a = x' := (reachableFromSet_of_absorbing Z x' habs haut a).mp ha
  have hb' : b = x' := (reachableFromSet_of_absorbing Z x' habs haut b).mp hb
  have hab : (⟨a, ha⟩ : {x // ReachableFromSet Z {x'} x}) = ⟨b, hb⟩ := by
    apply Subtype.ext
    exact ha'.trans hb'.symm
  exact hp (by rw [hab])

/-- Trajectory starting in an absorbing mode remains in the mode image. -/
theorem trajectory_stays_in_absorbing_mode
    (M : SystemMode Z₁ Z₂) (h : IsAbsorbingMode M)
    (f : ITZ I₂) (x₁ : S₁) (s : Time) :
    ∃ x', generateStateTrajectory Z₂ (M.stateMap x₁) (liftInput f) s = M.stateMap x' := by
  induction s with
  | zero => exact ⟨x₁, rfl⟩
  | succ s ih =>
    obtain ⟨x', hx'⟩ := ih
    rw [generateStateTrajectory_succ, hx']
    simpa [liftInput] using absorbing_closed_under_NZ M h x' (f s)

/-- Isolated mode: throughout a total experiment iff the start state is in the mode. -/
theorem isolated_throughout_iff
    (M : SystemMode Z₁ Z₂) (h : IsIsolatedMode M)
    (f : ITZ I₂) (x : S₂) (t : Time) :
    (∀ s ≤ t, InModeAt M (liftInput f) x t s) ↔ ∃ x₁, x = M.stateMap x₁ := by
  constructor
  · intro hthr
    have h0 := hthr 0 (Nat.zero_le t)
    have hM : ManifestAt M (liftInput f) x t 0 := by
      cases h0 with
      | inl hM => exact hM
      | inr hway =>
        rcases hway with ⟨r, x₁, p₁, hr0, _, hx₁, _, _, _⟩
        have hr : r = 0 := Nat.eq_zero_of_le_zero hr0
        subst hr
        exact ⟨Nat.zero_le t, x₁, hx₁⟩
    rcases hM with ⟨_, x₁, hx₁⟩
    exact ⟨x₁, by simpa [generateStateTrajectory] using hx₁⟩
  · intro ⟨x₁, hx⟩ s hs
    subst hx
    left
    refine ⟨hs, ?_⟩
    simpa using trajectory_stays_in_absorbing_mode M h.1 f x₁ s

/--
One-step exit witness for a transient mode under exhibitor autonomous stutter
(typed reading of the exit clause in Ex. 5.164).
-/
theorem transient_exists_exit_step (M : SystemMode Z₁ Z₂) (h : IsTransientMode M)
    (haut : ∀ y : S₂, Z₂.NZ y none = y) :
    ∃ (x : S₁) (p : I₂), ∀ x' : S₁, Z₂.NZ (M.stateMap x) (some p) ≠ M.stateMap x' := by
  obtain ⟨x₀⟩ := Z₁.sz_nonempty
  obtain ⟨f, t, htLeave⟩ := h.2.2.2.2 x₀
  have htpos : 0 < t := by
    by_contra ht0
    have : t = 0 := Nat.eq_zero_of_not_pos ht0
    subst this
    exact htLeave x₀ (by simp [generateStateTrajectory])
  classical
  let inMode : Time → Prop := fun u =>
    ∃ x' : S₁, generateStateTrajectory Z₂ (M.stateMap x₀) f u = M.stateMap x'
  have hin0 : inMode 0 := ⟨x₀, rfl⟩
  have hnott : ¬ inMode t := fun ⟨x', hx'⟩ => htLeave x' hx'
  have hex : ∃ n, ¬ inMode n := ⟨t, hnott⟩
  let s := Nat.find hex
  have hs_out : ¬ inMode s := Nat.find_spec hex
  have hs_min : ∀ m < s, inMode m := fun m hm => by
    by_contra hm'
    exact Nat.find_min hex hm hm'
  have hs_pos : 0 < s := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hs_out
    exact hs_out hin0
  have hs_in : inMode (s - 1) := hs_min (s - 1) (Nat.pred_lt (ne_of_gt hs_pos))
  obtain ⟨x, hx⟩ := hs_in
  have hs' : (s - 1) + 1 = s := Nat.sub_add_cancel hs_pos
  have hstep : generateStateTrajectory Z₂ (M.stateMap x₀) f ((s - 1) + 1) =
      Z₂.NZ (M.stateMap x) (f (s - 1)) := by
    rw [generateStateTrajectory_succ, hx]
  rw [hs'] at hstep
  match hf : f (s - 1) with
  | none =>
    have : generateStateTrajectory Z₂ (M.stateMap x₀) f s = M.stateMap x := by
      rw [hstep, hf, haut]
    exact absurd ⟨x, this⟩ hs_out
  | some p =>
    refine ⟨x, p, ?_⟩
    intro x' hEq
    have : inMode s := ⟨x', by rw [hstep, hf, hEq]⟩
    exact hs_out this

/-- Textbook differences between transient and isolated modes (Exercise 5.164). -/
theorem transient_vs_isolated_differences (M : SystemMode Z₁ Z₂)
    (haut : ∀ y : S₂, Z₂.NZ y none = y) :
    (IsTransientMode M →
      ¬ Function.Surjective M.inputMap ∧
        ∃ (x : S₁) (p : I₂), ∀ x' : S₁, Z₂.NZ (M.stateMap x) (some p) ≠ M.stateMap x') ∧
    (IsIsolatedMode M →
      Function.Surjective M.inputMap ∧
        ∀ (x : S₁) (p : I₂), ∃ x' : S₁, Z₂.NZ (M.stateMap x) (some p) = M.stateMap x') := by
  refine ⟨fun ht => ⟨ht.2.2.1, transient_exists_exit_step M ht haut⟩, ?_⟩
  · intro hi
    exact ⟨hi.1.2.2, fun x p => absorbing_closed_under_NZ M hi.1 x p⟩

theorem transient_not_absorbing (M : SystemMode Z₁ Z₂) :
    IsTransientMode M → ¬ IsAbsorbingMode M := by
  intro ht ha
  exact ht.2.2.1 ha.2.2

theorem no_proper_subset_of_unit (e : Unit → Unit) (_hinj : Function.Injective e) :
    Function.Surjective e := by
  intro y
  exact ⟨(), Subsingleton.elim _ _⟩

/-! ## Constant indices, manifestation, and inevitable transitions -/

/--
  [textbook/theorem5.44/source/theorem]
  [textbook/theorem5.44/lean/manifest_next_of_constant_input_time]
Theorem 5.44 in its corrected time-origin-independent form.  The source mixes
`k + d` and `k*d`; the actual induction step is from manifestation at `s` to
manifestation at `s+d`.  Prefix agreement is the exact nonanticipation
hypothesis needed by the trajectory recurrence.
-/
theorem manifestation_next_of_constant
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (f : ITZW I₂) (x : S₂) (t s : Time)
    (hmanifest : ManifestAt M f x t s) (p : I₁)
    (hbound : s + d ≤ t)
    (hsegment : ∀ u, u < d → f (s + u) = some (M.inputMap p)) :
    ManifestAt M f x t (s + d) := by
  rcases hmanifest with ⟨_, x₁, hx₁⟩
  refine ⟨hbound, Z₁.NZ x₁ (some p), ?_⟩
  rw [← Trajectory.stateTrajectory_time_invariance Z₂ x f s d, hx₁]
  have hagree :
      generateStateTrajectory Z₂ (M.stateMap x₁) (translate f s) d =
        generateStateTrajectory Z₂ (M.stateMap x₁)
          (liftInput (M.inputIndex x₁ p)) d := by
    apply stateTrajectory_nonanticipatory
    rw [rsn_eq_iff]
    intro u hu
    change f (u + s) = some (M.inputIndex x₁ p u)
    rw [Nat.add_comm, hsegment u hu, hinput]
  rw [hagree]
  have hd := htime.2 x₁ p
  change M.behavior.duration x₁ p = d at hd
  rw [← hd]
  exact (M.transition x₁ p).symm

/--
  [textbook/theorem5.47/source/theorem]
  [textbook/theorem5.47/lean/manifest_at_behavior_deadline]
Theorem 5.47 under the charitable total-input hypothesis: the experiment is a
total trajectory `ITZ`, so every time on the interval carries an input.
-/
theorem inevitable_next_manifestation_total
    (M : SystemMode Z₁ Z₂) (hInev : HasInevitableTransitions M)
    (f : ITZ I₂) (x : S₂) (t s : Time) (x₁ : S₁) (p : I₁)
    (hx₁ : generateStateTrajectory Z₂ x (liftInput f) s = M.stateMap x₁)
    (hat : f s = M.inputMap p)
    (hbound : s + M.timeIndex x₁ p ≤ t) :
    ManifestAt M (liftInput f) x t (s + M.timeIndex x₁ p) := by
  refine ⟨hbound, Z₁.NZ x₁ (some p), ?_⟩
  rw [← Trajectory.stateTrajectory_time_invariance Z₂ x (liftInput f) s
    (M.timeIndex x₁ p), hx₁]
  exact hInev x₁ p (fun u => f (u + s)) (by simp [hat])

/--
  [textbook/theorem5.47/lean/inMode_until_behavior_deadline]
The “in the mode while on the way” part of 5.47, under total inputs.
-/
theorem inevitable_inMode_interval
    (M : SystemMode Z₁ Z₂) (hInev : HasInevitableTransitions M)
    (f : ITZ I₂) (x : S₂) (t s : Time) (x₁ : S₁) (p : I₁)
    (_hs : s ≤ t) (hx₁ : generateStateTrajectory Z₂ x (liftInput f) s = M.stateMap x₁)
    (hat : f s = M.inputMap p)
    (hbound : s + M.timeIndex x₁ p ≤ t) :
    ∀ r, s ≤ r → r ≤ s + M.timeIndex x₁ p →
      InModeAt M (liftInput f) x t r := by
  intro r hsr hr
  by_cases heq : r = s + M.timeIndex x₁ p
  · left
    rw [heq]
    exact inevitable_next_manifestation_total M hInev f x t s x₁ p hx₁ hat hbound
  · right
    refine ⟨s, x₁, p, hsr, Nat.le_trans hr hbound, hx₁, by simp [hat], ?_, Or.inr (hInev x₁ p)⟩
    apply (Nat.sub_lt_iff_lt_add hsr).2
    rw [Nat.add_comm]
    exact Nat.lt_of_le_of_ne hr heq

/-! ## Non-uniqueness, output constancy, and ports -/

/-- A stuttering one-state system used for Statements 5.48 and 5.54. -/
def unitStutter (I : Type) : DiscreteSystem Unit I Unit :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ => ()) ⟨()⟩

/-- [textbook/theorem5.48/source/statement]
[textbook/theorem5.48/lean/behaviorFunction_not_unique_example]
Definition 5.48 witness family: every positive duration is a valid SMBF. -/
def stutterModeAt (I : Type) (n : Nat) :
    SystemMode (unitStutter I) (unitStutter I) where
  stateMap := id
  inputMap := id
  outputMap := id
  stateMap_injective := Function.injective_id
  inputMap_injective := Function.injective_id
  outputMap_injective := Function.injective_id
  behavior :=
    { input := fun _ p _ => p
      duration := fun _ _ => n + 1
      duration_pos := fun _ _ => Nat.zero_lt_succ n }
  behavior_initial := fun _ _ => rfl
  transition := by intro _ _; rfl
  readout := by intro _; rfl

/-- [textbook/theorem5.48/lean/behaviorFunction_infinite_family_example]
Statement 5.48: the witness family is injective in its time index. -/
theorem stutterModeAt_injective (I : Type) [Nonempty I] :
    Function.Injective (stutterModeAt I) := by
  intro m n h
  obtain ⟨p⟩ := ‹Nonempty I›
  have hd := congrArg (fun M => M.timeIndex () p) h
  change m + 1 = n + 1 at hd
  omega

/--
  [textbook/definition5.49/source/definition]
  [textbook/definition5.49/lean/SystemMode_HasConstantOutputOn]
Definition 5.49.  `project` represents projection to a selected set `B` of
output ports.  Since readout is partial in `DiscreteSystem`, equality is stated
in `Option B`; this is exactly output constancy along the SMBF interval.
-/
def HasConstantOutputOn (M : SystemMode Z₁ Z₂) (project : O₂ → B) : Prop :=
  ∀ x p s, s < M.timeIndex x p →
    (generateOutputTrajectory Z₂ (M.stateMap x) (liftInput (M.inputIndex x p)) s).map project =
      (Z₂.RZ (M.stateMap x)).map project

/-- [textbook/definition5.49/lean/SystemMode_HasConstantOutput]
Full-output version of Definition 5.49. -/
def HasConstantOutput (M : SystemMode Z₁ Z₂) : Prop :=
  HasConstantOutputOn M id

/-- Time index one makes constant output automatic: the only time in `[0, 1)` is 0. -/
theorem hasConstantOutput_of_timeIndex_one (M : SystemMode Z₁ Z₂)
    (h : HasConstantTimeIndex M 1) : HasConstantOutput M := by
  intro _ _ s hs
  have hs0 : s = 0 := Nat.lt_one_iff.mp (h.2 _ _ ▸ hs)
  subst hs0
  simp [generateOutputTrajectory, generateStateTrajectory_zero]

theorem primaryConstantInputMode_constantOutput (M : SystemMode Z₁ Z₂)
    (h : IsPrimaryMode M) : HasConstantOutput (primaryConstantInputMode M h) :=
  hasConstantOutput_of_timeIndex_one _ (primaryConstantInputMode_time M h)

/--
  [textbook/definition5.57/source/definition]
  [textbook/definition5.57/lean/SystemMode_ConstrictsInputs]
Definition 5.57 / paragraph 5.59: input constriction means the mode has a
single port index while the exhibitor has more than one, so there is no
port-index equivalence and hence no `PreservesPorts` witness along an
equivalence of port indices.
-/
def HasInputPortConstriction (modePorts exhibitorPorts : Nat) : Prop :=
  modePorts = 1 ∧ 1 < exhibitorPorts

/--
  [textbook/definition5.57/lean/SystemMode_ConstrictsOutputs]
Definition 5.57, output-port counterpart.
-/
def HasOutputPortConstriction (modePorts exhibitorPorts : Nat) : Prop :=
  modePorts = 1 ∧ 1 < exhibitorPorts

theorem equal_port_counts_not_input_constriction (n : Nat) :
    ¬ HasInputPortConstriction n n := by
  intro ⟨h1, h2⟩
  omega

theorem equal_port_counts_not_output_constriction (n : Nat) :
    ¬ HasOutputPortConstriction n n := by
  intro ⟨h1, h2⟩
  omega

/-- Constriction blocks a port-index equivalence (paragraph 5.59). -/
theorem input_constriction_blocks_equiv {m e : Nat}
    (h : HasInputPortConstriction m e) : IsEmpty (Fin m ≃ Fin e) :=
  ⟨fun equiv => by
    obtain ⟨hm, he⟩ := h
    have hcard := Fintype.card_congr equiv
    simp [Fintype.card_fin, hm] at hcard
    exact Nat.ne_of_gt he hcard.symm⟩

/-- A shared port indexing with `PreservesPorts` is not an input constriction. -/
theorem preservesPorts_not_input_constriction
    {Port : Type} [Fintype Port] {V₁ V₂ : Port → Type}
    {H : ((p : Port) → V₂ p) → ((p : Port) → V₁ p)}
    (_hp : Homomorphism.PreservesPorts (Equiv.refl Port) H) :
    ¬ HasInputPortConstriction (Fintype.card Port) (Fintype.card Port) :=
  equal_port_counts_not_input_constriction _

/--
  [textbook/theorem5.54/source/theorem]
  [textbook/theorem5.54/lean/systemMode_inputPort_card]
  [textbook/theorem5.54/lean/systemMode_outputPort_card]
Theorem 5.54 and paragraph 5.55, in the port-index representation.  A
product-structured inclusion is an equivalence of port indices, so a two-port
index set is not a subset of a three-port index set: `Fin 2 ≃ Fin 3` is
impossible.
-/
theorem theorem5_54_fin2_not_equiv_fin3 : IsEmpty (Fin 2 ≃ Fin 3) :=
  ⟨fun e => by
    have hcard := Fintype.card_congr e
    simp [Fintype.card_fin] at hcard⟩

/--
  [textbook/theorem5.54/lean/systemMode_port_subset]
Paragraph 5.59.  When the port counts agree, the inclusion is the portwise
family of `PreservesPorts` along the identity equivalence of port indices.
-/
theorem paragraph5_59_portwise
    {Port : Type} {V₁ V₂ : Port → Type}
    {H : ((p : Port) → V₂ p) → ((p : Port) → V₁ p)}
    (hp : Homomorphism.PreservesPorts (Equiv.refl Port) H) (f : (p : Port) → V₂ p)
    (p : Port) : H f p = hp.port p (f p) :=
  hp.proj f p

/-! ## Compiling mode experiments (Theorems 5.61 and 5.62) -/

/-- Elapsed exhibitor time after `n` mode transitions. -/
def compiledElapsed (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁) : Time → Time
  | 0 => 0
  | n + 1 =>
      compiledElapsed M x f n +
        M.timeIndex (generateStateTrajectory Z₁ x (liftInput f) n) (f n)

/--
  [textbook/theorem5.62/source/theorem]
  [textbook/theorem5.62/lean/liftExperiment_systemMode]
Piecewise concatenation of the successive SMBF trajectories.  Values after the
compiled prefix are intentionally inherited from the final SMBF trajectory;
only the prefix affects the endpoint theorem.
-/
def compiledInput (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁) : Time → ITZ I₂
  | 0 => M.inputIndex x (f 0)
  | n + 1 =>
      concatenate (compiledInput M x f n)
        (M.inputIndex (generateStateTrajectory Z₁ x (liftInput f) n) (f n))
        (compiledElapsed M x f n)

/-- Every nonempty compiled experiment starts with the embedded first input. -/
theorem compiledInput_zero (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁) :
    ∀ n, compiledInput M x f n 0 = M.inputMap (f 0) := by
  intro n
  induction n with
  | zero => exact M.behavior_initial x (f 0)
  | succ n ih =>
    cases n with
    | zero =>
      simp [compiledInput, compiledElapsed, concatenate, M.behavior_initial]
    | succ n =>
      have hpos : 0 < compiledElapsed M x f (n + 1) := by
        simp only [compiledElapsed]
        exact Nat.add_pos_right _ (M.behavior.duration_pos _ _)
      rw [compiledInput]
      simp [concatenate, hpos, ih]

/--
  [textbook/theorem5.62/lean/liftExperiment_systemMode_state]
Theorem 5.62, state part: a general mode experiment expands to an exhibitor
experiment assembled from the SMBF witness pieces.
-/
theorem compiled_state (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁) :
    ∀ n,
      generateStateTrajectory Z₂ (M.stateMap x)
          (liftInput (compiledInput M x f n)) (compiledElapsed M x f n) =
        M.stateMap (generateStateTrajectory Z₁ x (liftInput f) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [compiledElapsed, compiledInput]
    rw [← Trajectory.stateTrajectory_time_invariance_concatenation]
    rw [ih, ← M.transition]
    rfl

/-- [textbook/theorem5.62/lean/liftExperiment_systemMode_output]
Theorem 5.62, output part, with the explicit output embedding. -/
theorem compiled_output (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁) (n : Time) :
    (generateOutputTrajectory Z₁ x (liftInput f) n).map M.outputMap =
      generateOutputTrajectory Z₂ (M.stateMap x)
        (liftInput (compiledInput M x f n)) (compiledElapsed M x f n) := by
  unfold generateOutputTrajectory
  rw [M.readout, compiled_state]

/--
  [textbook/theorem5.61/source/theorem]
  [textbook/theorem5.61/lean/liftExperiment_constantInputTime]
Definition used by Theorem 5.61: hold each mode input for a block of `d`
exhibitor ticks.
-/
def expandConstantInput (M : SystemMode Z₁ Z₂) (f : ITZ I₁) (d : Time) : ITZ I₂ :=
  fun t => M.inputMap (f (t / d))

/--
  [textbook/theorem5.61/lean/liftExperiment_constantInputTime_state]
Theorem 5.61, state part.  The source's interval formula has capitalization
and endpoint slips; this block-expansion statement is its standard corrected
reading.  Positivity of `d` comes from the constant-time-index property.
-/
theorem constant_compiled_state
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (x : S₁) (f : ITZ I₁) :
    ∀ n,
      generateStateTrajectory Z₂ (M.stateMap x)
          (liftInput (expandConstantInput M f d)) (d * n) =
        M.stateMap (generateStateTrajectory Z₁ x (liftInput f) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ]
    rw [← Trajectory.stateTrajectory_time_invariance Z₂ (M.stateMap x)
      (liftInput (expandConstantInput M f d)) (d * n) d, ih]
    let xn := generateStateTrajectory Z₁ x (liftInput f) n
    have hagree :
        generateStateTrajectory Z₂ (M.stateMap xn)
            (translate (liftInput (expandConstantInput M f d)) (d * n)) d =
          generateStateTrajectory Z₂ (M.stateMap xn)
            (liftInput (M.inputIndex xn (f n))) d := by
      apply stateTrajectory_nonanticipatory
      rw [rsn_eq_iff]
      intro u hu
      simp only [translate, liftInput]
      congr 1
      rw [hinput]
      dsimp [expandConstantInput]
      have hd : 0 < d := htime.1
      rw [Nat.add_mul_div_left u n hd]
      simp [Nat.div_eq_of_lt hu]
    change generateStateTrajectory Z₂ (M.stateMap xn)
        (translate (liftInput (expandConstantInput M f d)) (d * n)) d =
      M.stateMap (Z₁.NZ xn (some (f n)))
    rw [hagree]
    have hd := htime.2 xn (f n)
    change M.behavior.duration xn (f n) = d at hd
    rw [← hd]
    exact (M.transition xn (f n)).symm

/-- [textbook/theorem5.61/lean/liftExperiment_constantInputTime_output]
Theorem 5.61, output part. -/
theorem constant_compiled_output
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (x : S₁) (f : ITZ I₁) (n : Time) :
    (generateOutputTrajectory Z₁ x (liftInput f) n).map M.outputMap =
      generateOutputTrajectory Z₂ (M.stateMap x)
        (liftInput (expandConstantInput M f d)) (d * n) := by
  unfold generateOutputTrajectory
  rw [M.readout, constant_compiled_state M hinput d htime]

/-! ## Definition 5.64: `SYSMO` as a typed parameterization -/

/--
  [textbook/definition5.64/source/definition]
  [textbook/definition5.64/lean/systemModeOfBehavior]
Data accepted by the `SYSMO` constructor.  `S` and `P` are represented by
their types and explicit embeddings; closure is carried by `next_mem` through
the subtype state.  `Q` is represented by `O` plus an output embedding and an
explicit restricted readout, avoiding the source's ambiguous range codomain.
-/
structure SysmoData (Z : DiscreteSystem S₂ I₂ O₂) where
  S : Type
  P : Type
  Q : Type
  sMap : S → S₂
  pMap : P → I₂
  qMap : Q → O₂
  sMap_injective : Function.Injective sMap
  pMap_injective : Function.Injective pMap
  qMap_injective : Function.Injective qMap
  state_nonempty : Nonempty S
  behavior : BehaviorWitness S P I₂
  behavior_initial : ∀ x p, behavior.input x p 0 = pMap p
  next : S → P → S
  transition : ∀ x p,
    sMap (next x p) =
      generateStateTrajectory Z (sMap x) (liftInput (behavior.input x p))
        (behavior.duration x p)
  readout : S → Option Q
  readout_compat : ∀ x, (readout x).map qMap = Z.RZ (sMap x)

/-- [textbook/definition5.64/lean/sysmo]
Definition 5.64: system produced by valid `SYSMO` data. -/
def sysmoSystem (D : SysmoData Z₂) : DiscreteSystem D.S D.P D.Q where
  sz_nonempty := D.state_nonempty
  NZ := fun x op => match op with | none => x | some p => D.next x p
  RZ := D.readout

/-- Definition 5.64: the constructor also returns the required mode witness. -/
def sysmoMode (D : SysmoData Z₂) : SystemMode (sysmoSystem D) Z₂ where
  stateMap := D.sMap
  inputMap := D.pMap
  outputMap := D.qMap
  stateMap_injective := D.sMap_injective
  inputMap_injective := D.pMap_injective
  outputMap_injective := D.qMap_injective
  behavior := D.behavior
  behavior_initial := D.behavior_initial
  transition := D.transition
  readout := D.readout_compat

theorem sysmo_isSystemMode (D : SysmoData Z₂) :
    IsSystemMode (sysmoSystem D) Z₂ :=
  ⟨sysmoMode D⟩

/-! ## Theorem 5.67: transitivity -/

/-- The elapsed compiled time is positive after a positive number of steps. -/
theorem compiledElapsed_pos (M : SystemMode Z₁ Z₂) (x : S₁) (f : ITZ I₁)
    {n : Time} (hn : 0 < n) : 0 < compiledElapsed M x f n := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n =>
    simp only [compiledElapsed]
    exact Nat.add_pos_right _ (M.behavior.duration_pos _ _)

/--
  [textbook/theorem5.67/source/theorem]
  [textbook/theorem5.67/lean/SystemMode_trans]
Theorem 5.67.  The composite SMBF expands the first mode's SMBF trajectory
through the second mode using the general experiment compiler.  This witness
data is essential: merely composing subset inclusions would not prove the
composite transition equation.
-/
def SystemMode.trans (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃) :
    SystemMode Z₁ Z₃ where
  stateMap := M₂₃.stateMap ∘ M₁₂.stateMap
  inputMap := M₂₃.inputMap ∘ M₁₂.inputMap
  outputMap := M₂₃.outputMap ∘ M₁₂.outputMap
  stateMap_injective := M₂₃.stateMap_injective.comp M₁₂.stateMap_injective
  inputMap_injective := M₂₃.inputMap_injective.comp M₁₂.inputMap_injective
  outputMap_injective := M₂₃.outputMap_injective.comp M₁₂.outputMap_injective
  behavior :=
    { input := fun x p =>
        compiledInput M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
          (M₁₂.timeIndex x p)
      duration := fun x p =>
        compiledElapsed M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
          (M₁₂.timeIndex x p)
      duration_pos := fun x p =>
        compiledElapsed_pos M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
          (M₁₂.behavior.duration_pos x p) }
  behavior_initial := by
    intro x p
    dsimp only
    rw [compiledInput_zero]
    simp [M₁₂.behavior_initial, Function.comp_apply]
  transition := by
    intro x p
    change M₂₃.stateMap (M₁₂.stateMap (Z₁.NZ x (some p))) = _
    rw [M₁₂.transition]
    symm
    exact compiled_state M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
      (M₁₂.timeIndex x p)
  readout := by
    intro x
    change (Z₁.RZ x).map (M₂₃.outputMap ∘ M₁₂.outputMap) =
      Z₃.RZ (M₂₃.stateMap (M₁₂.stateMap x))
    rw [← Option.map_map, M₁₂.readout, M₂₃.readout]

theorem systemMode_transitive
    (h₁₂ : IsSystemMode Z₁ Z₂) (h₂₃ : IsSystemMode Z₂ Z₃) :
    IsSystemMode Z₁ Z₃ := by
  rcases h₁₂ with ⟨M₁₂⟩
  rcases h₂₃ with ⟨M₂₃⟩
  exact ⟨M₁₂.trans M₂₃⟩

/-- Constant time index makes compiled elapsed time a product. -/
theorem compiledElapsed_constantTime
    (M : SystemMode Z₁ Z₂) (d : Time) (htime : HasConstantTimeIndex M d)
    (x : S₁) (f : ITZ I₁) :
    ∀ n, compiledElapsed M x f n = d * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [compiledElapsed, Nat.mul_succ, ih, htime.2]

/-- Constant input makes every value of a compiled trajectory the embedded input. -/
theorem compiledInput_constant
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (x : S₁) (p : I₁) :
    ∀ n t, compiledInput M x (fun _ => p) n t = M.inputMap p := by
  intro n
  induction n with
  | zero =>
      intro t
      exact hinput x p t
  | succ n ih =>
      intro t
      simp only [compiledInput]
      unfold concatenate
      split
      · exact ih t
      · apply hinput

/--
Composite of two constant-input, constant-time modes: time index multiplies and
the composite remains constant-input.
-/
theorem SystemMode.trans_constant
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (hIn₁₂ : HasConstantInput M₁₂) (e : Time) (hE : HasConstantTimeIndex M₁₂ e)
    (hIn₂₃ : HasConstantInput M₂₃) (d : Time) (hD : HasConstantTimeIndex M₂₃ d) :
    HasConstantInput (M₁₂.trans M₂₃) ∧
      HasConstantTimeIndex (M₁₂.trans M₂₃) (e * d) := by
  refine ⟨?_, ?_⟩
  · intro x p t
    change compiledInput M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
        (M₁₂.timeIndex x p) t =
      (M₂₃.inputMap ∘ M₁₂.inputMap) p
    have hfun : M₁₂.inputIndex x p = fun _ => M₁₂.inputMap p := by
      funext u; exact hIn₁₂ x p u
    have hdur : M₁₂.timeIndex x p = e := hE.2 x p
    rw [hfun, hdur]
    simpa [Function.comp_apply] using compiledInput_constant M₂₃ hIn₂₃
      (M₁₂.stateMap x) (M₁₂.inputMap p) e t
  · refine ⟨Nat.mul_pos hE.1 hD.1, fun x p => ?_⟩
    change compiledElapsed M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
        (M₁₂.timeIndex x p) = e * d
    have hfun : M₁₂.inputIndex x p = fun _ => M₁₂.inputMap p := by
      funext u; exact hIn₁₂ x p u
    have hdur : M₁₂.timeIndex x p = e := hE.2 x p
    rw [hfun, hdur, compiledElapsed_constantTime M₂₃ d hD]
    rw [Nat.mul_comm]

/-- Not manifest at time 0 implies not in-mode at time 0. -/
theorem not_inMode_of_not_manifest_zero
    (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t : Time)
    (h : ¬ ManifestAt M f x t 0) : ¬ InModeAt M f x t 0 := by
  intro hin
  cases hin with
  | inl hM => exact h hM
  | inr hway =>
      rcases hway with ⟨r, x₁, p₁, hr0, _, hx₁, _, _, _⟩
      have hr : r = 0 := Nat.eq_zero_of_le_zero hr0
      subst hr
      exact h ⟨Nat.zero_le t, x₁, hx₁⟩

end WymoreSystemModes
