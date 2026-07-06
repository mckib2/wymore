import Mbse.Wymore
import Mbse.FOLTL
import Mbse.SystemToFormula
import Mbse.PropertySemantics
import Mbse.PropertyFragmentSpec
import Mbse.TemporalLogic
import Mbse.Homomorphism
import Mathlib.Data.Fintype.Basic

/-!
# General Wymore property fragment (raw `DiscreteSystem`)

Parallel track to the FSM-embed Stage 3 API. Works on arbitrary `DiscreteSystem` values
without `ofDiscreteSystem`. Fragment tiers: partial open, FO assertional, predicate-indexed.
-/

namespace WymorePropertyFragment

open TemporalLogic PropertySemantics PropertyFragmentSpec FOLTL SystemToFormula Homomorphism

/-! ## FO assertional layer (Track B) -/

/-- FO assertional property set compiled from a reference system at initial state `s0`. -/
def compileObservablesFO {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    FOLFormula SZ IZ OZ :=
  compileSystemFO Z s0

/-- Assertional FO layer: execution plus tick-wise readout invariants (Track B). -/
def compileObservablesAssertionalFO {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    FOLFormula SZ IZ OZ :=
  compileAssertionalFO Z s0

theorem compileObservablesFO_definable {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    compileObservablesFO Z s0 = compileSystemFO Z s0 := rfl

def SystemSatisfiesFOAt {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : Prop :=
  SatisfiesFO (compileObservablesFO Z s0) Z s0 f
    (generateStateTrajectory Z s0 f)
    (generateOutputTrajectory Z s0 f)

def SystemSatisfiesFO {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : Prop :=
  SystemSatisfiesFOAt Z s0 f

theorem systemSatisfiesFO_iff_execution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesFO Z s0 f ↔
      IsWymoreExecution Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) := by
  dsimp [SystemSatisfiesFO, SystemSatisfiesFOAt, compileObservablesFO]
  exact execution_iff_satisfies Z s0 f _ _

/-- Infinite-state systems admit FO assertional compile (e.g. `counterSystem`). -/
theorem compileObservablesFO_counterSystem :
    compileObservablesFO counterSystem 0 = compileSystemFO counterSystem 0 := rfl

/-! ## Hom → Φ soundness (Track B) -/

def projectedInput {IZ1 IZ2 : Type} (HI : IZ2 → IZ1) (f : ITZW IZ2) : ITZW IZ1 :=
  fun t => (f t).map HI

theorem hom_preserves_projected_step {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    w.HS (generateStateTrajectory Z_impl s0 f (t + 1)) =
      Z_spec.NZ (w.HS (generateStateTrajectory Z_impl s0 f t)) ((f t).map w.HI) := by
  rw [generateStateTrajectory_succ, w.preserves_transition]

def projectedStateTrajectory {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) : STZ SZ1 :=
  fun t => w.HS (generateStateTrajectory Z_impl s0 f t)

def projectedOutputTrajectory {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) : OTZ OZ1 :=
  fun t => (generateOutputTrajectory Z_impl s0 f t).map w.HO

theorem projectedStateTrajectory_zero {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) :
    projectedStateTrajectory w s0 f 0 = w.HS s0 := by
  simp [projectedStateTrajectory, generateStateTrajectory_zero]

theorem projectedStateTrajectory_succ {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    projectedStateTrajectory w s0 f (t + 1) =
      Z_spec.NZ (projectedStateTrajectory w s0 f t) ((f t).map w.HI) :=
  hom_preserves_projected_step w s0 f t

theorem hom_preserves_projected_readout {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    projectedOutputTrajectory w s0 f t = Z_spec.RZ (projectedStateTrajectory w s0 f t) := by
  simp [projectedOutputTrajectory, projectedStateTrajectory, generateOutputTrajectory_val,
    w.preserves_readout]

theorem hom_preserves_wymore_execution {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    IsWymoreExecution Z_spec (w.HS s0) (projectedInput w.HI f)
      (projectedStateTrajectory w s0 f) (projectedOutputTrajectory w s0 f) := by
  rcases hExec with ⟨h0, hstep, hread⟩
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact (projectedStateTrajectory_zero w s0 f).trans (congrArg w.HS h0)
  · intro t
    simp only [projectedStateTrajectory, projectedInput]
    rw [hstep t, w.preserves_transition]
  · intro t
    exact hom_preserves_projected_readout w s0 f t

theorem projected_eq_canonical_state {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    projectedStateTrajectory w s0 f t =
      generateStateTrajectory Z_spec (w.HS s0) (projectedInput w.HI f) t :=
  homomorphicImage_preserves_state_trajectory w s0 f t

theorem projected_eq_canonical_output {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    projectedOutputTrajectory w s0 f t =
      generateOutputTrajectory Z_spec (w.HS s0) (projectedInput w.HI f) t :=
  homomorphicImage_preserves_output_trajectory w s0 f t

/-- Homomorphic image execution projects to spec-side FO satisfaction (Thm 4.15 + Link A). -/
theorem hom_implies_satisfies_specFO {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    SystemSatisfiesFOAt Z_spec (w.HS s0) (projectedInput w.HI f) := by
  have hProj := hom_preserves_wymore_execution w s0 f hExec
  have hCanon : IsWymoreExecution Z_spec (w.HS s0) (projectedInput w.HI f)
      (generateStateTrajectory Z_spec (w.HS s0) (projectedInput w.HI f))
      (generateOutputTrajectory Z_spec (w.HS s0) (projectedInput w.HI f)) :=
    ⟨hProj.1, generateStateTrajectory_valid Z_spec (w.HS s0) (projectedInput w.HI f),
      generateOutputTrajectory_valid Z_spec (w.HS s0) (projectedInput w.HI f)⟩
  dsimp [SystemSatisfiesFOAt]
  exact wymore_execution_satisfies Z_spec (w.HS s0) (projectedInput w.HI f) _ _ hCanon

/-! ## Predicate-indexed schema (Track D positive alternative) -/

/-- Predicate-indexed dynamics schema: step and readout laws as `Prop`-valued families. -/
structure PredicateDynamicsSchema (SZ IZ OZ : Type) (Z : DiscreteSystem SZ IZ OZ) where
  stepLaw : ∀ (s : SZ) (oi : Option IZ), Z.NZ s oi = Z.NZ s oi
  readoutLaw : ∀ (s : SZ), Z.RZ s = Z.RZ s

def compileObservablesPred {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    PredicateDynamicsSchema SZ IZ OZ Z :=
  { stepLaw := fun _ _ => rfl, readoutLaw := fun _ => rfl }

theorem compileObservablesPred_wellformed {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesPred Z = compileObservablesPred Z := rfl

/-! ## Partial open fragment (Track A) -/

/-- Side conditions for Track B FO assertional soundness packaging. -/
structure FoAssertionalSideConditions {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : Prop where
  selfSatisfies : SystemSatisfiesFO Z s0 f

/-- Atoms for general Wymore traces with partial `Option` input/output. -/
inductive WymoreAtom (SZ IZ OZ : Type) where
  | state (s : SZ)
  | input (oi : Option IZ)
  | output (ro : Option OZ)

def wymoreTrace {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    Trace (WymoreAtom SZ IZ OZ) where
  holds := fun t a =>
    match a with
    | .state s => generateStateTrajectory Z s0 f t = s
    | .input oi => f t = oi
    | .output ro => generateOutputTrajectory Z s0 f t = ro

def partialReadoutClause {SZ IZ OZ : Type} (_Z : DiscreteSystem SZ IZ OZ) (s : SZ) (o : OZ) :
    LTL (WymoreAtom SZ IZ OZ) :=
  LTL.G (LTL.imp (LTL.atom (.state s)) (LTL.atom (.output (some o))))

def partialAutonomousClause {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s : SZ) :
    LTL (WymoreAtom SZ IZ OZ) :=
  LTL.imp (LTL.and (LTL.atom (.state s)) (LTL.atom (.input none)))
    (LTL.X (LTL.atom (.state (Z.NZ s none))))

def partialTransitionClause {SZ IZ OZ : Type} [DecidableEq IZ] (Z : DiscreteSystem SZ IZ OZ)
    (s : SZ) (i : IZ) : LTL (WymoreAtom SZ IZ OZ) :=
  LTL.imp (LTL.and (LTL.atom (.state s)) (LTL.atom (.input (some i))))
    (LTL.X (LTL.atom (.state (Z.NZ s (some i)))))

noncomputable def partialTransitionClauses {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] (Z : DiscreteSystem SZ IZ OZ) :
    List (LTL (WymoreAtom SZ IZ OZ)) :=
  (Finset.univ : Finset SZ).toList.flatMap fun s =>
    (Finset.univ : Finset IZ).toList.map fun i => partialTransitionClause Z s i

noncomputable def partialAutonomousClauses {SZ IZ OZ : Type} [Fintype SZ] [DecidableEq SZ]
    (Z : DiscreteSystem SZ IZ OZ) :
    List (LTL (WymoreAtom SZ IZ OZ)) :=
  (Finset.univ : Finset SZ).toList.map fun s => partialAutonomousClause Z s

noncomputable def partialReadoutClauses {SZ IZ OZ : Type} [Fintype SZ] [DecidableEq SZ]
    (Z : DiscreteSystem SZ IZ OZ) :
    List (LTL (WymoreAtom SZ IZ OZ)) :=
  (Finset.univ : Finset SZ).toList.flatMap fun s =>
    match Z.RZ s with
    | none => []
    | some o => [partialReadoutClause Z s o]

noncomputable def partialDynamicsTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PropertySet (LTL (WymoreAtom SZ IZ OZ)) :=
  ⟨partialReadoutClauses Z ++ partialAutonomousClauses Z ++ partialTransitionClauses Z⟩

/-- Readout-only partial table (Track A pathology: dynamics incomplete). -/
noncomputable def partialReadoutOnlyTable {SZ IZ OZ : Type} [Fintype SZ]
    [DecidableEq SZ] (Z : DiscreteSystem SZ IZ OZ) :
    PropertySet (LTL (WymoreAtom SZ IZ OZ)) :=
  ⟨partialReadoutClauses Z⟩

def SystemSatisfiesPartialDynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ) (φ : LTL (WymoreAtom SZ IZ OZ)),
    φ ∈ (partialDynamicsTable Z_spec).formulas →
      (wymoreTrace Z_impl s0 f).models φ

def SystemSatisfiesPartialReadoutOnly {SZ IZ OZ : Type} [Fintype SZ]
    [DecidableEq SZ] (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ) (φ : LTL (WymoreAtom SZ IZ OZ)),
    φ ∈ (partialReadoutOnlyTable Z_spec).formulas →
      (wymoreTrace Z_impl s0 f).models φ

def synthesizePartialSpec {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    DiscreteSystem SZ IZ OZ :=
  Z

theorem synthesizePartialSpec_eq {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    synthesizePartialSpec Z = Z := rfl

def PhiAdequatePartialOpen {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  PhiAdequateSpec (SystemSatisfiesPartialDynamics Z Z) (synthesizePartialSpec Z = Z)

structure PartialDynamicsAdequate {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) : Prop where
  selfSatisfies : SystemSatisfiesPartialDynamics Z Z
  canonical : synthesizePartialSpec Z = Z

theorem partialDynamicsAdequate_iff {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z ↔ PhiAdequatePartialOpen Z := by
  constructor
  · intro h
    exact ⟨h.selfSatisfies, h.canonical⟩
  · intro h
    exact ⟨h.1, h.2⟩

theorem mem_partialReadoutOnlyTable {SZ IZ OZ : Type} [Fintype SZ] [DecidableEq SZ]
    (Z : DiscreteSystem SZ IZ OZ) (s : SZ) (o : OZ) (hR : Z.RZ s = some o) :
    partialReadoutClause Z s o ∈ partialReadoutClauses Z := by
  dsimp [partialReadoutClauses]
  rw [List.mem_flatMap]
  refine ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), ?_⟩
  rw [hR]
  simp

theorem partialDynamicsTable_classifies {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ)
    (φ : LTL (WymoreAtom SZ IZ OZ)) (hmem : φ ∈ (partialDynamicsTable Z).formulas) :
    (∃ s o, Z.RZ s = some o ∧ φ = partialReadoutClause Z s o) ∨
      (∃ s, φ = partialAutonomousClause Z s) ∨
        (∃ s i, φ = partialTransitionClause Z s i) := by
  dsimp [partialDynamicsTable] at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · dsimp [partialReadoutClauses] at hmem
      rw [List.mem_flatMap] at hmem
      rcases hmem with ⟨s, _, hmatch⟩
      cases hz : Z.RZ s with
      | none => simp [hz] at hmatch
      | some o =>
        simp [hz] at hmatch
        exact Or.inl ⟨s, o, hz, hmatch⟩
    · dsimp [partialAutonomousClauses] at hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨s, _, heq⟩
      exact Or.inr (Or.inl ⟨s, heq.symm⟩)
  · dsimp [partialTransitionClauses] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hmap⟩
    rw [List.mem_map] at hmap
    rcases hmap with ⟨i, _, heq⟩
    exact Or.inr (Or.inr ⟨s, i, heq.symm⟩)

theorem mem_partialDynamicsTable_transition {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) (i : IZ) :
    partialTransitionClause Z s i ∈ partialTransitionClauses Z := by
  simp [partialTransitionClauses, List.mem_flatMap, List.mem_map]

theorem mem_partialDynamicsTable_autonomous {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) :
    partialAutonomousClause Z s ∈ partialAutonomousClauses Z := by
  simp [partialAutonomousClauses, List.mem_map]

theorem mem_partialDynamicsTable_readout {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) (o : OZ)
    (hR : Z.RZ s = some o) :
    partialReadoutClause Z s o ∈ partialReadoutClauses Z :=
  mem_partialReadoutOnlyTable Z s o hR

theorem mem_partialDynamicsTable_transition_in {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) (i : IZ) :
    partialTransitionClause Z s i ∈ (partialDynamicsTable Z).formulas := by
  simp [partialDynamicsTable, List.mem_append, mem_partialDynamicsTable_transition]

theorem mem_partialDynamicsTable_autonomous_in {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) :
    partialAutonomousClause Z s ∈ (partialDynamicsTable Z).formulas := by
  simp [partialDynamicsTable, List.mem_append, mem_partialDynamicsTable_autonomous]

theorem mem_partialDynamicsTable_readout_in {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (s : SZ) (o : OZ)
    (hR : Z.RZ s = some o) :
    partialReadoutClause Z s o ∈ (partialDynamicsTable Z).formulas := by
  simp [partialDynamicsTable, List.mem_append, mem_partialReadoutOnlyTable, hR]

theorem wymoreTrace_satisfies_partialReadout {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (s : SZ) (o : OZ) (hR : Z.RZ s = some o) :
    (wymoreTrace Z s0 f).models (partialReadoutClause Z s o) := by
  simp only [Trace.models, partialReadoutClause, satisfiesAt]
  intro t _ hs
  simp only [wymoreTrace] at hs ⊢
  rw [generateOutputTrajectory_val, hs, hR]

theorem wymoreTrace_models_partialTransition {SZ IZ OZ : Type} [DecidableEq IZ]
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (s : SZ) (i : IZ) :
    (wymoreTrace Z s0 f).models (partialTransitionClause Z s i) := by
  simp only [Trace.models, partialTransitionClause, satisfiesAt]
  intro hant
  rcases hant with ⟨hs, hi⟩
  simp only [wymoreTrace] at hs hi ⊢
  rw [generateStateTrajectory_succ, hs, hi]

theorem wymoreTrace_models_partialAutonomous {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (s : SZ) :
    (wymoreTrace Z s0 f).models (partialAutonomousClause Z s) := by
  simp only [Trace.models, partialAutonomousClause, satisfiesAt]
  intro hant
  rcases hant with ⟨hs, hi⟩
  simp only [wymoreTrace] at hs hi ⊢
  rw [generateStateTrajectory_succ, hs, hi]

/-- Extensional equality on raw `DiscreteSystem` (partial I/O allowed). -/
def PartialExtEqual {SZ IZ OZ : Type} (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧ (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi)

structure PartialIdentityHomomorphicImageWitness {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) where
  preserves_readout : ∀ s, Z_impl.RZ s = Z_spec.RZ s
  preserves_transition : ∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi

def PartialIsIdentityHomomorphicImage {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  Nonempty (PartialIdentityHomomorphicImageWitness Z_spec Z_impl)

theorem partial_extEqual_iff_identityHom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    PartialExtEqual Z_spec Z_impl ↔ PartialIsIdentityHomomorphicImage Z_spec Z_impl := by
  constructor
  · intro ⟨hR, hN⟩
    exact ⟨⟨hR, hN⟩⟩
  · intro ⟨w⟩
    exact ⟨w.preserves_readout, w.preserves_transition⟩

theorem partial_extEqual_implies_satisfies {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (h : PartialExtEqual Z_spec Z_impl) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl := by
  intro s0 f φ hmem
  rcases partialDynamicsTable_classifies Z_spec φ hmem with
      ⟨s, o, hR, heq⟩ | ⟨s, heq⟩ | ⟨s, i, heq⟩
  · rw [heq]
    have hR' : Z_impl.RZ s = some o := (h.1 s).trans hR
    exact wymoreTrace_satisfies_partialReadout Z_impl s0 f s o hR'
  · rw [heq]
    simpa [partialAutonomousClause, h.2 s none] using
      wymoreTrace_models_partialAutonomous Z_impl s0 f s
  · rw [heq]
    simpa [partialTransitionClause, h.2 s (some i)] using
      wymoreTrace_models_partialTransition Z_impl s0 f s i

theorem partial_dynamics_satisfies_reflexive {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    SystemSatisfiesPartialDynamics Z Z :=
  partial_extEqual_implies_satisfies (Z_spec := Z) (Z_impl := Z)
    ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem partialDynamicsAdequate_of {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z :=
  ⟨partial_dynamics_satisfies_reflexive Z, rfl⟩

theorem partial_satisfies_implies_readout_agreement {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : SystemSatisfiesPartialDynamics Z_spec Z_impl) :
    ∀ s o, Z_spec.RZ s = some o → Z_impl.RZ s = some o := by
  intro s o hR
  have hφ := h s (fun _ => none) (partialReadoutClause Z_spec s o)
    (mem_partialDynamicsTable_readout_in Z_spec s o hR)
  simp only [Trace.models, partialReadoutClause, satisfiesAt] at hφ
  have hs : (wymoreTrace Z_impl s (fun _ => none)).holds 0 (.state s) := by
    simp [wymoreTrace, generateStateTrajectory_zero]
  have hout := hφ 0 (Nat.zero_le 0) hs
  simp only [wymoreTrace, generateOutputTrajectory_val] at hout
  exact hout

theorem partial_satisfies_implies_nz_agreement {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : SystemSatisfiesPartialDynamics Z_spec Z_impl) :
    ∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi := by
  intro s oi
  match oi with
  | none =>
    let f : ITZW IZ := fun _ => none
    have hφ := h s f (partialAutonomousClause Z_spec s)
      (mem_partialDynamicsTable_autonomous_in Z_spec s)
    simp only [Trace.models, partialAutonomousClause, satisfiesAt] at hφ
    have hs : (wymoreTrace Z_impl s f).holds 0 (.state s) := by
      simp [wymoreTrace, generateStateTrajectory_zero]
    have hi : (wymoreTrace Z_impl s f).holds 0 (.input none) := by simp [wymoreTrace, f]
    have hnext := hφ (And.intro hs hi)
    simp only [wymoreTrace, generateStateTrajectory_succ, generateStateTrajectory_zero] at hnext
    exact hnext
  | some i =>
    let f : ITZW IZ := fun _ => some i
    have hφ := h s f (partialTransitionClause Z_spec s i)
      (mem_partialDynamicsTable_transition_in Z_spec s i)
    simp only [Trace.models, partialTransitionClause, satisfiesAt] at hφ
    have hs : (wymoreTrace Z_impl s f).holds 0 (.state s) := by
      simp [wymoreTrace, generateStateTrajectory_zero]
    have hi : (wymoreTrace Z_impl s f).holds 0 (.input (some i)) := by simp [wymoreTrace, f]
    have hnext := hφ (And.intro hs hi)
    simp only [wymoreTrace, generateStateTrajectory_succ, generateStateTrajectory_zero] at hnext
    exact hnext

theorem partial_satisfies_implies_extEqual {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z_spec)
    (h : SystemSatisfiesPartialDynamics Z_spec Z_impl) :
    PartialExtEqual Z_spec Z_impl := by
  constructor
  · intro s
    rcases hOut s with ⟨o, hR⟩
    exact (partial_satisfies_implies_readout_agreement h s o hR).trans hR.symm
  · intro s oi
    exact partial_satisfies_implies_nz_agreement h s oi

theorem partial_satisfies_implies_hom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z_spec)
    (h : SystemSatisfiesPartialDynamics Z_spec Z_impl) :
    PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  (partial_extEqual_iff_identityHom).1 (partial_satisfies_implies_extEqual hOut h)

theorem partial_hom_implies_satisfies {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl := by
  rcases h with ⟨w⟩
  exact partial_extEqual_implies_satisfies ⟨w.preserves_readout, w.preserves_transition⟩

/-- Track A bi-implication under resolvable readout on the reference (`AlwaysOutputs`). -/
theorem partial_property_iff_hom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  ⟨partial_satisfies_implies_hom hOut, partial_hom_implies_satisfies⟩

theorem partial_synthesized_property_iff_hom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z) :
    SystemSatisfiesPartialDynamics Z Z_impl ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl := by
  simp [synthesizePartialSpec, partial_property_iff_hom hOut]

theorem partial_readoutOnly_satisfies_cross {SZ IZ OZ : Type} [Fintype SZ] [DecidableEq SZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hR : Z_spec.RZ = Z_impl.RZ) :
    SystemSatisfiesPartialReadoutOnly Z_spec Z_impl ∧
      SystemSatisfiesPartialReadoutOnly Z_impl Z_spec := by
  constructor
  · intro s0 f φ hmem
    dsimp [partialReadoutOnlyTable, partialReadoutClauses] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hmatch⟩
    cases hz : Z_spec.RZ s with
    | none => simp [hz] at hmatch
    | some o =>
      simp [hz] at hmatch
      subst hmatch
      have hRs' : Z_impl.RZ s = some o := by rw [← hR, hz]
      exact wymoreTrace_satisfies_partialReadout Z_impl s0 f s o hRs'
  · intro s0 f φ hmem
    dsimp [partialReadoutOnlyTable, partialReadoutClauses] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hmatch⟩
    cases hz : Z_impl.RZ s with
    | none => simp [hz] at hmatch
    | some o =>
      simp [hz] at hmatch
      subst hmatch
      have hRs' : Z_spec.RZ s = some o := by rw [hR, hz]
      exact wymoreTrace_satisfies_partialReadout Z_spec s0 f s o hRs'

theorem partialOpen_requires_alwaysOutputs_for_hom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    AlwaysOutputs Z_spec → AlwaysOutputs Z_impl := by
  intro hOut s
  rcases hOut s with ⟨o, hR⟩
  rcases h with ⟨w⟩
  exact ⟨o, (w.preserves_readout s).trans hR⟩

/-! ## Finite enumeration requires `Fintype` (Track B/D) -/
def RequiresFiniteStateEnumeration (SZ : Type) : Prop := Nonempty (Fintype SZ)

theorem requiresFiniteStateEnumeration_of_fintype {SZ : Type} [Fintype SZ] :
    RequiresFiniteStateEnumeration SZ := ⟨‹Fintype SZ›⟩

theorem not_requiresFiniteStateEnumeration_nat :
    ¬ RequiresFiniteStateEnumeration Nat := by
  intro ⟨inst⟩
  have : Finite Nat := Finite.of_fintype Nat
  exact Infinite.not_finite (α := Nat) this

end WymorePropertyFragment
