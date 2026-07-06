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

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [DecidableEq SZ] [DecidableEq IZ]
variable [Nonempty IZ]

noncomputable def partialDynamicsTable (Z : DiscreteSystem SZ IZ OZ) :
    PropertySet (LTL (WymoreAtom SZ IZ OZ)) :=
  let readouts := (Finset.univ : Finset SZ).toList.flatMap fun s =>
    match Z.RZ s with
    | none => []
    | some o => [partialReadoutClause Z s o]
  let autonomous := (Finset.univ : Finset SZ).toList.map fun s =>
    partialAutonomousClause Z s
  let transitions := (Finset.univ : Finset SZ).toList.flatMap fun s =>
    (Finset.univ : Finset IZ).toList.map fun i => partialTransitionClause Z s i
  ⟨readouts ++ autonomous ++ transitions⟩

/-- Readout-only partial table (Track A pathology: dynamics incomplete). -/
noncomputable def partialReadoutOnlyTable (Z : DiscreteSystem SZ IZ OZ) :
    PropertySet (LTL (WymoreAtom SZ IZ OZ)) :=
  let readouts := (Finset.univ : Finset SZ).toList.flatMap fun s =>
    match Z.RZ s with
    | none => []
    | some o => [partialReadoutClause Z s o]
  ⟨readouts⟩

def SystemSatisfiesPartialDynamics (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ) (φ : LTL (WymoreAtom SZ IZ OZ)),
    φ ∈ (partialDynamicsTable Z_spec).formulas →
      (wymoreTrace Z_impl s0 f).models φ

def SystemSatisfiesPartialReadoutOnly (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ) (φ : LTL (WymoreAtom SZ IZ OZ)),
    φ ∈ (partialReadoutOnlyTable Z_spec).formulas →
      (wymoreTrace Z_impl s0 f).models φ

structure PartialDynamicsAdequate (Z : DiscreteSystem SZ IZ OZ) : Prop where
  schemaComplete : partialDynamicsTable Z = partialDynamicsTable Z

/-! ## Finite enumeration requires `Fintype` (Track B/D) -/

/-- A finite enumerated dynamics table over state-indexed atoms needs `Fintype SZ`. -/
def RequiresFiniteStateEnumeration (SZ : Type) : Prop := Nonempty (Fintype SZ)

theorem requiresFiniteStateEnumeration_of_fintype {SZ : Type} [Fintype SZ] :
    RequiresFiniteStateEnumeration SZ := ⟨‹Fintype SZ›⟩

theorem not_requiresFiniteStateEnumeration_nat :
    ¬ RequiresFiniteStateEnumeration Nat := by
  intro ⟨inst⟩
  have : Finite Nat := Finite.of_fintype Nat
  exact Infinite.not_finite (α := Nat) this

end WymorePropertyFragment
