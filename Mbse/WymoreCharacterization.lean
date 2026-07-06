import Mbse.WymorePropertyFragment
import Mbse.WymorePathologyExamples
import Mbse.FragmentPathologyRegistry
import Mbse.HomSoundness
import Mbse.PropertyFragmentSpec
import Mbse.SystemToFormula
import Mbse.GeneralProperties
import Mbse.GeneralPropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.TemporalLogic
import Mbse.SpecFromProperties
import Mbse.HimsySynthesis
import Mbse.GeneralCharacterization
import Mbse.ObservablesFromSpec
import Mbse.SystemToLTL
import Mbse.Homomorphism
import Mbse.HomomorphismProperties
import Mbse.TracePropertyLayer
import Mbse.HomWitnessConstruction

/-!
# General Wymore property characterization

Consolidates FO assertional soundness, impossibility results, partial-open fragment,
extensional dynamics, and predicate-indexed alternatives. LTS refinement lives in
[`LTSCharacterization`](LTSCharacterization.lean).
-/

namespace WymoreCharacterization

open WymorePropertyFragment WymorePathologyExamples FragmentPathologyRegistry
  PropertyFragmentSpec PropertySemantics HomSoundness GeneralProperties
  ExtensionalDynamicsFragment SpecFromProperties HimsySynthesis GeneralCharacterization
  ObservablesFromSpec SystemToLTL Homomorphism HomomorphismProperties
  TracePropertyLayer HomWitnessConstruction PropertyFragment.FSM
  SystemToFormula PropertyFragment.General PropertyFragment.FSM FSMProperties PathologyExamples
  TemporalLogic ExtensionalDynamicsFragment FOLTL SpecFromProperties HimsySynthesis
  GeneralCharacterization ObservablesFromSpec SystemToLTL FSM Homomorphism HomomorphismProperties

/-! ## FO assertional -/

theorem stageWymore_fo_compile {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    compileObservablesFO Z s0 = compileSystemFO Z s0 :=
  compileObservablesFO_definable Z s0

theorem stageWymore_fo_satisfies_iff_execution {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesFO Z s0 f ↔
      IsWymoreExecution Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) :=
  systemSatisfiesFO_iff_execution Z s0 f

theorem stageWymore_fo_assertional_compile {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    compileObservablesAssertionalFO Z_spec Z_impl s0 = compileAssertionalFO Z_spec Z_impl s0 := rfl

theorem stageWymore_fo_assertional_iff_extensional {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesSpecAssertionalFOAt Z_spec Z_impl s0 f ↔
      SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl :=
  assertionalFO_at_iff_extensional hSpec hImpl s0 f

theorem stageWymore_fo_verification {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    SystemSatisfiesFOAt Z_spec (w.HS s0) (projectedInput w.HI f) :=
  hom_implies_satisfies_specFO w s0 f hExec

theorem stageWymore_fo_soundness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (_hSide : FoAssertionalSideConditions Z_spec (w.HS s0) (projectedInput w.HI f))
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    SystemSatisfiesFOAt Z_spec (w.HS s0) (projectedInput w.HI f) :=
  hom_implies_satisfies_specFO w s0 f hExec

theorem stageWymore_fo_execution_link {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesFO Z s0 f ↔
      IsWymoreExecution Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) :=
  stageWymore_fo_satisfies_iff_execution Z s0 f

theorem stageWymore_counterSystem_fo :
    SystemSatisfiesFO counterSystem 0 (fun _ => some true) :=
  counterSystem_satisfies_own_FO

/-- FO assertional fragment: hom→Φ soundness only; completeness is on extensional fragment. -/
theorem stageWymore_fo_soundness_only_note :
    foAssertionalFragment.finiteClauseEnumeration = false ∧
      extensionalDynamicsFragment.dynamicsComplete = true :=
  ⟨foAssertional_no_finite_enum, extensionalDynamics_dynamicsComplete⟩

/-! ## Extensional dynamics (infinite `SZ`) -/

theorem stageWymore_extensional_compile {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesExt Z = compileObservablesExt Z :=
  rfl

theorem stageWymore_extensional_property_iff_hom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl :=
  extensional_property_iff_hom hSpec hImpl

theorem stageWymore_extensional_soundness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    SystemSatisfiesExtensionalAt w :=
  hom_implies_satisfies_extensional w

theorem stageWymore_counterSystem_extensional :
    SystemSatisfiesExtensional counterSystem counterSystem counterSystem_alwaysOutputs
      counterSystem_alwaysOutputs :=
  counterSystem_satisfies_own_extensional

theorem stageWymore_extensional_fo_bridge {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl)
    (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesSpecFOAt Z_spec Z_impl s0 f :=
  extensional_implies_systemSatisfiesSpecFOAt hSpec hImpl h s0 f

theorem stageWymore_extensional_subsumes_executionFO {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesExtensional Z Z hOut hOut → SystemSatisfiesFO Z s0 f :=
  extensional_subsumes_executionFO Z hOut s0 f

theorem stageWymore_fo_extensional_completeness {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    (SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImageOpen Z Z_impl hZ hImpl) ∧
      (SystemSatisfiesExtensional Z Z_impl hZ hImpl →
        ∀ s0 f, SystemSatisfiesSpecFOAt Z Z_impl s0 f) :=
  extensional_adequate_verification_fo_bridge hZ hImpl hAdeq

theorem stageWymore_blocked_foAssertionalCompleteness :
    foAssertionalFragment.finiteClauseEnumeration = false ∧
      SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
        ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs :=
  blocked_foAssertionalCompleteness

theorem stageWymore_resolved_foAssertionalEncoding :
    SystemSatisfiesSpecAssertionalFOAt counterSystem counterSystem 0 (fun _ => some true) ∧
      ¬ SystemSatisfiesSpecAssertionalFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput :=
  resolved_foAssertionalEncoding

theorem stageWymore_resolved_sameTypeSurjectiveHomSeparation :
    SameTypeHomomorphicImage swapSpecSys swapImplSys ∧
      SystemSatisfiesExtensionalCross swapSpecSys swapImplSys ∧
        IsNonIdentityWitness swapHomWitness ∧
          ¬ SystemSatisfiesExtensional swapSpecSys swapImplSys
            swapSpecSys_alwaysOutputs swapImplSys_alwaysOutputs :=
  resolved_sameTypeSurjectiveHomSeparation

theorem stageWymore_resolved_predicateIndexedPartialCompile :
    SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
      (compileObservablesPartialOpen counterClosedReadout) ∧
      PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  resolved_predicateIndexedPartialCompile

/-! ## Cross-type extensional bi-implication -/

theorem stageWymore_extensional_cross_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesExtensionalCross Z_spec Z_impl ↔
      IsHomomorphicImage Z_spec Z_impl :=
  extensional_cross_property_iff_hom

theorem stageWymore_extensional_cross_soundness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesExtensionalCross Z_spec Z_impl :=
  extensional_cross_of_hom h

theorem stageWymore_counterElab_cross :
    SystemSatisfiesExtensionalCross counterSystem counterElab ∧
      IsHomomorphicImage counterSystem counterElab :=
  ⟨counterElab_satisfies_extensional_cross, counterElab_hom_to_counterSystem⟩

theorem stageWymore_extensional_sameType_implies_cross {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensionalCross Z_spec Z_impl :=
  extensional_sameType_implies_cross hSpec hImpl h

theorem stageWymore_extensional_sameType_collapse {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔
      (SystemSatisfiesExtensionalCross Z_spec Z_impl ∧
        SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) :=
  extensional_sameType_collapse_iff_hom hSpec hImpl

/-! ## Extensional synthesis + PhiAdequate -/

theorem stageWymore_extensional_synthesize_eq {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    synthesizeExtensionalSpec Z = Z :=
  synthesizeExtensionalSpec_eq Z

theorem stageWymore_extensional_link_b {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesExt (synthesizeExtensionalSpec Z) = compileObservablesExt Z :=
  compileObservablesExt_synthesize Z

theorem stageWymore_extensional_phi_adequate_cross {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    PhiAdequateExtensionalCross Z :=
  extensional_phi_adequate_cross Z

theorem stageWymore_extensional_phi_adequate_open {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) :
    PhiAdequateExtensionalOpen Z hOut :=
  extensional_phi_adequate_open Z hOut

theorem stageWymore_extensional_verification {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateExtensionalCross Z) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_synthesized_verification_cross _hAdeq

theorem stageWymore_extensional_verification_open {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  extensional_synthesized_verification_open hZ hImpl _hAdeq

theorem stageWymore_extensional_verification_equivalence {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl)
      (IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl)
      (PhiAdequateExtensionalCross Z) :=
  extensional_cross_verification_equivalence

theorem stageWymore_counterSystem_gated_verification :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab)
      (IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab)
      (PhiAdequateExtensionalCross counterSystem) :=
  stageWymore_extensional_verification_equivalence

theorem stageWymore_extensional_verification_equivalence_open {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    VerificationEquivalence
      (SystemSatisfiesExtensional Z Z_impl hZ hImpl)
      (SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl)
      (PhiAdequateExtensionalOpen Z hZ) :=
  extensional_open_verification_equivalence hZ hImpl

theorem stageWymore_counterSystem_synthesis :
    PhiAdequateExtensionalCross counterSystem ∧
      SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ∧
        IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab :=
  ⟨counterSystem_phi_adequate_cross, counterElab_satisfies_extensional_cross,
    counterElab_synthesized_hom⟩

/-! ## Infinite state impossibility (finite enumeration) -/

theorem stageWymore_infinite_no_finite_enum :
    ¬ RequiresFiniteStateEnumeration Nat :=
  counterSystem_no_finite_dynamicsTable

theorem stageWymore_predicate_schema {SZ IZ OZ : Type} [DecidableEq IZ]
    (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesPred Z = compileObservablesPartialOpen Z :=
  compileObservablesPred_eq_partialOpen Z

theorem stageWymore_partialDynamicsCompiled_iff_open {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    SystemSatisfiesPartialDynamicsCompiled Z_spec Z_impl (compileObservablesPartialOpen Z_spec) ↔
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl :=
  partialDynamicsCompiled_iff_open

theorem stageWymore_partialAssertionalFO_iff_partialDynamicsCompiled {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesSpecPartialAssertionalFOAt Z_spec Z_impl s0 f ↔
      SystemSatisfiesPartialDynamicsCompiled Z_spec Z_impl (compileObservablesPartialOpen Z_spec) :=
  partialAssertionalFO_at_iff_partialDynamicsCompiled hComplete s0 f

theorem stageWymore_compileObservablesPartial_schema {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesPartialDynamicsCompiled Z_spec Z_impl (compileObservablesPartialOpen Z_spec) ↔
      SystemSatisfiesSpecPartialAssertionalFOAt Z_spec Z_impl s0 f :=
  compileObservablesPartial_schema hComplete s0 f

/-! ## Partial open fragment -/

theorem stageWymore_partial_adequate {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z :=
  partial_adequate Z

theorem stageWymore_partial_readout_pathology :
    wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) ∧
      wymoreStay.RZ 0 = wymoreJump.RZ 0 := by
  refine ⟨wymoreStay_jump_different_step, ?_⟩
  simp [wymoreStay, wymoreJump, DiscreteSystem.ofTotal]

theorem stageWymore_partial_readout_only_blocked :
    SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
      SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
        wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) :=
  partial_readout_only_not_complete

theorem stageWymore_partial_identity_hom {Z_spec Z_impl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hDyn : SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  system_satisfies_implies_hom hSpec hImpl hDyn

theorem stageWymore_partial_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partial_property_iff_hom hOut

theorem stageWymore_partial_iff_hom_readoutComplete {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecComplete Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partial_property_iff_hom_readoutComplete hComplete

theorem stageWymore_closedSystem_partial :
    ReadoutSpecComplete closedSystem ∧
      (SystemSatisfiesPartialDynamics closedSystem closedSystemImpl ↔
        PartialIsIdentityHomomorphicImage closedSystem closedSystemImpl) :=
  closedSystem_resolved

theorem stageWymore_blocked_incompleteReadout :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl ∧
        ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl :=
  blocked_incompleteReadout

theorem stageWymore_resolved_partialClosedReadout :
    ReadoutSpecComplete closedSystem ∧
      (SystemSatisfiesPartialDynamics closedSystem closedSystemImpl ↔
        PartialIsIdentityHomomorphicImage closedSystem closedSystemImpl) :=
  resolved_partialClosedReadout

theorem stageWymore_blocked_autonomousInputIncomplete :
    pinnedFiniteFragment.dynamicsComplete = true ∧
      SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ PartialExtEqual autoNoneSpec autoNoneImpl :=
  blocked_autonomousInputIncomplete

theorem stageWymore_blocked_pinnedDynamicsIncomplete :
    pinnedFiniteFragment.dynamicsComplete = true ∧
      SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ SystemSatisfiesPartialDynamics autoNoneSpec autoNoneImpl :=
  blocked_pinnedDynamicsIncomplete

theorem stageWymore_resolved_infinitePartialReadout :
    ¬ AlwaysOutputs counterClosedReadout ∧
      SystemSatisfiesExtensionalPartial counterClosedReadout counterClosedReadout ∧
        PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  resolved_infinitePartialReadout

theorem stageWymore_resolved_infinitePartialDynamicsOpen :
    ¬ AlwaysOutputs counterClosedReadout ∧
      SystemSatisfiesPartialDynamicsOpen counterClosedReadout counterClosedReadout ∧
        PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  resolved_infinitePartialDynamicsOpen

theorem stageWymore_resolved_partialAssertionalFO :
    SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout 0
      counterClosedReadoutInput ∧
      PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  resolved_partialAssertionalFO

theorem stageWymore_resolved_partialCompileUnification :
    SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
      (compileObservablesPartialOpen counterClosedReadout) ∧
      SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout 0
        counterClosedReadoutInput ∧
      (∀ s0 f,
        SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
          (compileObservablesPartialOpen counterClosedReadout) ↔
          SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout s0 f) :=
  resolved_partialCompileUnification

theorem stageWymore_partialDynamicsOpen_iff_hom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) :
    SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partialDynamicsOpen_iff_hom hComplete

theorem stageWymore_partialDynamics_table_iff_open {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl :=
  partialDynamics_table_iff_open hComplete

theorem stageWymore_partial_verification {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z)
    (_hAdeq : PhiAdequatePartialOpen Z) :
    SystemSatisfiesPartialDynamics Z Z_impl ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl :=
  partial_synthesized_property_iff_hom hOut

theorem stageWymore_partial_soundness {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (_hOut : AlwaysOutputs Z_spec)
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl :=
  partial_hom_implies_satisfies h

theorem stageWymore_partial_fragment_sideConditions {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    (Z : DiscreteSystem SZ IZ OZ) (h : PartialOpenSideConditions SZ IZ OZ Z) :
    partialOpenFragment.dynamicsComplete = true :=
  h.dynamicsComplete

theorem stageWymore_closed_excluded :
    ¬ AlwaysOutputs closedSystem :=
  closedSystem_not_alwaysOutputs

theorem stageWymore_partial_fragment :
    partialOpenFragment.dynamicsComplete = true :=
  partialOpen_dynamicsComplete

/-! ## BLOCKED registry exports -/

theorem stageWymore_blocked_infiniteSZ : ¬ RequiresFiniteStateEnumeration Nat :=
  blocked_infiniteSZ

theorem stageWymore_resolved_infiniteSZ_extensional :
    extensionalDynamicsFragment.finiteClauseEnumeration = false ∧
      SystemSatisfiesExtensional counterSystem counterSystem counterSystem_alwaysOutputs
        counterSystem_alwaysOutputs :=
  ⟨extensionalDynamics_no_finite_enum, counterSystem_satisfies_own_extensional⟩

theorem stageWymore_resolved_crossTypeExtensional :
    SystemSatisfiesExtensionalCross counterSystem counterElab ∧
      IsHomomorphicImage counterSystem counterElab :=
  resolved_crossTypeExtensional

theorem stageWymore_blocked_partialRZ :
    pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem :=
  blocked_partialRZ

theorem stageWymore_blocked_readoutOnly :
    readoutOnlyFragment.dynamicsComplete = false ∧
      (FSMSatisfiesOutputTable fsmJump fsmStay ∧
        FSMSatisfiesOutputTable fsmStay fsmJump ∧
          ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump) :=
  blocked_readoutOnly

theorem stageWymore_blocked_eventuallyF :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      (∀ t, traceNoQ.holds t StutterAtom.p) ∧
        (∀ t, traceWithQ.holds t StutterAtom.p) ∧
          traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
            ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) :=
  blocked_eventuallyF

theorem stageWymore_blocked_eventuallyF_wymore :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) :=
  FragmentPathologyRegistry.blocked_eventuallyF_wymore

theorem stageWymore_blocked_barePhi_uniqueZ :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump :=
  blocked_barePhi_uniqueZ

theorem stageWymore_blocked_executionFOHomCompleteness :
    SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
      ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs :=
  blocked_executionFOHomCompleteness

theorem stageWymore_resolved_canonicalDisjunction :
    PropertyFragment.CombSatisfiesFunction implSystem implTable ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  resolved_canonicalDisjunction

theorem stageWymore_propositional_ltl_corollary {SZ IZ OZ : Type} [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F ↔
      ∀ (s0 : SZ) (f : ITZ IZ),
        (SystemToLTL.fsmTrace F s0 f).models (SystemToLTL.compileFSM F) :=
  fsm_satisfiesDynamics_self_iff_models_compileFSM F

theorem stageWymore_blocked_rawBranchingNZ :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
        SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
          wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  refine ⟨partialOpen_dynamicsComplete, ?_⟩
  exact partial_readout_only_not_complete

/-! ## Fragment specification alignment -/

theorem stageWymore_pinnedFinite_fragment :
    pinnedFiniteFragment = pinnedFragment :=
  pinnedFinite_eq_pinned

theorem stageWymore_fo_fragment :
    foAssertionalFragment.finiteClauseEnumeration = false :=
  foAssertional_no_finite_enum

theorem stageWymore_extensional_fragment :
    extensionalDynamicsFragment.finiteClauseEnumeration = false ∧
      extensionalDynamicsFragment.dynamicsComplete = true := by
  exact ⟨extensionalDynamics_no_finite_enum, extensionalDynamics_dynamicsComplete⟩

/-! ## HIMSY constructive synthesis -/

theorem stageWymore_himsy_eq_spec :
    HimsySpecEqual counterSystem (synthesizeHimsySpec counterElab_witness) :=
  counterSystem_eq_himsy_counterElab

theorem stageWymore_himsy_phi_adequate :
    PhiAdequateHimsy counterElab_witness :=
  counterSystem_himsy_phi_adequate

theorem stageWymore_himsy_verification {Z_impl : DiscreteSystem (Nat × Bool) Bool Nat} :
    PhiAdequateHimsy counterElab_witness →
      (SystemSatisfiesExtensionalCross (synthesizeHimsySpec counterElab_witness) Z_impl ↔
        IsHomomorphicImage (synthesizeHimsySpec counterElab_witness) Z_impl) :=
  himsy_synthesized_verification counterElab_witness

theorem stageWymore_himsy_verification_equivalence {Z_impl : DiscreteSystem (Nat × Bool) Bool Nat} :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeHimsySpec counterElab_witness) Z_impl)
      (IsHomomorphicImage (synthesizeHimsySpec counterElab_witness) Z_impl)
      (PhiAdequateHimsy counterElab_witness) :=
  himsy_verification_equivalence counterElab_witness

/-! ## Inverse table recovery -/

theorem stageWymore_recoverSpecFromTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (h : IsSynthesizableTable Phi Z hOut) :
    recoverSpecFromTable Phi Z hOut = Z ∧
      compileObservables (recoverSpecFromTable Phi Z hOut) hOut = Phi :=
  ⟨recoverSpecFromTable_eq Phi Z hOut h, recoverSpecFromTable_compiles Phi Z hOut h⟩

theorem stageWymore_fsmStay_recoverable :
    IsRecoverableExtensionalTable
      (dynamicsTable fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay))
      fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay) :=
  fsmStay_recoverable_table

/-! ## Finite unification (extensional ↔ partial ↔ pinned) -/

theorem stageWymore_extensional_iff_partialDynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hComplete : ReadoutSpecComplete Z_spec) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔
      SystemSatisfiesPartialDynamics Z_spec Z_impl :=
  extensional_iff_partialDynamics hSpec hImpl hComplete

theorem stageWymore_extensional_iff_partialExtEqual {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔ PartialExtEqual Z_spec Z_impl :=
  extensional_iff_partialExtEqual hSpec hImpl

theorem stageWymore_partialDynamics_iff_extEqual_readoutComplete {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [DecidableEq SZ] [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecComplete Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔ PartialExtEqual Z_spec Z_impl :=
  partialDynamics_iff_extEqual_readoutComplete hComplete

theorem stageWymore_extensional_synthesized_iff_partial_synthesized {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (hComplete : ReadoutSpecComplete Z) :
    (SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl) ↔
      (SystemSatisfiesPartialDynamics Z Z_impl ↔
        PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl) :=
  extensional_synthesized_iff_partial_synthesized_readoutComplete hZ hImpl hComplete

/-! ## Unified verification templates -/

theorem wymore_verification_pinned {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  system_synthesized_property_iff_hom hZ hImpl

theorem wymore_verification_partial_readoutComplete {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecComplete Z)
    (_hAdeq : PhiAdequatePartialOpen Z) :
    SystemSatisfiesPartialDynamics Z Z_impl ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl :=
  partial_synthesized_property_iff_hom_readoutComplete hComplete

theorem wymore_verification_extensional {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  extensional_synthesized_verification_open hZ hImpl _hAdeq

theorem wymore_verification_assertional_fo {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    ∀ s0 f, SystemSatisfiesSpecAssertionalFOAt Z Z_impl s0 f ↔
      SystemSatisfiesExtensional Z Z_impl hZ hImpl :=
  fun s0 f => assertionalFO_at_iff_extensional hZ hImpl s0 f

theorem wymore_verification_extensional_partial {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    SystemSatisfiesExtensionalPartial Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  extensional_partial_iff_hom

theorem wymore_verification_partial_open {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) :
    SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partialDynamicsOpen_iff_hom hComplete

theorem wymore_verification_partial_assertional_fo {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z_spec) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesSpecPartialAssertionalFOAt Z_spec Z_impl s0 f ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partialAssertionalFO_at_iff_hom hComplete s0 f

theorem wymore_verification_partial_compiled {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z)
    (_hAdeq : PhiAdequatePartialOpenPred Z) :
    SystemSatisfiesPartialDynamicsCompiled Z Z_impl (compileObservablesPartialOpen Z) ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl := by
  simp [synthesizePartialSpec, partialDynamicsCompiled_iff_hom hComplete]

theorem wymore_verification_partial_unified {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecCompleteOpen Z) (s0 : SZ) (f : ITZW IZ)
    (_hAdeq : PhiAdequatePartialOpenPred Z) :
    (SystemSatisfiesPartialDynamicsCompiled Z Z_impl (compileObservablesPartialOpen Z) ↔
        SystemSatisfiesSpecPartialAssertionalFOAt Z Z_impl s0 f) ∧
      (SystemSatisfiesPartialDynamicsCompiled Z Z_impl (compileObservablesPartialOpen Z) ↔
        PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl) :=
  ⟨compileObservablesPartial_schema hComplete s0 f,
    by simp [synthesizePartialSpec, partialDynamicsCompiled_iff_hom hComplete]⟩

theorem wymore_verification_extensional_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateExtensionalCross Z) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_synthesized_verification_cross _hAdeq

/-! ## Finite unification (pinned ↔ extensional) -/

theorem stageWymore_synthesizeExtensional_eq_synthesize {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    synthesizeExtensionalSpec Z = synthesizeSpec Z hOut :=
  stage4_synthesizeExtensional_eq_synthesize Z hOut

/-! ## Honest bi-implication tiers (TracePropertyLayer, HomWitness Tier C) -/

theorem stageWymore_traceProperty_separate_from_hom :
    FSMSatisfiesOutputTable PathologyExamples.fsmStay PathologyExamples.fsmStay ∧
      FSMSatisfiesOutputTable PathologyExamples.fsmStay PathologyExamples.fsmJump ∧
        (SystemToLTL.fsmTrace PathologyExamples.fsmJump 0 (fun _ => 0)).models
            (LTL.atom (.state 1)).F ∧
          ¬ (SystemToLTL.fsmTrace PathologyExamples.fsmStay 0 (fun _ => 0)).models
              (LTL.atom (.state 1)).F ∧
            ¬ FSMIsIdentityHomomorphicImage PathologyExamples.fsmStay PathologyExamples.fsmJump :=
  TracePropertyLayer.traceProperty_separate_from_hom

theorem stageWymore_fsm_decide_and_verify {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) (h : HomWitnessConstruction.checkFsmExtEqual F_spec F_impl = true) :
    FSMIsIdentityHomomorphicImage F_spec F_impl :=
  HomWitnessConstruction.fsm_decide_and_verify F_spec F_impl h

theorem stageWymore_verificationObligation_dynamics_gated {satisfies hom adequate : Prop}
    (hVE : VerificationEquivalence satisfies hom adequate) (hAdeq : adequate) :
    satisfies ↔ hom :=
  TracePropertyLayer.verificationObligation_dynamics_gated hVE hAdeq

theorem stageWymore_verificationObligation_full {satisfies hom adequate traceOk : Prop}
    (hVE : VerificationEquivalence satisfies hom adequate) (hAdeq : adequate)
    (hSat : satisfies) (hTrace : traceOk) :
    hom :=
  TracePropertyLayer.verificationObligation_full hVE hAdeq hSat hTrace

end WymoreCharacterization
