import Mbse.WymorePathologyExamples
import Mbse.PathologyExamples
import Mbse.PropertyFragmentSpec
import Mbse.WymorePropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.FSMProperties
import Mbse.Homomorphism
import Mbse.HomomorphismProperties
import Mbse.SystemToFormula

/-!
# Fragment pathology registry

Consolidated index mapping each `FragmentSpec` failure mode to a single machine-checked theorem.
Cited by the comparative report §5 and §9.
-/

namespace FragmentPathologyRegistry

open PropertyFragmentSpec PathologyExamples WymorePathologyExamples WymorePropertyFragment
  ExtensionalDynamicsFragment PropertyFragment.FSM PropertyFragment.General FSMProperties
  TemporalLogic SpecFromProperties HimsySynthesis FSM Homomorphism SystemToFormula
  Combinational CombinationalProperties HomomorphismProperties

/-- Failure modes blocking assertional Φ ↔ hom completeness outside pinned finite fragment. -/
inductive BlockerTag where
  | infiniteSZ
  | partialRZ
  | readoutOnly
  | eventuallyF
  | rawBranchingNZ
  | incompleteReadout
  | autonomousInputIncomplete
  | pinnedDynamicsIncomplete
  | foAssertionalCompleteness
  | executionFOHomCompleteness
  | barePhiUniqueZ

def blockerFragment : BlockerTag → FragmentSpec
  | .infiniteSZ => pinnedFiniteFragment
  | .partialRZ => pinnedFiniteFragment
  | .readoutOnly => readoutOnlyFragment
  | .eventuallyF => pinnedFragment
  | .rawBranchingNZ => partialOpenFragment
  | .incompleteReadout => partialOpenFragment
  | .autonomousInputIncomplete => pinnedFiniteFragment
  | .pinnedDynamicsIncomplete => pinnedFiniteFragment
  | .foAssertionalCompleteness => foAssertionalFragment
  | .executionFOHomCompleteness => foAssertionalFragment
  | .barePhiUniqueZ => readoutOnlyFragment

/-! ## One theorem per BLOCKED failure mode -/

/-- `Nat` (hence `counterSystem`) lacks finite clause enumeration for pinned tables. -/
theorem blocked_infiniteSZ :
    ¬ RequiresFiniteStateEnumeration Nat :=
  counterSystem_no_finite_dynamicsTable

theorem blocked_infiniteSZ_counterSystem :
    ¬ RequiresFiniteStateEnumeration Nat :=
  blocked_infiniteSZ

/-- Finite enumeration remains blocked; extensional fragment bypasses it for hom↔Φ. -/
theorem resolved_infiniteSZ_extensional :
    extensionalDynamicsFragment.finiteClauseEnumeration = false ∧
      SystemSatisfiesExtensional counterSystem counterSystem counterSystem_alwaysOutputs
        counterSystem_alwaysOutputs ∧
      SystemIsIdentityHomomorphicImageOpen counterSystem counterSystem
        counterSystem_alwaysOutputs counterSystem_alwaysOutputs :=
  ⟨extensionalDynamics_no_finite_enum, counterSystem_satisfies_own_extensional,
    extensional_satisfies_implies_hom counterSystem_alwaysOutputs counterSystem_alwaysOutputs
      counterSystem_satisfies_own_extensional⟩

/-- Cross-type extensional Φ ↔ hom (Def 4.3); witness `counterElab` → `counterSystem`. -/
theorem resolved_crossTypeExtensional :
    SystemSatisfiesExtensionalCross counterSystem counterElab ∧
      IsHomomorphicImage counterSystem counterElab :=
  ⟨counterElab_satisfies_extensional_cross, counterElab_hom_to_counterSystem⟩

/-- Gated extensional verification equivalence via `synthesizeExtensionalSpec` + `PhiAdequateExtensionalCross`. -/
theorem resolved_extensionalSynthesis :
    PhiAdequateExtensionalCross counterSystem ∧
      (SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ↔
        IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab) :=
  ⟨counterSystem_phi_adequate_cross, counterSystem_synthesized_cross_iff_hom⟩

/-- HIMSY constructive spec = homomorphic image (`counterSystem` = HIMSY(`counterElab`)). -/
theorem resolved_himsySynthesis :
    HimsySpecEqual counterSystem (synthesizeHimsySpec counterElab_witness) ∧
      IsHomomorphicImage counterSystem counterElab :=
  ⟨counterSystem_eq_himsy_counterElab, counterElab_hom_to_counterSystem⟩

/-- Witness-gated inverse table recovery on finite pinned fragment (`fsmStay`). -/
theorem resolved_inverseTableRecovery :
    IsRecoverableExtensionalTable
      (dynamicsTable fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay))
      fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay) :=
  fsmStay_recoverable_table

theorem blocked_incompleteReadout :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl ∧
        ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl :=
  ⟨partialOpen_dynamicsComplete, partial_satisfies_incompleteReadout_not_implies_extEqual⟩

theorem blocked_autonomousInputIncomplete :
    pinnedFiniteFragment.dynamicsComplete = true ∧
      SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ PartialExtEqual autoNoneSpec autoNoneImpl :=
  ⟨pinnedFragment_dynamicsComplete, pinnedDynamics_not_implies_extEqual_at_none⟩

theorem blocked_pinnedDynamicsIncomplete :
    pinnedFiniteFragment.dynamicsComplete = true ∧
      SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ SystemSatisfiesPartialDynamics autoNoneSpec autoNoneImpl :=
  ⟨pinnedFragment_dynamicsComplete, pinnedDynamics_not_implies_partialDynamics⟩

/-- Closed readout covered by readout-complete partial table (no `AlwaysOutputs` required). -/
theorem resolved_partialClosedReadout :
    ReadoutSpecComplete closedSystem ∧
      (SystemSatisfiesPartialDynamics closedSystem closedSystemImpl ↔
        PartialIsIdentityHomomorphicImage closedSystem closedSystemImpl) :=
  closedSystem_resolved

/-- Infinite partial readout: extensional partial ↔ hom without `AlwaysOutputs`. -/
theorem resolved_infinitePartialReadout :
    ¬ AlwaysOutputs counterClosedReadout ∧
      SystemSatisfiesExtensionalPartial counterClosedReadout counterClosedReadout ∧
        PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout := by
  rcases counterClosedReadout_resolved with ⟨hNot, _, hExt, hHom⟩
  exact ⟨hNot, hExt, hHom⟩

/-- Infinite assertional partial dynamics (predicate-indexed, no `Fintype`). -/
theorem resolved_infinitePartialDynamicsOpen :
    ¬ AlwaysOutputs counterClosedReadout ∧
      SystemSatisfiesPartialDynamicsOpen counterClosedReadout counterClosedReadout ∧
        PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  ⟨counterClosedReadout_not_alwaysOutputs, counterClosedReadout_satisfiesOpen_refl,
    (partialDynamicsOpen_iff_hom (readoutSpecCompleteOpen_of counterClosedReadout)).1
      counterClosedReadout_satisfiesOpen_refl⟩

/-- Predicate-indexed partial compile object on infinite `Nat`. -/
theorem resolved_predicateIndexedPartialCompile :
    SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
      (compileObservablesPartialOpen counterClosedReadout) ∧
      PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  ⟨counterClosedReadout_satisfiesCompiled_refl,
    (partialDynamicsCompiled_iff_hom (readoutSpecCompleteOpen_of counterClosedReadout)).1
      counterClosedReadout_satisfiesCompiled_refl⟩

theorem resolved_foAssertionalEncoding :
    SystemSatisfiesSpecAssertionalFOAt counterSystem counterSystem 0 (fun _ => some true) ∧
      ¬ SystemSatisfiesSpecAssertionalFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput :=
  ⟨counterSystem_satisfies_assertionalFO, foUnreachable_not_assertionalFO⟩

theorem resolved_partialAssertionalFO :
    SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout 0
      counterClosedReadoutInput ∧
      PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  ⟨counterClosedReadout_satisfiesPartialAssertionalFO_refl,
    (partialDynamicsOpen_iff_hom (readoutSpecCompleteOpen_of counterClosedReadout)).1
      counterClosedReadout_satisfiesOpen_refl⟩

theorem resolved_partialCompileUnification :
    SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
      (compileObservablesPartialOpen counterClosedReadout) ∧
      SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout 0
        counterClosedReadoutInput ∧
      (∀ s0 f,
        SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
          (compileObservablesPartialOpen counterClosedReadout) ↔
          SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout s0 f) :=
  ⟨counterClosedReadout_satisfiesCompiled_refl, counterClosedReadout_satisfiesPartialAssertionalFO_refl,
    fun s0 f =>
      compileObservablesPartial_schema (readoutSpecCompleteOpen_of counterClosedReadout) s0 f⟩

/-- Same-type surjective non-identity hom satisfies Cross, not pointwise Extensional. -/
theorem resolved_sameTypeSurjectiveHomSeparation :
    SameTypeHomomorphicImage swapSpecSys swapImplSys ∧
      SystemSatisfiesExtensionalCross swapSpecSys swapImplSys ∧
        IsNonIdentityWitness swapHomWitness ∧
          ¬ SystemSatisfiesExtensional swapSpecSys swapImplSys
            swapSpecSys_alwaysOutputs swapImplSys_alwaysOutputs :=
  sameType_surjectiveHom_separation

/-- Execution FO at a fixed witness does not imply extensional/hom agreement (`foUnreachable`). -/
theorem blocked_executionFOHomCompleteness :
    SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
      ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs :=
  ⟨fo_execution_not_complete_for_hom.1, fo_execution_not_complete_for_hom.2.1⟩

/-- Historical alias: use `blocked_executionFOHomCompleteness` (assertional FO is resolved separately). -/
theorem blocked_foAssertionalCompleteness :
    (foAssertionalFragment.finiteClauseEnumeration = false) ∧
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
        ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs) :=
  ⟨foAssertional_no_finite_enum, blocked_executionFOHomCompleteness⟩

theorem blocked_partialRZ :
    pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem :=
  closedSystem_excluded_from_pinned

theorem blocked_readoutOnly :
    readoutOnlyFragment.dynamicsComplete = false ∧
      (FSMSatisfiesOutputTable fsmJump fsmStay ∧
        FSMSatisfiesOutputTable fsmStay fsmJump ∧
        ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump) :=
  ⟨partial_readoutOnly_not_dynamicsComplete, example2_readout_table_incomplete⟩

/-- G-only dynamics fragment policy excludes `F`; trace-level witnesses differ on `F(q)`. -/
theorem blocked_eventuallyF :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      (∀ t, traceNoQ.holds t StutterAtom.p) ∧
      (∀ t, traceWithQ.holds t StutterAtom.p) ∧
      traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
      ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) := by
  rcases example3_F_obstruction with ⟨h1, h2, h3, h4⟩
  exact ⟨pinnedFragment_no_F, h1, h2, h3, h4⟩

/-- Same G-only output-table satisfaction; `F` state mission distinguishes traces. -/
theorem blocked_eventuallyF_wymore :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) :=
  PathologyExamples.blocked_eventuallyF_wymore

/-- Output-table Φ does not determine unique FSM (`fsmStay` vs `fsmJump`). -/
theorem blocked_barePhi_uniqueZ :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧
      ¬ FSMExtEqual fsmStay fsmJump :=
  ⟨rfl, fsmStay_jump_not_extEqual⟩

/-- Canonical combinational synthesis restores Stage-1 bi-implication (Example 1). -/
theorem resolved_canonicalDisjunction :
    PropertyFragment.CombSatisfiesFunction implSystem implTable ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  example1_refuted_for_canonical_spec

theorem blocked_rawBranchingNZ :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
        SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
          wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  refine ⟨partialOpen_dynamicsComplete, ?_⟩
  exact partial_readout_only_not_complete

end FragmentPathologyRegistry
