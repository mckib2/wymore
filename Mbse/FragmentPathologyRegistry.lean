import Mbse.WymorePathologyExamples
import Mbse.PathologyExamples
import Mbse.PropertyFragmentSpec
import Mbse.WymorePropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.FSMProperties

/-!
# Fragment pathology registry

Consolidated index mapping each `FragmentSpec` tier failure mode to a single machine-checked theorem.
Cited by the comparative report §5 and §9.
-/

namespace FragmentPathologyRegistry

open PropertyFragmentSpec PathologyExamples WymorePathologyExamples WymorePropertyFragment
  ExtensionalDynamicsFragment PropertyFragment.FSM PropertyFragment.General FSMProperties
  TemporalLogic SpecFromProperties HimsySynthesis FSM

/-- Failure modes blocking assertional Φ ↔ hom completeness outside pinned finite tier. -/
inductive BlockerTag where
  | infiniteSZ
  | partialRZ
  | readoutOnly
  | eventuallyF
  | rawBranchingNZ
  | partialSilentReadout
  | foAssertionalCompleteness

def blockerFragment : BlockerTag → FragmentSpec
  | .infiniteSZ => pinnedFiniteFragment
  | .partialRZ => pinnedFiniteFragment
  | .readoutOnly => readoutOnlyFragment
  | .eventuallyF => pinnedFragment
  | .rawBranchingNZ => partialOpenFragment
  | .partialSilentReadout => partialOpenFragment
  | .foAssertionalCompleteness => foAssertionalFragment

/-! ## One theorem per BLOCKED failure mode -/

theorem blocked_infiniteSZ :
    ¬ RequiresFiniteStateEnumeration Nat :=
  counterSystem_no_finite_dynamicsTable

/-- Finite enumeration remains blocked; extensional tier bypasses it for hom↔Φ. -/
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

/-- Witness-gated inverse table recovery on finite pinned tier (`fsmStay`). -/
theorem resolved_inverseTableRecovery :
    IsRecoverableExtensionalTable
      (dynamicsTable fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay))
      fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay) :=
  fsmStay_recoverable_table

theorem blocked_partialSilentReadout :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialDynamicsSilentLegacy silentReadoutSpec spuriousOutputImpl ∧
        ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl :=
  ⟨partialOpen_dynamicsComplete, partial_satisfies_silentLegacy_not_implies_extEqual⟩

/-- Closed readout covered by readout-complete partial table (no `AlwaysOutputs` required). -/
theorem resolved_partialClosedReadout :
    ReadoutSpecComplete closedShapeSpec ∧
      (SystemSatisfiesPartialDynamics closedShapeSpec closedShapeImpl ↔
        PartialIsIdentityHomomorphicImage closedShapeSpec closedShapeImpl) :=
  closedShapeSpec_resolved

theorem blocked_foAssertionalCompleteness :
    foAssertionalFragment.finiteClauseEnumeration = false ∧
      SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
        ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs :=
  ⟨foAssertional_no_finite_enum, fo_execution_not_complete_for_hom.1,
    fo_execution_not_complete_for_hom.2.1⟩

theorem blocked_partialRZ :
    pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem :=
  closedSystem_excluded_from_pinned

theorem blocked_readoutOnly :
    readoutOnlyFragment.dynamicsComplete = false ∧
      (FSMSatisfiesOutputTable fsmJump fsmStay ∧
        FSMSatisfiesOutputTable fsmStay fsmJump ∧
        ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump) :=
  ⟨partial_readoutOnly_not_dynamicsComplete, example2_readout_table_incomplete⟩

theorem blocked_eventuallyF :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      (∀ t, traceNoQ.holds t StutterAtom.p) ∧
      (∀ t, traceWithQ.holds t StutterAtom.p) ∧
      traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
      ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) := by
  rcases example3_F_obstruction with ⟨h1, h2, h3, h4⟩
  exact ⟨pinnedFragment_no_F, h1, h2, h3, h4⟩

theorem blocked_rawBranchingNZ :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
        SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
          wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  refine ⟨partialOpen_dynamicsComplete, ?_⟩
  exact partial_readout_only_not_complete

end FragmentPathologyRegistry
