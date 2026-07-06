import Mbse.BiImplicationFailures
import Mbse.WymorePathologyExamples
import Mbse.PathologyExamples
import Mbse.ExtensionalDynamicsFragment
import Mbse.WymorePropertyFragment
import Mbse.PropertySemantics
import Mbse.FSMProperties
import Mbse.PhiDecode

/-!
# PhiAdequacy exclusions

Pathology witnesses excluded from gated verification templates: either they fail
`PhiAdequate*` preconditions, or they refute `VerificationEquivalence` under the
correct gate when paired with a wrong satisfaction predicate.
-/

namespace PhiAdequacyExclusions

open BiImplicationFailures WymorePathologyExamples PathologyExamples
  ExtensionalDynamicsFragment WymorePropertyFragment PropertySemantics
  PropertyFragment.FSM FSMProperties PropertyFragment.General PropertyFragmentSpec
  FragmentPathologyRegistry PhiDecode

/-! ## Gated verification refutations (wrong predicate + adequate reference) -/

theorem silentReadout_wrongPredicate_fails_gatedVerification :
    ¬ VerificationEquivalence
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
      (PartialExtEqual silentReadoutSpec spuriousOutputImpl)
      (PhiAdequatePartialOpen silentReadoutSpec) := by
  intro hVE
  have hAdeq := (partialDynamicsAdequate_iff silentReadoutSpec).mp (partial_adequate silentReadoutSpec)
  have hEq := hVE hAdeq
  exact biImpFails_incompleteReadout.2 (hEq.mp biImpFails_incompleteReadout.1)

theorem autoNone_pinnedDynamics_fails_gatedPartialVerification :
    ¬ VerificationEquivalence
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs)
      (PartialExtEqual autoNoneSpec autoNoneImpl)
      (PhiAdequatePartialOpen autoNoneSpec) := by
  intro hVE
  have hAdeq := (partialDynamicsAdequate_iff autoNoneSpec).mp (partial_adequate autoNoneSpec)
  have hEq := hVE hAdeq
  exact biImpFails_autonomousNone.2 (hEq.mp biImpFails_autonomousNone.1)

theorem foUnreachable_executionFO_fails_gatedExtensionalVerification :
    ¬ VerificationEquivalence
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput)
      (SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs)
      (PhiAdequateExtensionalOpen foUnreachableSpec foUnreachableSpec_alwaysOutputs) := by
  intro hVE
  have hAdeq := extensional_phi_adequate_open foUnreachableSpec foUnreachableSpec_alwaysOutputs
  have hEq := hVE hAdeq
  exact biImpFails_executionFO.2 (hEq.mp biImpFails_executionFO.1)

/-! ## Output-table vs dynamics-table mismatch -/

theorem fsmStayJump_not_sameDynamicsPhi :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧
      fsmDynamicsTable fsmStay ≠ fsmDynamicsTable fsmJump := by
  refine ⟨rfl, ?_⟩
  intro h
  have hExt := PhiDecode.decodeFsm_unique_up_to_ext fsmStay fsmJump h
  exact fsmStay_jump_not_extEqual hExt

/-! ## Tier side-condition exclusions -/

theorem closedSystem_not_pinned_applicable :
    ¬ AlwaysOutputs closedSystem :=
  blocked_partialRZ.2

/-! ## Link to bi-implication failures -/

theorem phiAdequacy_excluded_implies_biImp_fails :
    SatisfactionWithoutHom
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
      (PartialExtEqual silentReadoutSpec spuriousOutputImpl) →
      ¬ VerificationEquivalence
        (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
        (PartialExtEqual silentReadoutSpec spuriousOutputImpl)
        True :=
  fun h => verificationEquivalence_fails_of_satisfaction_without_hom h trivial

theorem silentReadout_biImp_fails :
    SatisfactionWithoutHom
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
      (PartialExtEqual silentReadoutSpec spuriousOutputImpl) :=
  biImpFails_incompleteReadout

theorem autoNone_biImp_fails :
    SatisfactionWithoutHom
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs)
      (PartialExtEqual autoNoneSpec autoNoneImpl) :=
  biImpFails_autonomousNone

theorem foUnreachable_biImp_fails :
    SatisfactionWithoutHom
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput)
      (SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs) :=
  biImpFails_executionFO

end PhiAdequacyExclusions
