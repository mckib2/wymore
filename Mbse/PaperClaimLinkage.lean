import Mbse.BlockerAudit
import Mbse.BiImplicationFailures
import Mbse.TracePropertyLayer
import Mbse.PathologyExamples
import Mbse.WymorePathologyExamples
import Mbse.FSMProperties
import Mbse.PhiDecode
import Mbse.WymorePropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.ClassicalAssertionalBridge

/-!
# Paper claim linkage

Derived `paperClaimStatus` theorems and audits that reference `BiImplicationFailures`
and `TracePropertyLayer` (kept separate from `BlockerAudit` to avoid import cycles).
-/

namespace BlockerAudit

open BiImplicationFailures PathologyExamples WymorePathologyExamples
  PropertyFragment.FSM FSMProperties PhiDecode ExtensionalDynamicsFragment
  ClassicalAssertionalBridge

theorem paperClaim_outputTableOnly_blocked
    (_h : SatisfactionWithoutHom (FSMSatisfiesOutputTable fsmStay fsmJump)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump)) :
    paperClaimStatus .outputTableOnlyPhi = .blocked :=
  rfl

theorem paperClaim_traceProperty_qualified :
    TracePropertyLayer.tracePropertySeparateProp →
      paperClaimStatus .fInTracePropertyLayer = .qualified :=
  fun _ => rfl

theorem audit_tracePropertySeparate :
    TracePropertyLayer.tracePropertySeparateProp ∧
      paperClaimStatus .fInTracePropertyLayer = .qualified := by
  constructor
  · exact TracePropertyLayer.traceProperty_separate_from_hom
  · rfl

theorem paperClaim_barePhi_blocked_derived
    (_h : fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump) :
    paperClaimStatus .barePhiUniqueSpec = .blocked :=
  rfl

theorem paperClaim_executionFO_blocked_derived
    (_h : SatisfactionWithoutHom
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput)
      (SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs)) :
    paperClaimStatus .executionFOSubstitutesHom = .blocked :=
  rfl

/-- Fragment-qualified hom projection equivalence is proved (headline dynamics-encoding bridge). -/
theorem audit_homProjection_equivalence :
    paperClaimStatus .homProjectionEquivalence = .safe ∧
      (∀ {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
        (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2),
        ClassicalFCMembership Z_spec Z_impl ↔
          AssertionalFCHomMembership Z_spec Z_impl) := by
  refine ⟨paperClaim_homProjection_safe, ?_⟩
  intro _ _ _ _ _ _ Z_spec Z_impl
  exact qualified_equivalence_homProjection Z_spec Z_impl

end BlockerAudit
