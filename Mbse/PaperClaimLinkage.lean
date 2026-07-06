import Mbse.BlockerAudit
import Mbse.BiImplicationFailures
import Mbse.TracePropertyLayer
import Mbse.PathologyExamples
import Mbse.WymorePathologyExamples
import Mbse.FSMProperties
import Mbse.PhiDecode
import Mbse.WymorePropertyFragment
import Mbse.ExtensionalDynamicsFragment

/-!
# Paper claim linkage

Derived `paperClaimStatus` theorems and audits that reference `BiImplicationFailures`
and `TracePropertyLayer` (kept separate from `BlockerAudit` to avoid import cycles).
-/

namespace BlockerAudit

open BiImplicationFailures PathologyExamples WymorePathologyExamples
  PropertyFragment.FSM FSMProperties PhiDecode ExtensionalDynamicsFragment

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

end BlockerAudit
