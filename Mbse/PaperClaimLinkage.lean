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
import Mbse.WymoreExercises
import Mbse.ComposedCaseStudy
import Mbse.MinskyKit
import Mbse.FibCaseStudy
import Mbse.PartialDynamicsHomFragment
import Mbse.Homomorphism

/-!
# Paper claim linkage

Derived `paperClaimStatus` theorems and audits that reference `BiImplicationFailures`
and `TracePropertyLayer` (kept separate from `BlockerAudit` to avoid import cycles).
-/

namespace BlockerAudit

open BiImplicationFailures PathologyExamples WymorePathologyExamples
  PropertyFragment.FSM FSMProperties PhiDecode ExtensionalDynamicsFragment
  ClassicalAssertionalBridge WymoreExercises ComposedCaseStudy MinskyKit FibCaseStudy
  PartialDynamicsHomFragment Homomorphism

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

/-- Paper case-study kit: Part 1 directs + Part 2 alternates satisfy the headline bi-implication. -/
theorem audit_caseStudyPlaybook :
    paperClaimStatus .caseStudyPlaybook = .safe ∧
      (SystemSatisfiesPartialDynamicsHom counterInc counterIncShift ↔
        IsHomomorphicImage counterInc counterIncShift) ∧
      (SystemSatisfiesPartialDynamicsHom counterDec counterDecElab ↔
        IsHomomorphicImage counterDec counterDecElab) ∧
      (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestElab ↔
        IsHomomorphicImage zeroTest zeroTestElab) ∧
      (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDual ↔
        IsHomomorphicImage zeroTest zeroTestDual) :=
  ⟨paperClaim_caseStudyPlaybook_safe, counterIncShift_iff_hom, counterDecElab_iff_hom,
    zeroTestElab_iff_hom, zeroTestDual_iff_hom⟩

/-- Fibonacci composition: Φ↔hom, shelf NZ/RZ wiring, and `Nat.fib` functional correctness. -/
theorem audit_fibCaseStudy :
    (SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl ↔
      IsHomomorphicImage fibSpec fibAwkwardImpl) ∧
    (∀ n, fibSpecOut (fibSpecNext (fibRun n) .step) = Nat.fib n) ∧
    (∀ s n, (fibAwkwardNext s (.load n)).a = kitAssign 0) :=
  ⟨fibAwkward_iff_hom, fibSpec_computes_fib, fun s n =>
    (fibAwkward_uses_shelf_components).1 s n⟩

/-- Gallery cascade (not the paper spine): composed shift→counter buildable implements $Z_{12}$. -/
theorem audit_cascadeCaseStudy :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl ↔
      IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  cascadeAwkward_iff_hom

/-- Dual-port pattern select remains mechanized in the gallery. -/
theorem audit_dualPortMechanized :
    paperClaimStatus .dualPortMechanized = .safe ∧
      (SystemSatisfiesPartialDynamicsHom dualPatternSpec dualPatternElab ↔
        IsHomomorphicImage dualPatternSpec dualPatternElab) :=
  ⟨paperClaim_dualPort_safe, dualPatternElab_iff_hom⟩

/-- Restricted `F`/`U` inside dynamics-encoding Φ remains an open exploration. -/
theorem audit_restrictedFU_open :
    paperClaimStatus .restrictedFUInDynamicsEncoding = .openQuestion :=
  paperClaim_restrictedFU_open

end BlockerAudit
