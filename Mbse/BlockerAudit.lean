import Mbse.FragmentPathologyRegistry
import Mbse.PropertyFragmentSpec
import Mbse.FSMProperties
import Mbse.ExtensionalDynamicsFragment

/-!
# Blocker audit registry

Machine-checked classification of each `BlockerTag`: literal theorem strength,
workaround status, and paper-claim impact. See also
[`FragmentPathologyRegistry`](FragmentPathologyRegistry.lean) for the underlying
counterexamples.

**Strength taxonomy**

* `impossibility` — concrete Φ-satisfaction vs hom (or extensional) mismatch
* `designExclusion` — system class excluded by fragment side condition (not Φ→hom failure)
* `semanticLimit` — property class cannot distinguish witnesses (often trace-level)
* `namingOnly` — theorem true but historical name mislabels the obstruction
-/

namespace BlockerAudit

variable {SZ IZ OZ : Type} [Nonempty IZ]

open FragmentPathologyRegistry PropertyFragmentSpec PathologyExamples
  WymorePathologyExamples WymorePropertyFragment FSMProperties PropertyFragment.FSM
  PropertyFragment.General ExtensionalDynamicsFragment TemporalLogic

/-- How a blocker relates to the underlying theorem. -/
inductive BlockerStrength where
  | impossibility
  | designExclusion
  | semanticLimit
  | namingOnly

/-- Paper-facing claims whose safety is governed by blockers/resolutions. -/
inductive PaperClaimTag where
  | executionEncoding
  | assertionalFC
  | phiHomAdequate
  | infiniteState
  | propositionalLTLCorollary
  | fInMissionPhi
  | fInTracePropertyLayer
  | executionFOSubstitutesHom
  | outputTableOnlyPhi
  | pinnedAutonomousNone
  | barePhiUniqueSpec
  | assertionalFOWithoutBridge
  | homProjectionEquivalence
  | classicalAssertionalEquivalence
  | caseStudyPlaybook
  | dualPortMechanized
  | restrictedFUInDynamicsEncoding

/-- Workaround tags paired with blockers. -/
inductive ResolvedTag where
  | infiniteSZExtensional
  | partialClosedReadout
  | dynamicsCompleteTable
  | assertionalFOBridge
  | canonicalDisjunction
  | missionPhiSeparate
  | tracePropertySeparate

structure BlockerAuditInfo where
  tag : BlockerTag
  strength : BlockerStrength
  workaround : Option ResolvedTag
  blocksClaims : List PaperClaimTag

def blockerStrength : BlockerTag → BlockerStrength
  | .infiniteSZ => .designExclusion
  | .partialRZ => .designExclusion
  | .readoutOnly => .impossibility
  | .eventuallyF => .semanticLimit
  | .rawBranchingNZ => .impossibility
  | .incompleteReadout => .impossibility
  | .autonomousInputIncomplete => .impossibility
  | .pinnedDynamicsIncomplete => .impossibility
  | .foAssertionalCompleteness => .impossibility
  | .executionFOHomCompleteness => .namingOnly
  | .barePhiUniqueZ => .impossibility

def blockerWorkaround : BlockerTag → Option ResolvedTag
  | .infiniteSZ => some .infiniteSZExtensional
  | .partialRZ => some .partialClosedReadout
  | .readoutOnly => some .dynamicsCompleteTable
  | .eventuallyF => some .tracePropertySeparate
  | .rawBranchingNZ => some .dynamicsCompleteTable
  | .incompleteReadout => some .partialClosedReadout
  | .autonomousInputIncomplete => some .dynamicsCompleteTable
  | .pinnedDynamicsIncomplete => some .dynamicsCompleteTable
  | .foAssertionalCompleteness => some .assertionalFOBridge
  | .executionFOHomCompleteness => some .assertionalFOBridge
  | .barePhiUniqueZ => none

def blockerBlocksClaims : BlockerTag → List PaperClaimTag
  | .infiniteSZ => [.propositionalLTLCorollary]
  | .partialRZ => []
  | .readoutOnly => [.outputTableOnlyPhi]
  | .eventuallyF => [.fInMissionPhi, .fInTracePropertyLayer]
  | .rawBranchingNZ => [.outputTableOnlyPhi]
  | .incompleteReadout => []
  | .autonomousInputIncomplete => [.pinnedAutonomousNone]
  | .pinnedDynamicsIncomplete => [.pinnedAutonomousNone]
  | .foAssertionalCompleteness => [.executionFOSubstitutesHom, .assertionalFOWithoutBridge]
  | .executionFOHomCompleteness => [.executionFOSubstitutesHom]
  | .barePhiUniqueZ => [.barePhiUniqueSpec]

def blockerAuditInfo (tag : BlockerTag) : BlockerAuditInfo where
  tag := tag
  strength := blockerStrength tag
  workaround := blockerWorkaround tag
  blocksClaims := blockerBlocksClaims tag

/-! ## Per-tag audit theorems (literal content + classification) -/

theorem audit_infiniteSZ :
    ((blockerAuditInfo .infiniteSZ).strength = .designExclusion) ∧
      (¬ RequiresFiniteStateEnumeration Nat) :=
  ⟨rfl, blocked_infiniteSZ⟩

theorem audit_partialRZ :
    ((blockerAuditInfo .partialRZ).strength = .designExclusion) ∧
      (pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem) :=
  ⟨rfl, blocked_partialRZ⟩

theorem audit_readoutOnly :
    ((blockerAuditInfo .readoutOnly).strength = .impossibility) ∧
      (FSMSatisfiesOutputTable fsmJump fsmStay ∧
        FSMSatisfiesOutputTable fsmStay fsmJump ∧
          ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump) := by
  rcases blocked_readoutOnly with ⟨_, h⟩
  exact ⟨rfl, h⟩

theorem audit_eventuallyF :
    ((blockerAuditInfo .eventuallyF).strength = .semanticLimit) ∧
      (pinnedFragment.eventuallyPolicy = .excluded ∧
        traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
          ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q))) := by
  rcases blocked_eventuallyF with ⟨hPol, _, _, hY, hN⟩
  exact ⟨rfl, ⟨hPol, hY, hN⟩⟩

theorem audit_rawBranchingNZ :
    ((blockerAuditInfo .rawBranchingNZ).strength = .impossibility) ∧
      (wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0)) := by
  rcases blocked_rawBranchingNZ with ⟨_, h⟩
  exact ⟨rfl, h.2.2⟩

theorem audit_incompleteReadout :
    ((blockerAuditInfo .incompleteReadout).strength = .impossibility) ∧
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl ∧
        ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl) := by
  rcases blocked_incompleteReadout with ⟨_, h⟩
  exact ⟨rfl, h⟩

theorem audit_autonomousInputIncomplete :
    ((blockerAuditInfo .autonomousInputIncomplete).strength = .impossibility) ∧
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ PartialExtEqual autoNoneSpec autoNoneImpl) := by
  rcases blocked_autonomousInputIncomplete with ⟨_, h⟩
  exact ⟨rfl, h⟩

theorem audit_pinnedDynamicsIncomplete :
    ((blockerAuditInfo .pinnedDynamicsIncomplete).strength = .impossibility) ∧
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs ∧
        ¬ SystemSatisfiesPartialDynamics autoNoneSpec autoNoneImpl) := by
  rcases blocked_pinnedDynamicsIncomplete with ⟨_, h⟩
  exact ⟨rfl, h⟩

theorem audit_executionFOHomCompleteness :
    ((blockerAuditInfo .executionFOHomCompleteness).strength = .namingOnly) ∧
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
        ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs) :=
  ⟨rfl, fo_execution_not_complete_for_hom.1, fo_execution_not_complete_for_hom.2.1⟩

theorem audit_foAssertionalCompleteness :
    ((blockerAuditInfo .foAssertionalCompleteness).strength = .impossibility) ∧
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
        ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs) := by
  rcases blocked_foAssertionalCompleteness with ⟨hEnum, hFO⟩
  exact ⟨rfl, hFO⟩

theorem audit_barePhiUniqueZ :
    ((blockerAuditInfo .barePhiUniqueZ).strength = .impossibility) ∧
      (fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump) :=
  ⟨rfl, blocked_barePhi_uniqueZ⟩

/-! ## Paper claim safety map -/

inductive PaperClaimStatus where
  | safe
  | qualified
  | blocked
  | openQuestion

def paperClaimStatus : PaperClaimTag → PaperClaimStatus
  | .executionEncoding => .safe
  | .assertionalFC => .safe
  | .phiHomAdequate => .safe
  | .infiniteState => .safe
  | .propositionalLTLCorollary => .qualified
  | .fInMissionPhi => .qualified
  | .fInTracePropertyLayer => .qualified
  | .executionFOSubstitutesHom => .blocked
  | .outputTableOnlyPhi => .blocked
  | .pinnedAutonomousNone => .blocked
  | .barePhiUniqueSpec => .blocked
  | .assertionalFOWithoutBridge => .blocked
  | .homProjectionEquivalence => .safe
  | .classicalAssertionalEquivalence => .openQuestion
  | .caseStudyPlaybook => .safe
  | .dualPortMechanized => .safe
  | .restrictedFUInDynamicsEncoding => .openQuestion

theorem paperClaim_executionEncoding_safe :
    paperClaimStatus .executionEncoding = .safe := rfl

theorem paperClaim_phiHomAdequate_safe :
    paperClaimStatus .phiHomAdequate = .safe := rfl

theorem paperClaim_executionFO_blocked :
    paperClaimStatus .executionFOSubstitutesHom = .blocked := rfl

theorem paperClaim_barePhi_blocked :
    paperClaimStatus .barePhiUniqueSpec = .blocked := rfl

theorem paperClaim_homProjection_safe :
    paperClaimStatus .homProjectionEquivalence = .safe := rfl

/-- Map impossibility / semantic-limit blockers to `BiImplicationFailures` theorem names. -/
def biImpFailsTheorem : BlockerTag → Option String
  | .readoutOnly => some "biImpFails_readoutOnly"
  | .barePhiUniqueZ => some "biImpFails_barePhi"
  | .executionFOHomCompleteness => some "biImpFails_executionFO"
  | .autonomousInputIncomplete => some "biImpFails_autonomousNone"
  | .pinnedDynamicsIncomplete => some "biImpFails_pinnedDynamics"
  | .incompleteReadout => some "biImpFails_incompleteReadout"
  | .rawBranchingNZ => some "biImpFails_rawBranchingNZ"
  | .eventuallyF => some "biImpFails_eventuallyF_tracePropertyLimit"
  | .infiniteSZ => some "biImpFails_infiniteSZ_excludes_pinned"
  | .partialRZ => some "biImpFails_partialRZ_excludes_pinned"
  | .foAssertionalCompleteness => some "biImpFails_executionFO"

/-- Map paper claims to linking theorem names (when not a bare `rfl`). -/
def paperClaimTheorem : PaperClaimTag → Option String
  | .outputTableOnlyPhi => some "paperClaim_outputTableOnly_blocked"
  | .fInTracePropertyLayer => some "paperClaim_traceProperty_qualified"
  | .executionFOSubstitutesHom => some "paperClaim_executionFO_blocked"
  | .barePhiUniqueSpec => some "paperClaim_barePhi_blocked"
  | .homProjectionEquivalence => some "audit_homProjection_equivalence"
  | .classicalAssertionalEquivalence => some "audit_classicalAssertional_open"
  | .caseStudyPlaybook => some "audit_caseStudyPlaybook"
  | .dualPortMechanized => some "audit_dualPortMechanized"
  | .restrictedFUInDynamicsEncoding => some "audit_restrictedFU_open"
  | _ => none

theorem paperClaim_classicalEquiv_open :
    paperClaimStatus .classicalAssertionalEquivalence = .openQuestion := rfl

theorem paperClaim_caseStudyPlaybook_safe :
    paperClaimStatus .caseStudyPlaybook = .safe := rfl

theorem paperClaim_dualPort_safe :
    paperClaimStatus .dualPortMechanized = .safe := rfl

theorem paperClaim_restrictedFU_open :
    paperClaimStatus .restrictedFUInDynamicsEncoding = .openQuestion := rfl

end BlockerAudit
