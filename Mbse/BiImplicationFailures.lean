import Mbse.BlockerAudit
import Mbse.FragmentPathologyRegistry
import Mbse.HomSoundness
import Mbse.PropertySemantics
import Mbse.WymorePathologyExamples
import Mbse.WymorePropertyFragment
import Mbse.SystemToLTL

/-!
# Bi-implication failure witnesses

Catalog of cases where `VerificationEquivalence` fails or the wrong satisfaction
predicate breaks `satisfies ↔ hom`. Each impossibility `BlockerTag` maps to a
`biImpFails_*` theorem packaging the underlying blocker.
-/

namespace BiImplicationFailures

open PropertySemantics FragmentPathologyRegistry BlockerAudit PropertyFragmentSpec
  PathologyExamples WymorePathologyExamples PropertyFragment.FSM FSMProperties
  HomomorphismProperties ExtensionalDynamicsFragment WymorePropertyFragment
  PropertyFragment.General TemporalLogic

variable {SZ IZ OZ : Type}

/-! ## Helper definitions -/

/-- Satisfaction holds but homomorphic-image does not (bi-implication fails →). -/
def SatisfactionWithoutHom (satisfies hasHom : Prop) : Prop :=
  satisfies ∧ ¬ hasHom

/-- Ungated verification fails when adequacy is true but satisfaction does not imply hom. -/
theorem verificationEquivalence_fails_of_satisfaction_without_hom
    {satisfies hasHom adequate : Prop}
    (h : SatisfactionWithoutHom satisfies hasHom) (hAdeq : adequate) :
    ¬ VerificationEquivalence satisfies hasHom adequate := by
  intro hVE
  have := hVE hAdeq
  exact h.2 (this.mp h.1)

/-! ## Per-blocker failure theorems -/

theorem biImpFails_readoutOnly :
    SatisfactionWithoutHom
      (FSMSatisfiesOutputTable fsmStay fsmJump)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump) := by
  rcases blocked_readoutOnly with ⟨_, ⟨_, hSat, hHom⟩⟩
  exact ⟨hSat, hHom⟩

theorem biImpFails_barePhi :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧
      ¬ FSMExtEqual fsmStay fsmJump :=
  blocked_barePhi_uniqueZ

theorem biImpFails_executionFO :
    SatisfactionWithoutHom
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput)
      (SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs) := by
  rcases blocked_executionFOHomCompleteness with ⟨hFO, hExt⟩
  exact ⟨hFO, hExt⟩

theorem biImpFails_autonomousNone :
    SatisfactionWithoutHom
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs)
      (PartialExtEqual autoNoneSpec autoNoneImpl) := by
  rcases blocked_autonomousInputIncomplete with ⟨_, h⟩
  exact h

theorem biImpFails_pinnedDynamics :
    SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
      autoNoneImpl_alwaysOutputs ∧
      ¬ SystemSatisfiesPartialDynamics autoNoneSpec autoNoneImpl := by
  exact blocked_pinnedDynamicsIncomplete.2

theorem biImpFails_incompleteReadout :
    SatisfactionWithoutHom
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
      (PartialExtEqual silentReadoutSpec spuriousOutputImpl) := by
  rcases blocked_incompleteReadout with ⟨_, h⟩
  exact h

theorem biImpFails_rawBranchingNZ :
    SatisfactionWithoutHom
      (SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump)
      (PartialExtEqual wymoreStay wymoreJump) := by
  rcases blocked_rawBranchingNZ with ⟨_, _, hSat, hNZ⟩
  refine ⟨hSat, ?_⟩
  intro hExt
  exact hNZ.symm (hExt.2 0 (some 0))

/-! ## Design exclusions (tier inapplicability) -/

theorem biImpFails_infiniteSZ_excludes_pinned :
    ¬ RequiresFiniteStateEnumeration Nat :=
  blocked_infiniteSZ

theorem biImpFails_partialRZ_excludes_pinned :
    pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem :=
  blocked_partialRZ

/-! ## Semantic limit (trace properties vs dynamics encoding) -/

theorem biImpFails_eventuallyF_tracePropertyLimit :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.atom (.state 1)).F ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.atom (.state 1)).F :=
  FragmentPathologyRegistry.blocked_eventuallyF_wymore

/-! ## VerificationEquivalence corollaries (wrong template + trivial adequacy) -/

theorem biImpFails_readoutOnly_verificationEquivalence :
    ¬ VerificationEquivalence
      (FSMSatisfiesOutputTable fsmStay fsmJump)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump)
      True :=
  verificationEquivalence_fails_of_satisfaction_without_hom biImpFails_readoutOnly trivial

theorem biImpFails_incompleteReadout_verificationEquivalence :
    ¬ VerificationEquivalence
      (SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl)
      (PartialExtEqual silentReadoutSpec spuriousOutputImpl)
      True :=
  verificationEquivalence_fails_of_satisfaction_without_hom biImpFails_incompleteReadout trivial

theorem biImpFails_autonomousNone_verificationEquivalence :
    ¬ VerificationEquivalence
      (SystemSatisfiesDynamics autoNoneSpec autoNoneImpl autoNoneSpec_alwaysOutputs
        autoNoneImpl_alwaysOutputs)
      (PartialExtEqual autoNoneSpec autoNoneImpl)
      True :=
  verificationEquivalence_fails_of_satisfaction_without_hom biImpFails_autonomousNone trivial

end BiImplicationFailures
