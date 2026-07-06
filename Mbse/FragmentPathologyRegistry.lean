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
  ExtensionalDynamicsFragment PropertyFragment.FSM FSMProperties TemporalLogic

/-- Failure modes blocking assertional Φ ↔ hom completeness outside pinned finite tier. -/
inductive BlockerTag where
  | infiniteSZ
  | partialRZ
  | readoutOnly
  | eventuallyF
  | rawBranchingNZ

def blockerFragment : BlockerTag → FragmentSpec
  | .infiniteSZ => pinnedFiniteFragment
  | .partialRZ => pinnedFiniteFragment
  | .readoutOnly => readoutOnlyFragment
  | .eventuallyF => pinnedFragment
  | .rawBranchingNZ => partialOpenFragment

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
