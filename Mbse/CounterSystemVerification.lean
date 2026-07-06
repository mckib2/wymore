import Mbse.WymoreCharacterization
import Mbse.ExtensionalDynamicsFragment
import Mbse.HimsySynthesis
import Mbse.FragmentPathologyRegistry
import Mbse.WymorePathologyExamples
import Mbse.PropertySemantics
import Mbse.SpecFromProperties

/-!
# Counter system: gated verification aggregator

Single citeable `VerificationEquivalence` for the infinite-state `counterSystem` example,
plus a playbook bundling adequacy, blockers, cross hom, and HIMSY synthesis.
-/

namespace CounterSystemVerification

open WymoreCharacterization ExtensionalDynamicsFragment HimsySynthesis SpecFromProperties
  FragmentPathologyRegistry WymorePathologyExamples PropertySemantics Homomorphism
  WymorePropertyFragment

theorem counterSystem_gated_verification :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab)
      (IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab)
      (PhiAdequateExtensionalCross counterSystem) :=
  stageWymore_extensional_verification_equivalence

theorem counterSystem_not_pinned_finite :
    ¬ RequiresFiniteStateEnumeration Nat :=
  blocked_infiniteSZ

theorem counterSystem_verification_playbook :
    PhiAdequateExtensionalCross counterSystem ∧
      (¬ RequiresFiniteStateEnumeration Nat) ∧
      SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ∧
        IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab ∧
          HimsySpecEqual counterSystem (synthesizeHimsySpec counterElab_witness) := by
  refine ⟨counterSystem_phi_adequate_cross, blocked_infiniteSZ, ?_, ?_, counterSystem_eq_himsy_counterElab⟩
  · exact counterElab_satisfies_extensional_cross
  · exact counterElab_synthesized_hom

end CounterSystemVerification
