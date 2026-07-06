import Mbse.BlockerAudit
import Mbse.BiImplicationFailures
import Mbse.FragmentPathologyRegistry
import Mbse.HomSoundness
import Mbse.PropertySemantics
import Mbse.ExtensionalDynamicsFragment
import Mbse.WymoreCharacterization
import Mbse.TracePropertyLayer
import Mbse.PathologyExamples
import Mbse.WymorePathologyExamples
import Mbse.SpecFromProperties
import Mbse.WymorePropertyFragment
import Mbse.PartialDynamicsHomFragment
import Mbse.GeneralProperties
import Mbse.GeneralPropertyFragment

/-!
# Classical vs assertional FC bridge (scoping)

Documents partial bridges already in the library and blockers to naive global
`FC_constructive = FC_assertional` equivalence. Full cotyledon-level set equality
without side conditions remains open.

**Headline (proved):** fragment-qualified hom projection equivalence
(`qualified_equivalence_homProjection`).

**Legacy:** pinned finite `PinnedAssertionalFCMembership` retains the old decidable
projection for tooling; it is not the headline assertional FC definition.
-/

namespace ClassicalAssertionalBridge

open BlockerAudit BiImplicationFailures FragmentPathologyRegistry PropertySemantics
  HomSoundness ExtensionalDynamicsFragment WymoreCharacterization TracePropertyLayer
  PathologyExamples WymorePathologyExamples SpecFromProperties WymorePropertyFragment
  PartialDynamicsHomFragment GeneralProperties PropertyFragment.General
  PropertyFragment.FSM FSMProperties Homomorphism

variable {SZ IZ OZ SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}

/-! ## Membership predicates (documentation) -/

/-- Classical FC membership: implementation is a Wymore Def.~4.3 homomorphic image of
reference `Z_spec` (cross-type allowed). -/
def ClassicalFCMembership
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  IsHomomorphicImage Z_spec Z_impl

/-- Dynamics-encoding bridge FC membership (headline hom projection tier). -/
def AssertionalFCHomMembership
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  SystemSatisfiesPartialDynamicsHom Z_spec Z_impl

/-- Shared fixed-table bridge FC membership (same `(S,I,O)`, literal impl-state atoms). -/
def AssertionalFCPartialOpenMembership [DecidableEq IZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Prop :=
  SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl

/-- Legacy pinned finite assertional membership (decidable projection; requires
`AlwaysOutputs` and finite enumeration). Not the headline definition. -/
def PinnedAssertionalFCMembership [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hZ : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  SystemSatisfiesDynamics Z_spec Z_impl hZ hImpl

/-! ## Negative witness proposition aliases (for audit conjuncts) -/

abbrev blockedReadoutOnlyProp :=
  SatisfactionWithoutHom (FSMSatisfiesOutputTable fsmStay fsmJump)
    (FSMIsIdentityHomomorphicImage fsmStay fsmJump)

abbrev blockedBarePhiProp :=
  fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump

abbrev blockedExecutionFOProp :=
  SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
    ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
      foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs ∧
    ¬ SystemIsIdentityHomomorphicImageOpen foUnreachableSpec foUnreachableImpl
      foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs

/-! ## Qualified equivalence (proved on dynamics-encoding fragment) -/

/-- Fragment-qualified bridge: constructive FC membership ↔ hom-relative dynamics-encoding
satisfaction (headline hom projection tier; ungated). -/
theorem qualified_equivalence_homProjection
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    ClassicalFCMembership Z_spec Z_impl ↔
      AssertionalFCHomMembership Z_spec Z_impl := by
  unfold ClassicalFCMembership AssertionalFCHomMembership
  exact partialDynamicsHom_iff_hom.symm

/-- Shared fixed-table specialization: literal partial dynamics ↔ partial identity hom. -/
theorem qualified_equivalence_partialOpen [DecidableEq IZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) :
    AssertionalFCPartialOpenMembership Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl := by
  unfold AssertionalFCPartialOpenMembership
  exact partialDynamicsOpen_iff_hom

/-! ## Partial bridge (synthesis / legacy projections) -/

theorem hom_implies_assertionalCross {Z : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_cross_of_hom h

theorem qualified_equivalence_extensionalOpen {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  (extensional_open_verification_equivalence hZ hImpl) hAdeq

/-! ## Negative witnesses blocking naive equivalence -/

theorem blocked_readoutOnly_membership : blockedReadoutOnlyProp :=
  biImpFails_readoutOnly

theorem blocked_barePhi_membership : blockedBarePhiProp :=
  blocked_barePhi_uniqueZ

abbrev blocked_traceProperty_separate_witness := TracePropertyLayer.traceProperty_separate_from_hom

theorem blocked_executionFOHomCompleteness_membership : blockedExecutionFOProp :=
  fo_execution_not_complete_for_hom

/-! ## Open global equivalence audit -/

theorem audit_classicalAssertional_open :
    paperClaimStatus .classicalAssertionalEquivalence = .openQuestion ∧
      blockedReadoutOnlyProp ∧
      blockedBarePhiProp ∧
      TracePropertyLayer.tracePropertySeparateProp ∧
      blockedExecutionFOProp := by
  constructor
  · rfl
  constructor
  · exact blocked_readoutOnly_membership
  constructor
  · exact blocked_barePhi_membership
  constructor
  · exact TracePropertyLayer.traceProperty_separate_from_hom
  · exact blocked_executionFOHomCompleteness_membership

end ClassicalAssertionalBridge
