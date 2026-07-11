import Mbse.ClassicalAssertionalBridge
import Mbse.PartialDynamicsHomFragment
import Mbse.WymorePropertyFragment
import Mbse.PropertyFragmentSpec
import Mbse.HomSearch
import Mbse.PhiChecker
import Mbse.WymoreExercises
import Mbse.ComposedCaseStudy
import Mbse.MinskyKit
import Mbse.FibCaseStudy
import Mbse.Homomorphism

/-!
# Assertional FC public API

Stable surface for the dynamics-encoding Functionality Cotyledon bridge.
Import this module from future papers instead of reaching into internal fragment files.
-/

namespace AssertionalFC

open ClassicalAssertionalBridge PartialDynamicsHomFragment WymorePropertyFragment
  PropertyFragmentSpec HomSearch PhiChecker Homomorphism WymoreExercises ComposedCaseStudy
  MinskyKit FibCaseStudy

export ClassicalAssertionalBridge (ClassicalFCMembership AssertionalFCHomMembership
  AssertionalFCPartialOpenMembership PinnedAssertionalFCMembership
  qualified_equivalence_homProjection qualified_equivalence_partialOpen)

export PartialDynamicsHomFragment (SystemSatisfiesPartialDynamicsHom
  partialDynamicsHom_iff_hom partialDynamicsHom_of_hom)

export WymorePropertyFragment (SystemSatisfiesPartialDynamicsOpen
  partialDynamicsOpen_iff_hom PartialIsIdentityHomomorphicImage PartialExtEqual)

export PropertyFragmentSpec (FragmentSpec partialHomPredicateFragment partialOpenPredicateFragment
  pinnedFiniteFragment extensionalDynamicsFragment foAssertionalFragment)

export HomSearch (searchHom searchIdentityHom searchProjectionHom tryWitness
  searchHom_sound searchHom_complete searchIdentityHom_complete checkPartialExtEqual)

export PhiChecker (checkPartialDynamicsOpen checkPartialDynamicsHom verifyAssertionalFC
  verifyAssertionalFC_iff verify_of_hom hom_of_verify
  checkPartialDynamicsOpen_iff_hom checkPartialDynamicsHom_iff)

export MinskyKit (counterInc counterDec natAdder zeroTest counterIncShift
  minskyKit_playbook counterIncShift_iff_hom counterDecElab_iff_hom
  zeroTestElab_iff_hom zeroTestDual_iff_hom)

export FibCaseStudy (fibSpec fibAwkwardImpl fibAwkward_iff_hom fib_caseStudy_playbook
  fibSpec_computes_fib fibAwkward_uses_shelf_components)

export WymoreExercises (onesCounter pattern01110 realAccumulator dualPatternSpec
  caseStudy_playbook onesCounterRich_iff_hom pattern01110Shift_iff_hom
  realAccumulatorRich_iff_hom dualPatternElab_iff_hom
  pattern01110Shift onesCounterV1 pattern01110V3)

export ComposedCaseStudy (cascadeSpec cascadeAwkwardImpl cascadeAwkward_iff_hom
  cascade_caseStudy_playbook)

/-- Headline fragment used by the paper. -/
abbrev headlineFragment := partialHomPredicateFragment

/-- Shared fixed-table specialization fragment. -/
abbrev fixedTableFragment := partialOpenPredicateFragment

theorem headline_iff {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    AssertionalFCHomMembership Z_spec Z_impl ↔ ClassicalFCMembership Z_spec Z_impl :=
  (qualified_equivalence_homProjection Z_spec Z_impl).symm

end AssertionalFC
