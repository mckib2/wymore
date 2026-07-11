import Mbse.HomSearch
import Mbse.PartialDynamicsHomFragment
import Mbse.WymorePropertyFragment
import Mbse.FSMProperties
import Mbse.ClassicalAssertionalBridge
import Mbse.HomWitnessConstruction

/-!
# Executable Φ_dyn checkers (finite tiers)

`Bool` checkers proved equivalent to semantic satisfaction predicates on finite
alphabets. Cross-type headline checking reduces to [`HomSearch`](HomSearch.lean)
via `partialDynamicsHom_iff_hom`.
-/

namespace PhiChecker

open HomSearch WymorePropertyFragment PartialDynamicsHomFragment
  ClassicalAssertionalBridge Homomorphism FSMProperties HomWitnessConstruction

variable {SZ IZ OZ SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}

/-! ## Same-type fixed-table checker -/

/-- Check shared fixed-table Φ via pointwise dynamics agreement. -/
noncomputable def checkPartialDynamicsOpen [Fintype SZ] [Fintype IZ] [DecidableEq OZ]
    [DecidableEq SZ] (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Bool :=
  checkPartialExtEqual Z_spec Z_impl

theorem checkPartialDynamicsOpen_iff [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    [DecidableEq IZ] (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) :
    checkPartialDynamicsOpen Z_spec Z_impl = true ↔
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl := by
  rw [checkPartialDynamicsOpen, checkPartialExtEqual_iff, partialDynamicsOpen_iff_extEqual]

theorem checkPartialDynamicsOpen_iff_hom [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    [DecidableEq IZ] (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) :
    checkPartialDynamicsOpen Z_spec Z_impl = true ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl := by
  rw [checkPartialDynamicsOpen_iff, partialDynamicsOpen_iff_hom]

/-! ## FSM pinned dynamics checker -/

noncomputable def checkFSMExtEqual [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) : Bool :=
  HomWitnessConstruction.checkFsmExtEqual F_spec F_impl

theorem checkFSMExtEqual_iff_hom [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    checkFSMExtEqual F_spec F_impl = true ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  HomWitnessConstruction.fsm_decide_and_verify_iff F_spec F_impl

/-! ## Cross-type headline checker (via search) -/

/-- Check headline assertional FC by searching for a Def.~4.3 witness. -/
noncomputable def checkPartialDynamicsHom [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Bool :=
  (searchHom Z_spec Z_impl).isSome

theorem checkPartialDynamicsHom_iff [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    checkPartialDynamicsHom Z_spec Z_impl = true ↔
      SystemSatisfiesPartialDynamicsHom Z_spec Z_impl := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
    exact partialDynamicsHom_of_hom (searchHom_sound Z_spec Z_impl w hw)
  · intro hSat
    exact searchHom_complete Z_spec Z_impl (partialDynamicsHom_iff_hom.mp hSat)

theorem checkPartialDynamicsHom_iff_classical [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    checkPartialDynamicsHom Z_spec Z_impl = true ↔
      ClassicalFCMembership Z_spec Z_impl := by
  rw [checkPartialDynamicsHom_iff]
  exact Iff.symm (qualified_equivalence_homProjection Z_spec Z_impl)

/-! ## Unified verify entry points -/

/-- Verify assertional FC both ways: Φ-check ↔ classical hom membership (finite). -/
noncomputable def verifyAssertionalFC [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Bool :=
  checkPartialDynamicsHom Z_spec Z_impl

theorem verifyAssertionalFC_iff [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    verifyAssertionalFC Z_spec Z_impl = true ↔
      (AssertionalFCHomMembership Z_spec Z_impl ∧ ClassicalFCMembership Z_spec Z_impl) := by
  simp only [verifyAssertionalFC]
  rw [checkPartialDynamicsHom_iff]
  constructor
  · intro h
    exact ⟨h, (qualified_equivalence_homProjection Z_spec Z_impl).mpr h⟩
  · intro ⟨h, _⟩
    exact h

/-- From a supplied witness, Φ satisfaction holds (hom → Φ direction). -/
theorem verify_of_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl :=
  partialDynamicsHom_of_hom h

/-- From Φ satisfaction, a hom exists (Φ → hom direction). -/
theorem hom_of_verify {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl) :
    IsHomomorphicImage Z_spec Z_impl :=
  partialDynamicsHom_iff_hom.mp h

end PhiChecker
