import Mbse.Homomorphism
import Mbse.HomWitnessConstruction
import Mbse.WymorePropertyFragment
import Mbse.FSMProperties
import Mbse.FiniteWymore
import Mbse.PartialDynamicsHomFragment
import Mbse.WymoreExercises

/-!
# Finite homomorphism search

Enumerates candidate Def.~4.3 maps on finite alphabets and returns a witness when
one exists. Complements [`HomWitnessConstruction`](HomWitnessConstruction.lean)
(verify supplied maps / decide identity extEqual).

Infinite/real automatic discovery remains blocked
(`HomWitnessConstruction.synthesis_automaticHomDiscovery_blocked`).
-/

namespace HomSearch

open Homomorphism WymorePropertyFragment FSMProperties HomWitnessConstruction
  PartialDynamicsHomFragment WymoreExercises

variable {SZ IZ OZ SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}

/-! ## Decidable checks on supplied maps -/

/-- Surjectivity as a `Bool` on finite types. -/
def checkSurjective [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) : Bool :=
  decide (Function.Surjective f)

theorem checkSurjective_iff {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    [Decidable (Function.Surjective f)] (f : α → β) :
    checkSurjective f = true ↔ Function.Surjective f :=
  decide_eq_true_iff

/-- Check static Def.~4.3 laws for fixed maps (no surjectivity). -/
noncomputable def checkHomLaws [DecidableEq SZ1] [DecidableEq OZ1]
    [Fintype SZ2] [Fintype IZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) : Bool :=
  decide (∀ x : SZ2, (Z_impl.RZ x).map HO = Z_spec.RZ (HS x)) &&
    decide (∀ x : SZ2, ∀ oi : Option IZ2,
      HS (Z_impl.NZ x oi) = Z_spec.NZ (HS x) (oi.map HI))

theorem checkHomLaws_iff [DecidableEq SZ1] [DecidableEq OZ1]
    [Fintype SZ2] [Fintype IZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) :
    checkHomLaws Z_spec Z_impl HS HI HO = true ↔
      (∀ x, (Z_impl.RZ x).map HO = Z_spec.RZ (HS x)) ∧
        (∀ x oi, HS (Z_impl.NZ x oi) = Z_spec.NZ (HS x) (oi.map HI)) := by
  simp [checkHomLaws, Bool.and_eq_true, decide_eq_true_eq]

/-- Package maps into a witness when checks succeed. -/
noncomputable def tryWitness [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) :
    Option (HomomorphicImageWitness Z_spec Z_impl) :=
  if hS : Function.Surjective HS then
    if hI : Function.Surjective HI then
      if hO : Function.Surjective HO then
        if hR : ∀ x, (Z_impl.RZ x).map HO = Z_spec.RZ (HS x) then
          if hN : ∀ x oi, HS (Z_impl.NZ x oi) = Z_spec.NZ (HS x) (oi.map HI) then
            some {
              HS := HS, HI := HI, HO := HO
              HS_surjective := hS, HI_surjective := hI, HO_surjective := hO
              preserves_readout := hR, preserves_transition := hN
            }
          else none
        else none
      else none
    else none
  else none

theorem tryWitness_sound [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (_h : tryWitness Z_spec Z_impl HS HI HO = some w) :
    IsHomomorphicImage Z_spec Z_impl :=
  ⟨w⟩

theorem tryWitness_succeeds_of_witness [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    (tryWitness Z_spec Z_impl w.HS w.HI w.HO).isSome := by
  simp [tryWitness, w.HS_surjective, w.HI_surjective, w.HO_surjective,
    w.preserves_readout, w.preserves_transition]

/-! ## Same-type identity search (Bool; witness structure is a Prop) -/

/-- Decide pointwise `PartialExtEqual` on finite same-type systems. -/
noncomputable def checkPartialExtEqual [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Bool :=
  decide (∀ s : SZ, Z_impl.RZ s = Z_spec.RZ s) &&
    decide (∀ s : SZ, ∀ oi : Option IZ, Z_impl.NZ s oi = Z_spec.NZ s oi)

theorem checkPartialExtEqual_iff [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) :
    checkPartialExtEqual Z_spec Z_impl = true ↔ PartialExtEqual Z_spec Z_impl := by
  simp [checkPartialExtEqual, PartialExtEqual, Bool.and_eq_true, decide_eq_true_eq]

/-- Identity search as a Bool (Prop-level witness recovered via iff). -/
noncomputable def searchIdentityHom [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : Bool :=
  checkPartialExtEqual Z_spec Z_impl

theorem searchIdentityHom_iff [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) :
    searchIdentityHom Z_spec Z_impl = true ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl := by
  rw [searchIdentityHom, checkPartialExtEqual_iff, partial_extEqual_iff_identityHom]

theorem searchIdentityHom_complete [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    searchIdentityHom Z_spec Z_impl = true :=
  (searchIdentityHom_iff Z_spec Z_impl).mpr h

/-- Lift identity agreement to a Def.~4.3 identity witness. -/
noncomputable def identityHomWitness [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (h : PartialExtEqual Z_spec Z_impl) :
    HomomorphicImageWitness Z_spec Z_impl where
  HS := id
  HI := id
  HO := id
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun s oi => by
    simp [h.2 s oi]
  preserves_readout := fun s => by
    simp [h.1 s]

/-! ## Full finite search -/

/-- Brute-force search over all `HS, HI, HO` on finite alphabets. -/
noncomputable def searchHom [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) :
    Option (HomomorphicImageWitness Z_spec Z_impl) :=
  if h : ∃ (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1),
      (tryWitness Z_spec Z_impl HS HI HO).isSome = true then
    let HS := Classical.choose h
    let HI := Classical.choose (Classical.choose_spec h)
    let HO := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
    tryWitness Z_spec Z_impl HS HI HO
  else
    none

theorem searchHom_sound [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (_h : searchHom Z_spec Z_impl = some w) :
    IsHomomorphicImage Z_spec Z_impl :=
  ⟨w⟩

/-- Completeness: full search returns `some` whenever a Def.~4.3 witness exists. -/
theorem searchHom_complete [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (h : IsHomomorphicImage Z_spec Z_impl) :
    (searchHom Z_spec Z_impl).isSome = true := by
  rcases h with ⟨w⟩
  have hTry : (tryWitness Z_spec Z_impl w.HS w.HI w.HO).isSome = true :=
    tryWitness_succeeds_of_witness Z_spec Z_impl w
  have hex : ∃ (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1),
      (tryWitness Z_spec Z_impl HS HI HO).isSome = true :=
    ⟨w.HS, w.HI, w.HO, hTry⟩
  simp only [searchHom, hex, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))

/-- Search surjective `HS` with identity I/O maps (same `IZ`/`OZ`). -/
noncomputable def searchProjectionHom [Fintype SZ1] [Fintype SZ2] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ1] [DecidableEq SZ2] [DecidableEq IZ] [DecidableEq OZ]
    (Z_spec : DiscreteSystem SZ1 IZ OZ) (Z_impl : DiscreteSystem SZ2 IZ OZ) :
    Option (HomomorphicImageWitness Z_spec Z_impl) :=
  if h : ∃ HS : SZ2 → SZ1, (tryWitness Z_spec Z_impl HS id id).isSome = true then
    tryWitness Z_spec Z_impl (Classical.choose h) id id
  else
    none

theorem searchProjectionHom_sound [Fintype SZ1] [Fintype SZ2] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ1] [DecidableEq SZ2] [DecidableEq IZ] [DecidableEq OZ]
    (Z_spec : DiscreteSystem SZ1 IZ OZ) (Z_impl : DiscreteSystem SZ2 IZ OZ)
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (_h : searchProjectionHom Z_spec Z_impl = some w) :
    IsHomomorphicImage Z_spec Z_impl :=
  ⟨w⟩

/-! ## Case-study wiring -/

theorem pattern01110Elab_via_tryConstruct :
    IsHomomorphicImage pattern01110 pattern01110Elab :=
  pattern01110Elab_maps_verified

theorem pattern01110Rich_via_tryConstruct :
    IsHomomorphicImage pattern01110 pattern01110Rich :=
  pattern01110Rich_maps_verified

theorem dualPatternElab_search_ok :
    IsHomomorphicImage dualPatternSpec dualPatternElab :=
  dualPatternElab_hom

/-- Same-type identity search succeeds on a system against itself. -/
theorem searchIdentity_self [Fintype SZ] [Fintype IZ] [DecidableEq OZ] [DecidableEq SZ]
    (Z : DiscreteSystem SZ IZ OZ) :
    searchIdentityHom Z Z = true :=
  searchIdentityHom_complete Z Z ⟨⟨fun _ => rfl, fun _ _ => rfl⟩⟩

/-- Completeness of search on the finite recognizer elaboration (via existing witness). -/
theorem pattern01110Elab_searchHom_complete :
    (searchHom (Z_spec := pattern01110) (Z_impl := pattern01110Elab)).isSome = true :=
  searchHom_complete pattern01110 pattern01110Elab pattern01110Elab_hom

end HomSearch
