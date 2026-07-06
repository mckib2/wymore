import Mbse.Homomorphism
import Mbse.ExtensionalDynamicsFragment
import Mbse.PropertySemantics

/-!
# HIMSY constructive synthesis (Thm 4.15 packaging)

When `Z_spec` is a homomorphic image of `Z_elab`, the spec equals `HIMSY(Z_elab, HS, HI, HO)`
on `NZ`/`RZ` fields (not definitional `DiscreteSystem` equality — HIMSY uses `Classical.choose`).
-/

namespace HimsySynthesis

open Homomorphism ExtensionalDynamicsFragment PropertySemantics

/-- Pointwise `NZ`/`RZ` agreement between a spec and a HIMSY construction. -/
structure HimsySpecEqual {SZ1 IZ1 OZ1 : Type}
    (Z_spec Z_himsy : DiscreteSystem SZ1 IZ1 OZ1) : Prop where
  nz_eq : ∀ s oi, Z_spec.NZ s oi = Z_himsy.NZ s oi
  rz_eq : ∀ s, Z_spec.RZ s = Z_himsy.RZ s

/-- Constructive spec from elaboration via homomorphic-image witness (Def 4.10). -/
noncomputable def synthesizeHimsySpec {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) : DiscreteSystem SZ1 IZ1 OZ1 :=
  himsy Z_elab w.HS w.HI w.HO
    (himsyWellDefined_of_homomorphicImage w)
    w.HS_surjective w.HI_surjective w.HO_surjective

theorem synthesizeHimsySpec_eq_spec {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Inhabited IZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) :
    HimsySpecEqual Z_spec (synthesizeHimsySpec w) := by
  rcases homomorphic_image_eq_himsy w with ⟨hN, hR⟩
  exact ⟨hN, hR⟩

theorem synthesizeHimsySpec_is_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Inhabited IZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) :
    IsHomomorphicImage (synthesizeHimsySpec w) Z_elab :=
  himsy_is_homomorphic_image Z_elab w.HS w.HI w.HO
    (himsyWellDefined_of_homomorphicImage w)
    w.HS_surjective w.HI_surjective w.HO_surjective

theorem hom_spec_iff_himsy {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Inhabited IZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) :
    HimsySpecEqual Z_spec (synthesizeHimsySpec w) ↔
      IsHomomorphicImage Z_spec Z_elab := by
  constructor
  · intro _
    exact ⟨w⟩
  · intro _
    exact synthesizeHimsySpec_eq_spec w

theorem synthesizeHimsySpec_satisfies_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Inhabited IZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) :
    SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_elab :=
  extensional_cross_of_hom (synthesizeHimsySpec_is_hom (w := w))

def PhiAdequateHimsy {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) : Prop :=
  PhiAdequateSpec (SystemSatisfiesExtensionalCross Z_spec Z_elab)
    (HimsySpecEqual Z_spec (synthesizeHimsySpec w))

theorem himsy_phi_adequate_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Inhabited IZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) :
    PhiAdequateHimsy w :=
  ⟨extensional_cross_of_hom ⟨w⟩, synthesizeHimsySpec_eq_spec w⟩

theorem himsy_synthesized_cross_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_impl ↔
      IsHomomorphicImage (synthesizeHimsySpec w) Z_impl :=
  extensional_cross_property_iff_hom

theorem himsy_synthesized_verification {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateHimsy w) :
    SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_impl ↔
      IsHomomorphicImage (synthesizeHimsySpec w) Z_impl :=
  himsy_synthesized_cross_iff_hom w

end HimsySynthesis
