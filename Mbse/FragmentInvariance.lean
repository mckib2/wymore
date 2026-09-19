import Mbse.CouplingIsomorphism
import Mbse.IsomorphismConstructions
import Mbse.NestedCoupling
import Mbse.PartialDynamicsHomFragment

/-!
# What the compiled fragment does and does not see

The paper's original argument for the fragment was that an engineer "need not maintain the
correspondence map".  A referee will object that satisfaction quantifies existentially over exactly
those maps, so nothing has been eliminated.  The defensible claim is sharper and follows from the
Chapter 4 results: **the map is encoding-specific, the property set is an invariant.**

Everything below is a transport of `partialDynamicsHom_iff_hom` along a Chapter 4 theorem, so each
proof is one line and each statement is a fact about the *fragment*:

* `satisfies_iff_of_spec_iso`, `satisfies_iff_of_impl_iso` — re-encoding either side changes nothing.
* `satisfies_of_copy_impl` — in particular relabelling or permuting ports changes nothing, since a
  copy carries its own port bijections (Definition 4.47).
* `satisfies_of_elaboration` — conformance of the zones of a coupling gives conformance of the
  machine (Theorem 4.56); with injectivity the two machines are copies (Corollary 4.59).
* `satisfies_of_rearrangement`, `satisfies_of_nesting` — how components are ordered, and how they are
  grouped into subsystems, is invisible to the fragment (Exercises 4.85, 4.86).
* `satisfies_of_null_order_elimination` — components that reach no port are invisible (Exercise 4.66).
* `mutual_satisfaction_isomorphic` — on finite systems the fragment determines its reference up to
  isomorphism: it is a *characteristic formula*, which is the precise sense in which nothing was lost
  by compiling to a next-only Horn safety fragment.
-/

namespace FragmentInvariance

open Homomorphism PartialDynamicsHomFragment

/-! ## Transport along a homomorphism on either side -/

variable {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}

/-- Weakening the reference: anything realising a reference realises its homomorphic images. -/
theorem satisfies_of_spec_hom {Z_spec' : DiscreteSystem SZ3 IZ3 OZ3}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (hspec : IsHomomorphicImage Z_spec' Z_spec)
    (hsat : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec' Z_impl :=
  partialDynamicsHom_of_hom
    (isHomomorphicImage_trans hspec (hom_of_partialDynamicsHom hsat))

/-- Elaborating the build: anything that realises a build also realises its elaborations. -/
theorem satisfies_of_impl_hom {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} {Z_impl' : DiscreteSystem SZ3 IZ3 OZ3}
    (hsat : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl)
    (himpl : IsHomomorphicImage Z_impl Z_impl') :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl' :=
  partialDynamicsHom_of_hom
    (isHomomorphicImage_trans (hom_of_partialDynamicsHom hsat) himpl)

/-! ## Encoding independence -/

/-- The fragment depends on the reference only through its isomorphism class. -/
theorem satisfies_iff_of_spec_iso {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_spec' : DiscreteSystem SZ3 IZ3 OZ3} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (hiso : IsIsomorphicTo Z_spec Z_spec') :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      SystemSatisfiesPartialDynamicsHom Z_spec' Z_impl :=
  ⟨satisfies_of_spec_hom (isIsomorphicTo_symm hiso).isHomomorphicImage,
    satisfies_of_spec_hom hiso.isHomomorphicImage⟩

/-- The fragment depends on the build only through its isomorphism class. -/
theorem satisfies_iff_of_impl_iso {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} {Z_impl' : DiscreteSystem SZ3 IZ3 OZ3}
    (hiso : IsIsomorphicTo Z_impl Z_impl') :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      SystemSatisfiesPartialDynamicsHom Z_spec Z_impl' :=
  ⟨fun hsat => satisfies_of_impl_hom hsat hiso.isHomomorphicImage,
    fun hsat => satisfies_of_impl_hom hsat (isIsomorphicTo_symm hiso).isHomomorphicImage⟩

/-! ## Port relabelling and permutation

A copy (Definition 4.47) carries bijections between the two port index sets, so the statements below
cover renaming ports *and* permuting them, which is the form interface churn actually takes.
-/

section Ports

variable {SZa SZb Porta Portb OutPorta OutPortb : Type}
  {PortVala : Porta → Type} {PortValb : Portb → Type}
  {OutPortVala : OutPorta → Type} {OutPortValb : OutPortb → Type}
  {Za : DiscreteSystem SZa ((p : Porta) → PortVala p) ((q : OutPorta) → OutPortVala q)}
  {Zb : DiscreteSystem SZb ((p : Portb) → PortValb p) ((q : OutPortb) → OutPortValb q)}

/-- Re-porting the build leaves the verdict unchanged. -/
theorem satisfies_of_copy_impl {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (hcopy : IsCopyOf Za Zb)
    (hsat : SystemSatisfiesPartialDynamicsHom Z_spec Za) :
    SystemSatisfiesPartialDynamicsHom Z_spec Zb :=
  satisfies_of_impl_hom hsat hcopy.isIsomorphicTo.isHomomorphicImage

/-- Re-porting the reference leaves the verdict unchanged. -/
theorem satisfies_of_copy_spec {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (hcopy : IsCopyOf Za Zb)
    (hsat : SystemSatisfiesPartialDynamicsHom Za Z_impl) :
    SystemSatisfiesPartialDynamicsHom Zb Z_impl :=
  satisfies_of_spec_hom (isIsomorphicTo_symm hcopy.isIsomorphicTo).isHomomorphicImage hsat

end Ports

/-! ## Composition: verify the zones, get the machine

This is the result that makes the approach scale.  A solver settles small zone-level queries; this
theorem assembles them into a verdict about the coupled system, and the coupled system is never
re-examined.
-/

section Composition

variable {n : Nat} {SCR : SystemCouplingRecipe n}

/-- Theorem 4.56 at the level of the fragment: componentwise conformance lifts to the resultant. -/
theorem satisfies_of_elaboration {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (hsat : SystemSatisfiesPartialDynamicsHom Z_spec (rsy SCR hOut1)) :
    SystemSatisfiesPartialDynamicsHom Z_spec (rsy (elabRecipe E) hOut2) :=
  satisfies_of_impl_hom hsat
    (thm4_56_resultant_homomorphic_image E hOut1 hOut2).2.2.isHomomorphicImage

/--
Corollary 4.59 at the level of the fragment: when the zone maps are also injective, the two machines
satisfy exactly the same compiled fragments — neither is more abstract than the other.
-/
theorem satisfies_iff_of_elaboration_copy {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (hS : ∀ i, Function.Injective (E.hom i).HS)
    (hI : ∀ (i : Fin n) (p : SCR.VSCR.Port i), Function.Injective ((E.inPorts i).port p))
    (hO : ∀ (i : Fin n) (q : SCR.VSCR.OutPort i), Function.Injective ((E.outPorts i).port q)) :
    SystemSatisfiesPartialDynamicsHom Z_spec (rsy SCR hOut1) ↔
      SystemSatisfiesPartialDynamicsHom Z_spec (rsy (elabRecipe E) hOut2) :=
  satisfies_iff_of_impl_iso
    (cor4_59_resultant_copy E hOut1 hOut2 hS hI hO).isIsomorphicTo

/-- Exercise 4.85: the order in which components are listed is invisible to the fragment. -/
theorem satisfies_iff_of_rearrangement {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (F : Fin n ≃ Fin n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    SystemSatisfiesPartialDynamicsHom Z_spec (rsy (reindexRecipe SCR F) (fun k => hOut (F k))) ↔
      SystemSatisfiesPartialDynamicsHom Z_spec (rsy SCR hOut) :=
  satisfies_iff_of_impl_iso (ex4_85_rearrangement_isomorphic SCR F hOut).2.2

/-- Exercise 4.66: components that reach no port are invisible to the fragment. -/
theorem satisfies_of_null_order_elimination {m : Nat} {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (E : NullOrderElimination SCR m) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hsat : SystemSatisfiesPartialDynamicsHom Z_spec (rsy (elimRecipe E) (fun k => hOut (E.ι k)))) :
    SystemSatisfiesPartialDynamicsHom Z_spec (rsy SCR hOut) :=
  satisfies_of_impl_hom hsat (ex4_66_null_order_elimination E hOut).2.2

end Composition

/-- Exercise 4.86: whether components are grouped into subsystems is invisible to the fragment. -/
theorem satisfies_iff_of_nesting {n : Nat} {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    (N : NestedCoupling n) :
    SystemSatisfiesPartialDynamicsHom Z_spec (rsy (flatRecipe N) (flat_hOut N)) ↔
      SystemSatisfiesPartialDynamicsHom Z_spec (rsy (nestRecipe N) (nest_hOut N)) :=
  satisfies_iff_of_impl_iso (ex4_86_nested_coupling_isomorphic N).2.2.1

/-! ## Canonicity: the fragment is a characteristic formula -/

/--
Exercise 4.83 at the level of the fragment.  If two finite systems each satisfy the fragment
compiled from the other, they are isomorphic.  So on finite systems the compiled fragment pins its
reference down to isomorphism: it is a characteristic formula for the realisation preorder, and the
invariance results above say precisely which distinctions it is entitled to ignore.
-/
theorem mutual_satisfaction_isomorphic {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2} (hfin1 : IsFinite Z1) (hfin2 : IsFinite Z2)
    (h12 : SystemSatisfiesPartialDynamicsHom Z1 Z2)
    (h21 : SystemSatisfiesPartialDynamicsHom Z2 Z1) :
    IsIsomorphicTo Z1 Z2 :=
  ex4_83_mutual_homomorphism_isomorphic_both_finite hfin1 hfin2
    (hom_of_partialDynamicsHom h12) (hom_of_partialDynamicsHom h21)

end FragmentInvariance
