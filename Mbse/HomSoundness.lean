import Mbse.HomomorphismProperties
import Mbse.GeneralProperties
import Mbse.PropertySemanticsBridge
import Mbse.CombinationalProperties
import Mbse.FSMProperties
import Mbse.PropertyFragmentSpec
import Mbse.SpecFromProperties
import Mbse.ExtensionalDynamicsFragment
import Mbse.HimsySynthesis

/-!
# Cross-cutting hom soundness and Link C templates

One-way: homomorphic image ⇒ property satisfaction (Thm 4.15 / trajectory preservation).
Bi-implication templates with `PhiAdequateSpec` gate.
-/

namespace HomSoundness

open PropertySemantics PropertySemanticsBridge PropertyFragment PropertyFragment.FSM
  PropertyFragment.General HomomorphismProperties CombinationalProperties FSMProperties
  SpecFromProperties GeneralProperties PropertyFragmentSpec Homomorphism
  Combinational FSM ExtensionalDynamicsFragment HimsySynthesis

/-! ## Combinational templates -/

theorem stage1_verification_equivalence {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ) :
    VerificationEquivalence
      (CombSatisfiesFunction C_impl F)
      (CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl)
      (PhiAdequateSpec (CombSatisfiesFunction (synthesizeCombSpec F) F)
        (synthesizeCombSpec F = synthesizeCombSpec F)) :=
  verificationEquivalence_of_adequate (comb_property_iff_hom F C_impl)

theorem stage1_general_verification_equivalence {IZ1 OZ1 IZ2 OZ2 : Type}
    [Fintype IZ1] [Fintype OZ1] (F : IZ1 → OZ1) (C_impl : CombinationalSystem IZ2 OZ2) :
    VerificationEquivalence
      (CombIsHomomorphicImage (synthesizeCombSpec F) C_impl)
      (CombIsHomomorphicImage (synthesizeCombSpec F) C_impl)
      (PhiAdequateSpec (CombSatisfiesFunction (synthesizeCombSpec F) F)
        (synthesizeCombSpec F = synthesizeCombSpec F)) :=
  verificationEquivalence_of_adequate Iff.rfl

/-! ## FSM templates -/

theorem stage2_verification_equivalence {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    VerificationEquivalence
      (FSMSatisfiesDynamics F_spec F_impl)
      (FSMIsIdentityHomomorphicImage F_spec F_impl)
      (PhiAdequateSpec (FSMSatisfiesDynamics F_spec F_spec)
        (synthesizeFsmSpec F_spec = synthesizeFsmSpec F_spec)) :=
  verificationEquivalence_of_adequate (fsm_property_iff_hom F_spec F_impl)

/-! ## Stage 3 templates -/

theorem stage3_verification_equivalence {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    VerificationEquivalence
      (SystemSatisfiesDynamics Z Z_impl hZ hImpl)
      (SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl)
      (PhiAdequateSpec (SystemSatisfiesDynamics Z Z hZ hZ)
        (synthesizeSpec Z hZ = synthesizeSpec Z hZ)) :=
  verificationEquivalence_of_adequate (system_synthesized_property_iff_hom hZ hImpl)

/-! ## Extensional templates -/

theorem extensional_cross_verification_equivalence {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl)
      (IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl)
      (PhiAdequateExtensionalCross Z) :=
  verificationEquivalence_of_adequate extensional_synthesized_cross_iff_hom

theorem extensional_open_verification_equivalence {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    VerificationEquivalence
      (SystemSatisfiesExtensional Z Z_impl hZ hImpl)
      (SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl)
      (PhiAdequateExtensionalOpen Z hZ) :=
  verificationEquivalence_of_adequate (extensional_synthesized_sameType_iff_hom hZ hImpl)

/-! ## HIMSY synthesis templates -/

theorem himsy_verification_equivalence {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    VerificationEquivalence
      (SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_impl)
      (IsHomomorphicImage (synthesizeHimsySpec w) Z_impl)
      (PhiAdequateHimsy w) :=
  verificationEquivalence_of_adequate (himsy_synthesized_cross_iff_hom w)

/-! ## One-way hom → Φ (soundness) -/

theorem comb_hom_implies_spec_satisfies {IZ OZ : Type}
    {C_spec C_impl : CombinationalSystem IZ OZ} (F : IZ → OZ)
    (w : CombIdentityHomomorphicImageWitness C_spec C_impl)
    (hSpec : CombSatisfiesFunction C_spec F) :
    CombSatisfiesFunction C_impl F :=
  comb_hom_spec_satisfies_impl F w hSpec

theorem fsm_hom_implies_spec_satisfies_dynamics {SZ IZ OZ : Type} [Nonempty IZ]
    {F_spec F_impl : FSMSystem SZ IZ OZ}
    (w : FSMIdentityHomomorphicImageWitness F_spec F_impl)
    (hSpec : FSMSatisfiesDynamics F_spec F_spec) :
    FSMSatisfiesDynamics F_spec F_impl :=
  fsm_hom_spec_satisfies_dynamics w hSpec

theorem hom_preserves_visible_output {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    (projectObs w s0 f t).output =
      (generateOutputTrajectory Z_impl s0 f t).map w.HO :=
  visibleObs_projected_output w s0 f t

/-- Disjunction side condition: canonical synthesis commits one branch (Pathology Example 1). -/
theorem disjunction_requires_canonical_synthesis :
    PropertyFragmentSpec.pinnedFragment.disjunctionPolicy =
      PropertyFragmentSpec.DisjunctionPolicy.canonicalCommitment := rfl

/-- Eventually excluded from assertional fragment (Pathology Example 3). -/
theorem eventually_excluded_from_fragment :
    PropertyFragmentSpec.pinnedFragment.eventuallyPolicy =
      PropertyFragmentSpec.EventuallyPolicy.excluded := rfl

end HomSoundness
