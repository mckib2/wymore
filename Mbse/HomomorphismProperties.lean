import Mbse.Homomorphism
import Mbse.PropertyFragment
import Mbse.FSMProperties

/-!
# Homomorphism preservation of assertional properties

One-way implication: if a reference system satisfies property fragment `Phi` and an
implementation is a homomorphic image, the implementation inherits homomorphism-visible
properties.
-/

namespace HomomorphismProperties

open PropertyFragment PropertySemantics Combinational Homomorphism

/-! ## Combinational layer -/

/-- Combinational homomorphic image witness (input/output maps only). -/
structure CombHomomorphicImageWitness {IZ1 OZ1 IZ2 OZ2 : Type}
    (C_spec : CombinationalSystem IZ1 OZ1)
    (C_impl : CombinationalSystem IZ2 OZ2) where
  HI : IZ2 → IZ1
  HO : OZ2 → OZ1
  HI_surjective : Function.Surjective HI
  HO_surjective : Function.Surjective HO
  preserves_readout : ∀ i, HO (C_impl.RZ i) = C_spec.RZ (HI i)

def CombIsHomomorphicImage {IZ1 OZ1 IZ2 OZ2 : Type}
    (C_spec : CombinationalSystem IZ1 OZ1) (C_impl : CombinationalSystem IZ2 OZ2) : Prop :=
  Nonempty (CombHomomorphicImageWitness C_spec C_impl)

theorem comb_morphism_gives_image {IZ1 OZ1 IZ2 OZ2 : Type}
    {C_spec : CombinationalSystem IZ1 OZ1} {C_impl : CombinationalSystem IZ2 OZ2}
    (m : Combinational.SystemMorphism C_impl C_spec)
    (hI : Function.Surjective m.φI) (hO : Function.Surjective m.φO) :
    CombIsHomomorphicImage C_spec C_impl :=
  ⟨{
    HI := m.φI
    HO := m.φO
    HI_surjective := hI
    HO_surjective := hO
    preserves_readout := fun i => m.preserves_readout i
  }⟩

theorem comb_hom_preserves_function {IZ1 OZ1 IZ2 OZ2 : Type}
    {C_spec : CombinationalSystem IZ1 OZ1} {C_impl : CombinationalSystem IZ2 OZ2}
    (h : CombHomomorphicImageWitness C_spec C_impl) (F : IZ1 → OZ1)
    (hF : CombSatisfiesFunction C_spec F) (i : IZ2) :
    h.HO (C_impl.RZ i) = F (h.HI i) := by
  rw [h.preserves_readout i, (combSatisfiesFunction_iff C_spec F).mp hF (h.HI i)]

/-- Identity-map combinational homomorphic image (same input/output types). -/
structure CombIdentityHomomorphicImageWitness {IZ OZ : Type}
    (C_spec C_impl : CombinationalSystem IZ OZ) where
  preserves_readout : ∀ i, C_impl.RZ i = C_spec.RZ i

def CombIsIdentityHomomorphicImage {IZ OZ : Type}
    (C_spec C_impl : CombinationalSystem IZ OZ) : Prop :=
  Nonempty (CombIdentityHomomorphicImageWitness C_spec C_impl)

theorem comb_identity_witness_of_satisfies {IZ OZ : Type}
    {C_spec C_impl : CombinationalSystem IZ OZ} (F : IZ → OZ)
    (hSpec : CombSatisfiesFunction C_spec F) (hImpl : CombSatisfiesFunction C_impl F) :
    CombIdentityHomomorphicImageWitness C_spec C_impl where
  preserves_readout := fun i => by
    rw [(combSatisfiesFunction_iff C_impl F).mp hImpl i,
      (combSatisfiesFunction_iff C_spec F).mp hSpec i]

theorem comb_identity_hom_impl_satisfies {IZ OZ : Type}
    {C_spec C_impl : CombinationalSystem IZ OZ} (F : IZ → OZ)
    (h : CombIdentityHomomorphicImageWitness C_spec C_impl)
    (hF : CombSatisfiesFunction C_spec F) :
    CombSatisfiesFunction C_impl F := by
  rw [combSatisfiesFunction_iff] at hF ⊢
  intro i
  rw [← hF i, h.preserves_readout i]

/-- One-way: spec satisfies `F` and identity homomorphic image implies impl satisfies `F`. -/
theorem comb_hom_spec_satisfies_impl {IZ OZ : Type}
    {C_spec C_impl : CombinationalSystem IZ OZ} (F : IZ → OZ)
    (w : CombIdentityHomomorphicImageWitness C_spec C_impl)
    (hSpec : CombSatisfiesFunction C_spec F) :
    CombSatisfiesFunction C_impl F :=
  comb_identity_hom_impl_satisfies F w hSpec

/-! ## FSM layer -/

open PropertyFragment.FSM FSM FSMProperties

/-- One-way: identity homomorphic image + spec output-table satisfaction implies impl satisfaction. -/
theorem fsm_hom_spec_satisfies_output {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    {F_spec F_impl : FSMSystem SZ IZ OZ}
    (w : FSMIdentityHomomorphicImageWitness F_spec F_impl)
    (_hSpec : FSMSatisfiesOutputTable F_spec F_spec) :
    FSMSatisfiesOutputTable F_spec F_impl :=
  fsm_extEqual_implies_satisfies_output
    (F_spec := F_spec) (F_impl := F_impl)
    ⟨fun s => (w.preserves_readout s).symm, fun s i => (w.preserves_transition s i).symm⟩

/-- One-way: identity homomorphic image + spec dynamics satisfaction implies impl satisfaction. -/
theorem fsm_hom_spec_satisfies_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    {F_spec F_impl : FSMSystem SZ IZ OZ}
    (w : FSMIdentityHomomorphicImageWitness F_spec F_impl)
    (_hSpec : FSMSatisfiesDynamics F_spec F_spec) :
    FSMSatisfiesDynamics F_spec F_impl :=
  fsm_extEqual_implies_satisfies_dynamics
    (F_spec := F_spec) (F_impl := F_impl)
    ⟨fun s => (w.preserves_readout s).symm, fun s i => (w.preserves_transition s i).symm⟩

/-! ## General discrete-system layer (output-visible formulas) -/

/-- An assertional property is preserved when it depends only on projected outputs. -/
theorem homomorphic_image_preserves_output_values {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    (generateOutputTrajectory Z_impl s0 f t).map w.HO =
      generateOutputTrajectory Z_spec (w.HS s0) (fun τ => (f τ).map w.HI) t :=
  homomorphicImage_preserves_output_trajectory w s0 f t

end HomomorphismProperties
