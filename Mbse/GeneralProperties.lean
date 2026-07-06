import Mbse.GeneralPropertyFragment
import Mbse.FSMProperties
import Mbse.Homomorphism
import Mbse.SpecFromProperties

/-!
# Stage 3: general total finite `DiscreteSystem` bi-implication

Lifts Stage-2 FSM results through `FSM.ofDiscreteSystem` / `toDiscreteSystem`.
-/

namespace GeneralProperties


open PropertyFragment.General PropertyFragment.FSM FSM FSMProperties SpecFromProperties
  PropertySemantics Homomorphism GeneralFSMBridge

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

structure SystemIdentityHomomorphicImageWitness (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) where
  preserves_readout : ∀ s, (ofDiscreteSystem Z_impl hImpl).RZ s =
    (ofDiscreteSystem Z_spec hSpec).RZ s
  preserves_transition : ∀ s i,
    (ofDiscreteSystem Z_impl hImpl).NZ s i =
      (ofDiscreteSystem Z_spec hSpec).NZ s i

def SystemIsIdentityHomomorphicImage (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  Nonempty (SystemIdentityHomomorphicImageWitness Z_spec Z_impl hSpec hImpl)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem system_identityHom_iff_fsm {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl ↔
      FSMIsIdentityHomomorphicImage (ofDiscreteSystem Z_spec hSpec)
        (ofDiscreteSystem Z_impl hImpl) := by
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.preserves_readout, w.preserves_transition⟩⟩
  · intro ⟨w⟩
    exact ⟨⟨w.preserves_readout, w.preserves_transition⟩⟩

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem system_extEqual_iff_identityHom {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemExtEqual Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl := by
  rw [SystemExtEqual_iff_fsm, system_identityHom_iff_fsm, fsm_extEqual_iff_identityHom]

theorem system_satisfies_implies_hom {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl := by
  rw [SystemSatisfiesDynamics_iff_fsm] at h
  exact (system_identityHom_iff_fsm hSpec hImpl).2 (fsm_satisfies_implies_hom h)

theorem system_hom_implies_satisfies {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl := by
  rw [SystemSatisfiesDynamics_iff_fsm]
  exact fsm_hom_implies_satisfies ((system_identityHom_iff_fsm hSpec hImpl).1 h)

/-- Stage 3 identity-map bi-implication for total finite systems. -/
theorem system_property_iff_hom {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  ⟨system_satisfies_implies_hom hSpec hImpl, system_hom_implies_satisfies hSpec hImpl⟩

theorem system_synthesized_property_iff_hom {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl := by
  simp [synthesizeSpec, system_property_iff_hom hZ hImpl]

theorem fsm_property_iff_hom_via_embed {F_spec F_impl : FSMSystem SZ IZ OZ} :
    SystemSatisfiesDynamics F_spec.toDiscreteSystem F_impl.toDiscreteSystem
        (FSM.fsm_alwaysOutputs F_spec) (FSM.fsm_alwaysOutputs F_impl) ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl := by
  rw [PropertyFragment.General.SystemSatisfiesDynamics_iff_fsm]
  rw [PropertyFragment.FSM.fsm_satisfies_dynamics_spec_extEqual
      (PropertyFragment.General.ofDiscreteSystem_extEqual_toDiscreteSystem F_spec)]
  rw [PropertyFragment.FSM.fsm_satisfies_dynamics_impl_extEqual
      (PropertyFragment.General.ofDiscreteSystem_extEqual_toDiscreteSystem F_impl)]
  exact fsm_property_iff_hom F_spec F_impl

end GeneralProperties
