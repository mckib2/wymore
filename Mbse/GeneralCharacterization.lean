import Mbse.CombinationalProperties
import Mbse.FSMProperties
import Mbse.GeneralProperties
import Mbse.SpecFromProperties
import Mbse.ObservablesFromSpec
import Mbse.HomomorphismProperties
import Mbse.HomSoundness

/-!
# General characterization of TL-side conditions

Consolidates Stages 1–3 bi-implications, Link B, and side conditions.
-/

namespace GeneralCharacterization


open CombinationalProperties FSMProperties GeneralProperties SpecFromProperties
  ObservablesFromSpec HomomorphismProperties HomSoundness
  PropertyFragment PropertyFragment.FSM PropertyFragment.General
  PropertySemantics Combinational FSM

/-! ## Stage 1 -/

/-- Stage 1: combinational function-table fragment — full bi-implication. -/
theorem stage1_combinational {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ) :
    CombSatisfiesFunction C_impl F ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl :=
  comb_property_iff_hom F C_impl

/-- Stage 1 with Φ-adequacy gate. -/
theorem stage1_verification {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ) :
    (PhiAdequateSpec (CombSatisfiesFunction (synthesizeCombSpec F) F)
        (synthesizeCombSpec F = synthesizeCombSpec F)) →
      (CombSatisfiesFunction C_impl F ↔
        CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl) := by
  intro _
  exact stage1_combinational F C_impl

/-- Stage 1 general surjective hom (readout agreement formulation). -/
theorem stage1_combinational_general {IZ1 OZ1 IZ2 OZ2 : Type} [Fintype IZ1] [Fintype OZ1]
    (F : IZ1 → OZ1) (C_impl : CombinationalSystem IZ2 OZ2) :
    CombIsHomomorphicImage (synthesizeCombSpec F) C_impl ↔
      ∃ w, CombReadoutAgreement (synthesizeCombSpec F) C_impl w :=
  comb_general_property_iff_hom F C_impl

theorem stage1_link_b {IZ OZ : Type} [Fintype IZ] [Fintype OZ] (F : IZ → OZ) :
    compileCombObservables (synthesizeCombSpec F) = combFunctionTable (synthesizeCombSpec F) F :=
  comb_synthesized_observables F

/-! ## Stage 2 -/

theorem stage2_readout_only {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F_spec F_impl → ∀ s, F_impl.RZ s = F_spec.RZ s :=
  fsm_readout_agreement F_spec F_impl

theorem stage2_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom F_spec F_impl

theorem stage2_dynamics_extEqual {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl → FSMExtEqual F_spec F_impl :=
  fsm_dynamics_implies_extEqual

theorem stage2_extEqual {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) :
    FSMExtEqual F F ↔
      FSMSatisfiesOutputTable F F ∧ FSMIsIdentityHomomorphicImage F F :=
  fsm_extEqual_iff_satisfies_and_hom F

theorem stage2_canonical {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) (F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F_impl ↔
      FSMIsIdentityHomomorphicImage (synthesizeFsmSpec F) F_impl :=
  fsm_synthesized_property_iff_hom F F_impl

theorem stage2_verification {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    (PhiAdequateSpec (FSMSatisfiesDynamics F_spec F_spec)
        (synthesizeFsmSpec F_spec = synthesizeFsmSpec F_spec)) →
      (FSMSatisfiesDynamics F_spec F_impl ↔
        FSMIsIdentityHomomorphicImage F_spec F_impl) := by
  intro _
  exact stage2_dynamics F_spec F_impl

theorem stage2_link_b {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables (synthesizeFsmSpec F) = fsmDynamicsTable F :=
  fsm_synthesized_observables F

theorem stage2_fsm_phi_adequate {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) :
    PhiAdequateSpec (FSMSatisfiesDynamics F F) (synthesizeFsmSpec F = synthesizeFsmSpec F) :=
  fsm_phi_adequate F

/-! ## Stage 3 -/

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

theorem stage3_dynamics {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  system_property_iff_hom hSpec hImpl

theorem stage3_synthesized {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  system_synthesized_property_iff_hom hZ hImpl

theorem stage3_verification {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    (PhiAdequateSpec (SystemSatisfiesDynamics Z Z hZ hZ)
        (synthesizeSpec Z hZ = synthesizeSpec Z hZ)) →
      (SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl) := by
  intro _
  exact stage3_synthesized hZ hImpl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem stage3_link_b {Z : DiscreteSystem SZ IZ OZ} (hOut : AlwaysOutputs Z) :
    compileObservables (synthesizeSpec Z hOut) hOut = dynamicsTable Z hOut :=
  compileObservables_synthesizeSpec Z hOut

theorem stage3_fsm_embed {F_spec F_impl : FSMSystem SZ IZ OZ} :
    SystemSatisfiesDynamics F_spec.toDiscreteSystem F_impl.toDiscreteSystem
        (fsm_alwaysOutputs F_spec) (fsm_alwaysOutputs F_impl) ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom_via_embed

/-- FSM clause template lifts to `toDiscreteSystem` via Stage 3 bi-implication. -/
theorem stage3_generalizes_fsm {F_spec F_impl : FSMSystem SZ IZ OZ} :
    SystemSatisfiesDynamics F_spec.toDiscreteSystem F_impl.toDiscreteSystem
      (FSM.fsm_alwaysOutputs F_spec) (FSM.fsm_alwaysOutputs F_impl) ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom_via_embed

end GeneralCharacterization
