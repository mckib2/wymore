import Mbse.CombinationalProperties
import Mbse.FSMProperties
import Mbse.GeneralProperties
import Mbse.SpecFromProperties
import Mbse.ObservablesFromSpec
import Mbse.HomomorphismProperties
import Mbse.HomSoundness
import Mbse.ExtensionalDynamicsFragment

/-!
# General characterization of TL-side conditions

Consolidates Stages 1–3 bi-implications, Link B, and side conditions.
-/

namespace GeneralCharacterization


open CombinationalProperties FSMProperties GeneralProperties SpecFromProperties
  ObservablesFromSpec HomomorphismProperties HomSoundness ExtensionalDynamicsFragment
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

theorem stage2_readout_only {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F_spec F_impl → ∀ s, F_impl.RZ s = F_spec.RZ s :=
  fun h => fsm_readout_agreement F_spec F_impl h

theorem stage2_dynamics {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom F_spec F_impl

theorem stage2_dynamics_extEqual {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl → FSMExtEqual F_spec F_impl :=
  fsm_dynamics_implies_extEqual

theorem stage2_extEqual {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    FSMExtEqual F F ↔
      FSMSatisfiesOutputTable F F ∧ FSMIsIdentityHomomorphicImage F F :=
  fsm_extEqual_iff_satisfies_and_hom F

theorem stage2_canonical {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ)
    (F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F_impl ↔
      FSMIsIdentityHomomorphicImage (synthesizeFsmSpec F) F_impl :=
  fsm_synthesized_property_iff_hom F F_impl

theorem stage2_verification {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    (PhiAdequateSpec (FSMSatisfiesDynamics F_spec F_spec)
        (synthesizeFsmSpec F_spec = synthesizeFsmSpec F_spec)) →
      (FSMSatisfiesDynamics F_spec F_impl ↔
        FSMIsIdentityHomomorphicImage F_spec F_impl) := by
  intro _
  exact stage2_dynamics F_spec F_impl

theorem stage2_link_b {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables (synthesizeFsmSpec F) = fsmDynamicsTable F :=
  fsm_synthesized_observables F

theorem stage2_fsm_phi_adequate {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    PhiAdequateSpec (FSMSatisfiesDynamics F F) (synthesizeFsmSpec F = synthesizeFsmSpec F) :=
  fsm_phi_adequate F

/-! ## Stage 3 -/

theorem stage3_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  system_property_iff_hom hSpec hImpl

theorem stage3_synthesized {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  system_synthesized_property_iff_hom hZ hImpl

theorem stage3_verification {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    (PhiAdequateSpec (SystemSatisfiesDynamics Z Z hZ hZ)
        (synthesizeSpec Z hZ = synthesizeSpec Z hZ)) →
      (SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl) := by
  intro _
  exact stage3_synthesized hZ hImpl

theorem stage3_link_b {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    {Z : DiscreteSystem SZ IZ OZ} (hOut : AlwaysOutputs Z) :
    compileObservables (synthesizeSpec Z hOut) hOut = dynamicsTable Z hOut :=
  compileObservables_synthesizeSpec Z hOut

theorem stage3_fsm_embed {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    @SystemSatisfiesDynamics SZ IZ OZ F_spec.sz_finite F_spec.iz_finite F_spec.oz_finite
      F_spec.toDiscreteSystem F_impl.toDiscreteSystem
      (fsm_alwaysOutputs F_spec) (fsm_alwaysOutputs F_impl) ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom_via_embed F_spec F_impl

/-- FSM clause template lifts to `toDiscreteSystem` via Stage 3 bi-implication. -/
theorem stage3_generalizes_fsm {SZ IZ OZ : Type} [Nonempty IZ] (F_spec F_impl : FSMSystem SZ IZ OZ) :
    @SystemSatisfiesDynamics SZ IZ OZ F_spec.sz_finite F_spec.iz_finite F_spec.oz_finite
      F_spec.toDiscreteSystem F_impl.toDiscreteSystem
      (FSM.fsm_alwaysOutputs F_spec) (FSM.fsm_alwaysOutputs F_impl) ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom_via_embed F_spec F_impl

/-! ## Finite unification (pinned ↔ extensional) -/

theorem stage4_synthesizeExtensional_eq_synthesize {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    synthesizeExtensionalSpec Z = synthesizeSpec Z hOut :=
  synthesizeExtensional_eq_synthesize Z hOut

theorem stage4_extensional_satisfies_iff_dynamics_ofTotal {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {NZ_spec NZ_impl : SZ → IZ → SZ} {RZ_spec RZ_impl : SZ → OZ}
    (hNE_spec : Nonempty SZ) (hNE_impl : Nonempty SZ)
    (hSpec : AlwaysOutputs (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec))
    (hImpl : AlwaysOutputs (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl)) :
    SystemSatisfiesExtensional (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
        (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl ↔
      SystemSatisfiesDynamics (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
        (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl :=
  extensional_satisfies_iff_dynamics_ofTotal hNE_spec hNE_impl hSpec hImpl

theorem stage4_extensional_synthesized_iff_pinned_ofTotal {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {NZ Z_impl_NZ : SZ → IZ → SZ} {RZ Z_impl_RZ : SZ → OZ} (hNE : Nonempty SZ) :
    let Z_spec := DiscreteSystem.ofTotal NZ RZ hNE
    let Z_impl := DiscreteSystem.ofTotal Z_impl_NZ Z_impl_RZ hNE
    let hZ := ofTotal_alwaysOutputs NZ RZ hNE
    let hImpl := ofTotal_alwaysOutputs Z_impl_NZ Z_impl_RZ hNE
    (SystemSatisfiesExtensional Z_spec Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z_spec) Z_impl hZ hImpl) ↔
      (SystemSatisfiesDynamics Z_spec Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImage (synthesizeSpec Z_spec hZ) Z_impl hZ hImpl) :=
  extensional_synthesized_iff_pinned_synthesized_ofTotal hNE

theorem stage4_extensional_synthesized_implies_pinned {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl →
      SystemSatisfiesDynamics Z Z_impl hZ hImpl :=
  extensional_synthesized_implies_pinned_synthesized hZ hImpl

end GeneralCharacterization
