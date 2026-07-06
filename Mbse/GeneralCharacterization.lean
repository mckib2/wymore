import Mbse.CombinationalProperties
import Mbse.FSMProperties

/-!
# General characterization of TL-side conditions

Consolidates Stage 1 (combinational bi-implication) and Stage 2 (FSM side conditions).
-/

namespace GeneralCharacterization

open CombinationalProperties FSMProperties PropertyFragment PropertyFragment.FSM SpecFromProperties
  PropertySemantics Combinational FSM HomomorphismProperties

/-- Stage 1: combinational function-table fragment — full bi-implication. -/
theorem stage1_combinational {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ) :
    CombSatisfiesFunction C_impl F ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl :=
  comb_property_iff_hom F C_impl

/-- Stage 2: readout-only output-table properties fix `RZ` but not `NZ`. -/
theorem stage2_readout_only {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F_spec F_impl → ∀ s, F_impl.RZ s = F_spec.RZ s :=
  fsm_readout_agreement F_spec F_impl

/-- Stage 2: full dynamics fragment — bi-implication under identity maps. -/
theorem stage2_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom F_spec F_impl

/-- Stage 2: dynamics satisfaction implies full extensional equality. -/
theorem stage2_dynamics_extEqual {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl → FSMExtEqual F_spec F_impl :=
  fsm_dynamics_implies_extEqual

/-- Stage 2: output-table fragment ties extensional equality only reflexively. -/
theorem stage2_extEqual {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F : FSMSystem SZ IZ OZ) :
    FSMExtEqual F F ↔
      FSMSatisfiesOutputTable F F ∧ FSMIsIdentityHomomorphicImage F F :=
  fsm_extEqual_iff_satisfies_and_hom F

end GeneralCharacterization
