import Mbse.PropertyFragment
import Mbse.FSMProperties
import Mbse.GeneralPropertyFragment
import Mbse.ObservablesFromSpec
import Mbse.PropertySemantics
import Mbse.SystemToLTL

/-!
# Canonical specifications from property sets
-/

namespace SpecFromProperties


open PropertyFragment Combinational PropertyFragment.FSM PropertyFragment.General FSM
  FSMProperties ObservablesFromSpec PropertySemantics TemporalLogic SystemToLTL GeneralFSMBridge

/-! ## Combinational -/

def synthesizeCombSpec {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ] :
    CombinationalSystem IZ OZ :=
  fccsy F

theorem synthesizeCombSpec_readout {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ]
    (i : IZ) :
    (synthesizeCombSpec F).RZ i = F i := rfl

theorem synthesizeCombSpec_satisfies {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ] :
    CombSatisfiesFunction (synthesizeCombSpec F) F := by
  rw [combSatisfiesFunction_iff]
  intro i; rfl

/-! ## FSM -/

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

def synthesizeFsmSpec (F : FSMSystem SZ IZ OZ) : FSMSystem SZ IZ OZ := F

theorem synthesizeFsmSpec_satisfies (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F F :=
  fsm_satisfies_reflexive F

theorem synthesizeFsmSpec_satisfies_dynamics (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F :=
  fsm_dynamics_satisfies_reflexive F

theorem fsm_synthesized_property_iff_hom (F : FSMSystem SZ IZ OZ) (F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F_impl ↔
      FSMIsIdentityHomomorphicImage (synthesizeFsmSpec F) F_impl :=
  fsm_property_iff_hom F F_impl

theorem fsm_phi_adequate (F : FSMSystem SZ IZ OZ) :
    PhiAdequateSpec (FSMSatisfiesDynamics F F) (synthesizeFsmSpec F = synthesizeFsmSpec F) := by
  constructor
  · exact fsm_dynamics_satisfies_reflexive F
  · rfl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem fsm_synthesized_observables (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables (synthesizeFsmSpec F) = fsmDynamicsTable F := by
  simp [compileFsmObservables, synthesizeFsmSpec]

/-! ## General total finite -/

def synthesizeSpec (Z : DiscreteSystem SZ IZ OZ) (_hOut : AlwaysOutputs Z) : DiscreteSystem SZ IZ OZ :=
  Z

theorem synthesizeSpec_satisfies (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    SystemSatisfiesDynamics Z Z hOut hOut := by
  rw [PropertyFragment.General.SystemSatisfiesDynamics_iff_fsm]
  exact fsm_dynamics_satisfies_reflexive (ofDiscreteSystem Z hOut)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem synthesizeSpec_eq (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    synthesizeSpec Z hOut = Z := rfl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem compileObservables_synthesizeSpec (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    compileObservables (synthesizeSpec Z hOut) hOut = dynamicsTable Z hOut := by
  simp [compileObservables, synthesizeSpec, dynamicsTable]

/-! ## Inverse synthesis (partial) -/

def IsSynthesizableTable (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) : Prop :=
  compileObservables Z hOut = Phi ∧ synthesizeSpec Z hOut = Z

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsm_table_synthesizable (F : FSMSystem SZ IZ OZ) :
    IsSynthesizableTable (dynamicsTable F.toDiscreteSystem (fsm_alwaysOutputs F)) F.toDiscreteSystem
      (fsm_alwaysOutputs F) := by
  refine ⟨?_, rfl⟩
  exact (compileObservables_eq_dynamics F.toDiscreteSystem (fsm_alwaysOutputs F)).symm

theorem comb_table_synthesizable {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ] :
    compileCombObservables (synthesizeCombSpec F) = combFunctionTable (synthesizeCombSpec F) F := by
  simp [compileCombObservables, combFunctionTable, synthesizeCombSpec_readout]

end SpecFromProperties
