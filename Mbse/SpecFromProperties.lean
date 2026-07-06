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

def synthesizeFsmSpec {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) : FSMSystem SZ IZ OZ := F

theorem synthesizeFsmSpec_satisfies {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F F :=
  fsm_satisfies_reflexive F

theorem synthesizeFsmSpec_satisfies_dynamics {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F :=
  fsm_dynamics_satisfies_reflexive F

theorem fsm_synthesized_property_iff_hom {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ)
    (F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F_impl ↔
      FSMIsIdentityHomomorphicImage (synthesizeFsmSpec F) F_impl :=
  fsm_property_iff_hom F F_impl

theorem fsm_phi_adequate {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    PhiAdequateSpec (FSMSatisfiesDynamics F F) (synthesizeFsmSpec F = synthesizeFsmSpec F) := by
  constructor
  · exact fsm_dynamics_satisfies_reflexive F
  · rfl

theorem fsm_synthesized_observables {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables (synthesizeFsmSpec F) = fsmDynamicsTable F := by
  simp [compileFsmObservables, synthesizeFsmSpec]

/-! ## General total finite -/

def synthesizeSpec {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (_hOut : AlwaysOutputs Z) :
    DiscreteSystem SZ IZ OZ :=
  Z

theorem synthesizeSpec_satisfies {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    SystemSatisfiesDynamics Z Z hOut hOut := by
  rw [PropertyFragment.General.SystemSatisfiesDynamics_iff_fsm]
  exact fsm_dynamics_satisfies_reflexive (ofDiscreteSystem Z hOut)

theorem synthesizeSpec_eq {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    synthesizeSpec Z hOut = Z := rfl

theorem compileObservables_synthesizeSpec {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    compileObservables (synthesizeSpec Z hOut) hOut = dynamicsTable Z hOut := by
  simp [compileObservables, synthesizeSpec, dynamicsTable]

/-! ## General extensional (Track D; arbitrary `SZ`) -/

/-- Canonical extensional spec from a reference system (identity synthesis today). -/
def synthesizeExtensionalSpec {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    DiscreteSystem SZ IZ OZ :=
  Z

theorem synthesizeExtensionalSpec_eq {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    synthesizeExtensionalSpec Z = Z := rfl

/-! ## Inverse synthesis (partial)

Recovery from Φ requires a witness reference `Z` (or hom witness for cross-type via HIMSY).
Bare `PropertySet` decode without canonical structure is intentionally not provided.
-/

def IsSynthesizableTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) : Prop :=
  compileObservables Z hOut = Phi ∧ synthesizeSpec Z hOut = Z

def recoverSpecFromTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (_Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) : DiscreteSystem SZ IZ OZ :=
  synthesizeSpec Z hOut

theorem recoverSpecFromTable_eq {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (h : IsSynthesizableTable Phi Z hOut) :
    recoverSpecFromTable Phi Z hOut = Z :=
  h.2

theorem recoverSpecFromTable_compiles {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (h : IsSynthesizableTable Phi Z hOut) :
    compileObservables (recoverSpecFromTable Phi Z hOut) hOut = Phi :=
  h.1

def recoverFsmFromTable {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) : FSMSystem SZ IZ OZ :=
  synthesizeFsmSpec F

theorem recoverFsmFromTable_eq {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) :
    recoverFsmFromTable F = F :=
  rfl

theorem recoverFsmFromTable_compiles {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables (recoverFsmFromTable F) = fsmDynamicsTable F := by
  simp [recoverFsmFromTable, compileFsmObservables, synthesizeFsmSpec]

theorem fsm_table_synthesizable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (F : FSMSystem SZ IZ OZ) :
    IsSynthesizableTable (dynamicsTable F.toDiscreteSystem (fsm_alwaysOutputs F)) F.toDiscreteSystem
      (fsm_alwaysOutputs F) := by
  refine ⟨?_, rfl⟩
  exact (compileObservables_eq_dynamics F.toDiscreteSystem (fsm_alwaysOutputs F)).symm

theorem comb_table_synthesizable {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ] :
    compileCombObservables (synthesizeCombSpec F) = combFunctionTable (synthesizeCombSpec F) F := by
  simp [compileCombObservables, combFunctionTable, synthesizeCombSpec_readout]

end SpecFromProperties
