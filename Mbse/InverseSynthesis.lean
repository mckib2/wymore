import Mbse.SpecFromProperties
import Mbse.PhiDecode
import Mbse.BlockerAudit
import Mbse.SynthesisPipeline
import Mbse.BiImplicationFailures
import Mbse.FragmentPathologyRegistry
import Mbse.FSMProperties
import Mbse.FiniteWymore
import Mbse.ObservablesFromSpec
import Mbse.TemporalLogic
import Mbse.SystemToLTL

/-!
# Inverse synthesis characterization

Forward: witness-gated table recovery and canonical dynamics decode.
Backward: bare output-table Φ does not determine unique spec without witness/canonical shape.
-/

namespace InverseSynthesis

open SpecFromProperties PhiDecode BlockerAudit SynthesisPipeline BiImplicationFailures
  FragmentPathologyRegistry FSMProperties PropertyFragment.FSM FSM PropertySemantics
  PathologyExamples ObservablesFromSpec PropertyFragment.General TemporalLogic SystemToLTL

variable {SZ IZ OZ : Type}

/-! ## Forward (re-exports) -/

theorem forward_recoverSpecFromTable_eq {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (h : IsSynthesizableTable Phi Z hOut) :
    recoverSpecFromTable Phi Z hOut = Z :=
  recoverSpecFromTable_eq Phi Z hOut h

theorem forward_recoverSpecFromTable_compiles {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (h : IsSynthesizableTable Phi Z hOut) :
    compileObservables (recoverSpecFromTable Phi Z hOut) hOut = Phi :=
  recoverSpecFromTable_compiles Phi Z hOut h

theorem forward_decodeFsmFromCanonicalPhi_eq (F : FSMSystem SZ IZ OZ)
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (h : IsCanonicalDynamicsPhi F Phi) :
    decodeFsmFromCanonicalPhi F Phi h = F :=
  decodeFsmFromCanonicalPhi_eq F Phi h

theorem forward_decodeFsm_compiles (F : FSMSystem SZ IZ OZ)
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (h : IsCanonicalDynamicsPhi F Phi) :
    compileFsmObservables (decodeFsmFromCanonicalPhi F Phi h) = Phi :=
  decodeFsm_compiles F Phi h

/-! ## Backward / negative -/

theorem bareOutputTable_not_unique :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump :=
  blocked_barePhi_uniqueZ

theorem barePhi_not_synthesizable_without_witness :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump → ¬ FSMExtEqual fsmStay fsmJump :=
  fun _ => blocked_barePhi_uniqueZ.2

theorem isCanonicalDynamicsPhi_iff_synthesizable_fsm (F : FSMSystem SZ IZ OZ)
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ] :
    IsCanonicalDynamicsPhi F (fsmDynamicsTable F) ∧
      IsSynthesizableTable (dynamicsTable F.toDiscreteSystem (fsm_alwaysOutputs F))
        F.toDiscreteSystem (fsm_alwaysOutputs F) := by
  refine ⟨rfl, ?_⟩
  exact fsm_table_synthesizable F

/-! ## Unified inverse-synthesis spec -/

structure InverseSynthesisSpec where
  requiresWitness : Bool
  requiresCanonicalDynamics : Bool
  requiresReadoutComplete : Bool

def inverseSynthesisPinnedFinite : InverseSynthesisSpec where
  requiresWitness := true
  requiresCanonicalDynamics := true
  requiresReadoutComplete := false

def inverseSynthesisReadoutOnly : InverseSynthesisSpec where
  requiresWitness := true
  requiresCanonicalDynamics := false
  requiresReadoutComplete := false

def inverseSynthesisBareOutputTable : InverseSynthesisSpec where
  requiresWitness := false
  requiresCanonicalDynamics := false
  requiresReadoutComplete := false

theorem synthesis_bare_phi_insufficient :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump :=
  SynthesisPipeline.synthesis_bare_phi_insufficient

theorem synthesis_witness_required_for_inverse {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (h : IsSynthesizableTable Phi Z hOut) :
    recoverSpecFromTable Phi Z hOut = Z ∧
      compileObservables (recoverSpecFromTable Phi Z hOut) hOut = Phi :=
  SynthesisPipeline.synthesis_witness_required_for_inverse Phi Z hOut h

theorem bareOutputTable_missing_witness :
    inverseSynthesisBareOutputTable.requiresWitness = false ∧
      (fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump) :=
  ⟨rfl, blocked_barePhi_uniqueZ⟩

end InverseSynthesis
