import Mbse.FSMProperties
import Mbse.SpecFromProperties
import Mbse.ObservablesFromSpec
import Mbse.BlockerAudit
import Mbse.PropertySemantics
import Mbse.TemporalLogic
import Mbse.SystemToLTL

/-!
# Conditional decode: canonical dynamics Φ → FSM

Bare output-table Φ does **not** determine a unique FSM (`blocked_barePhi_uniqueZ`).
When Φ is the dynamics-complete table compiled from a reference FSM, round-trip
recovery yields that FSM up to extensional equality.
-/

namespace PhiDecode

variable {SZ IZ OZ : Type} [Nonempty IZ]

open PropertyFragment.FSM FSMProperties SpecFromProperties ObservablesFromSpec
  FragmentPathologyRegistry BlockerAudit PathologyExamples PropertySemantics TemporalLogic
  SystemToLTL

/-- Φ is canonical dynamics table shape from reference `F`. -/
def IsCanonicalDynamicsPhi (F : FSMSystem SZ IZ OZ) (Phi : PropertySet (LTL (Atom SZ IZ OZ))) : Prop :=
  Phi = fsmDynamicsTable F

noncomputable def decodeFsmFromCanonicalPhi (F : FSMSystem SZ IZ OZ)
    (_Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (_h : IsCanonicalDynamicsPhi F _Phi) : FSMSystem SZ IZ OZ :=
  recoverFsmFromTable F

omit [Nonempty IZ] in
theorem decodeFsmFromCanonicalPhi_eq (F : FSMSystem SZ IZ OZ)
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (h : IsCanonicalDynamicsPhi F Phi) :
    decodeFsmFromCanonicalPhi F Phi h = F :=
  recoverFsmFromTable_eq F

omit [Nonempty IZ] in
theorem decodeFsm_compiles (F : FSMSystem SZ IZ OZ)
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (h : IsCanonicalDynamicsPhi F Phi) :
    compileFsmObservables (decodeFsmFromCanonicalPhi F Phi h) = Phi := by
  rw [decodeFsmFromCanonicalPhi_eq F Phi h, compileFsmObservables_eq_dynamics F, h]

theorem decodeFsm_unique_up_to_ext (F G : FSMSystem SZ IZ OZ)
    (hPhi : fsmDynamicsTable F = fsmDynamicsTable G) :
    FSMExtEqual F G := by
  have hG : FSMSatisfiesDynamics F G :=
    fun s0 f φ hmem => fsm_dynamics_satisfies_reflexive G s0 f φ (hPhi ▸ hmem)
  exact fsm_satisfies_implies_extEqual hG

theorem barePhi_not_unique :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump :=
  blocked_barePhi_uniqueZ

end PhiDecode
