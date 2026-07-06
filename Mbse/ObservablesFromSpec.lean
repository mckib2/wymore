import Mbse.PropertyFragment
import Mbse.FSMProperties
import Mbse.GeneralPropertyFragment
import Mbse.SystemToLTL

/-!
# Observable assertional properties compiled from specifications

Homomorphism-visible properties compiled from reference systems (Link B: spec → Φ).
-/

namespace ObservablesFromSpec

open PropertyFragment PropertyFragment.FSM PropertyFragment.General Combinational FSM
  PropertySemantics TemporalLogic SystemToLTL

/-! ## Combinational -/

/-- Property set compiled from a combinational reference system. -/
noncomputable def compileCombObservables {IZ OZ : Type}
    (C_spec : CombinationalSystem IZ OZ) : PropertySet (LTL (CombAtom IZ OZ)) :=
  combFunctionTable C_spec C_spec.RZ

theorem compileCombObservables_satisfies {IZ OZ : Type}
    (C_spec : CombinationalSystem IZ OZ) :
    CombSatisfiesFunction C_spec C_spec.RZ := by
  rw [combSatisfiesFunction_iff]
  intro i; rfl

/-! ## FSM -/

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

/-- Property set compiled from an FSM reference (dynamics-complete). -/
noncomputable def compileFsmObservables (F : FSMSystem SZ IZ OZ) :
    PropertySet (LTL (Atom SZ IZ OZ)) :=
  fsmDynamicsTable F

theorem compileFsmObservables_eq_dynamics (F : FSMSystem SZ IZ OZ) :
    compileFsmObservables F = fsmDynamicsTable F := rfl

/-! ## General total finite -/

/-- Property set compiled from a total finite discrete system. -/
noncomputable def compileObservables (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    PropertySet (LTL (Atom SZ IZ OZ)) :=
  dynamicsTable Z hOut

theorem compileObservables_eq_dynamics (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    compileObservables Z hOut = dynamicsTable Z hOut := rfl

end ObservablesFromSpec
