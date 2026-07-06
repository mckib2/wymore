import Mbse.PropertyFragment

/-!
# Observable assertional properties compiled from combinational specifications

Homomorphism-visible properties for a combinational reference system coincide with
its function-table property set.
-/

namespace ObservablesFromSpec

open PropertyFragment Combinational PropertySemantics TemporalLogic

/-- Property set compiled from a combinational reference system. -/
noncomputable def compileCombObservables {IZ OZ : Type}
    (C_spec : CombinationalSystem IZ OZ) : PropertySet (LTL (CombAtom IZ OZ)) :=
  combFunctionTable C_spec C_spec.RZ

theorem compileCombObservables_satisfies {IZ OZ : Type}
    (C_spec : CombinationalSystem IZ OZ) :
    CombSatisfiesFunction C_spec C_spec.RZ := by
  rw [combSatisfiesFunction_iff]
  intro i; rfl

end ObservablesFromSpec
