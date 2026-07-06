import Mbse.PropertyFragment

/-!
# Canonical combinational specifications from property sets

`SynthesizeSpec` produces the reference combinational system for a function-table
property set.
-/

namespace SpecFromProperties

open PropertyFragment Combinational

/-- Canonical reference system for a combinational function table. -/
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

end SpecFromProperties
