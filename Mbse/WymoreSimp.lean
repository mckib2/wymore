import Mbse.WymoreAttr
import Mbse.Trajectory

/-!
# Wymore simp lemmas

Registers safe `@[wymore]` facts used by `wymore_simp`.  Additional rsy /
UISCR lemmas are tagged at their declaration sites in `Wymore.lean` and
`WymoreModeCoupling.lean`.
-/

attribute [wymore] generateStateTrajectory_zero generateStateTrajectory_succ
attribute [wymore] generateOutputTrajectory_val
attribute [wymore] Option.map_some Option.map_map

namespace Trajectory

@[wymore] theorem FunctionGraph_mem {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ FunctionGraph f ↔ b = f a := by
  simp [FunctionGraph, Set.mem_setOf_eq]

end Trajectory
