import Mbse.WymoreAttr
import Mbse.Trajectory

attribute [wymore] generateStateTrajectory_zero generateStateTrajectory_succ
attribute [wymore] generateOutputTrajectory_val
attribute [wymore] Option.map_some Option.map_map

namespace Trajectory

@[wymore] theorem FunctionGraph_mem {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ FunctionGraph f ↔ b = f a := by
  simp [FunctionGraph, Set.mem_setOf_eq]

end Trajectory
