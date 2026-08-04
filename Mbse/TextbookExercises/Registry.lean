import Mbse.TextbookExercises.Ch02
import Mbse.TextbookExercises.Ch03
import Mbse.TextbookExercises.Ch04

/-!
# Textbook exercise registry

Curated index of selected Wymore textbook exercises formalized in Lean.
The registry is the source of truth for exercise scope (not every end-of-chapter problem).
-/

namespace Mbse.TextbookExercises

/-- Witness vs theorem-proof exercise kinds. -/
inductive ExerciseKind where
  | witness
  | theoremProof
  deriving DecidableEq, Repr

/-- Registry row linking a textbook exercise to its Lean anchor. -/
structure ExerciseEntry where
  id : String
  chapter : Nat
  kind : ExerciseKind
  status : String
  leanAnchor : String

def registry : List ExerciseEntry :=
  [ ⟨"2.116", 2, .witness, "solved", "Ch02.ex2_116_i"⟩
  , ⟨"2.117", 2, .witness, "solved", "Ch02.ex2_117_system"⟩
  , ⟨"2.118", 2, .witness, "solved", "Ch02.ex2_118_system"⟩
  , ⟨"2.121", 2, .theoremProof, "solved", "generateStateTrajectory_total_eq_composeSteps"⟩
  , ⟨"2.122", 2, .theoremProof, "solved", "generateStateTrajectory_loops_within_card"⟩
  , ⟨"2.138", 2, .theoremProof, "solved", "stateTrajectory_time_invariance_concatenation"⟩
  , ⟨"2.142", 2, .theoremProof, "solved", "reachableBy_concatenate"⟩
  , ⟨"2.148", 2, .theoremProof, "solved", "properly_aligned_sfz_card_ge_opz"⟩
  , ⟨"2.146", 2, .theoremProof, "solved", "projective_readout_osz_eq_fsz"⟩
  , ⟨"2.149", 2, .theoremProof, "solved", "properly_aligned_non_product_has_state_readout"⟩
  , ⟨"2.150", 2, .theoremProof, "solved", "properly_aligned_non_product_output_readout_dichotomy"⟩
  , ⟨"3.113", 3, .theoremProof, "solved", "Ch03.scr_port_count_sum_eq_union"⟩
  , ⟨"3.114", 3, .theoremProof, "solved", "Ch03.scr_unconnected_ports_exist"⟩
  , ⟨"3.115", 3, .theoremProof, "solved", "Ch03.scr_port_counts_gt_connections"⟩
  , ⟨"3.116", 3, .theoremProof, "solved", "Ch03.cascade_scr_min_two_components"⟩
  , ⟨"3.117", 3, .theoremProof, "solved", "Ch03.pure_feedback_min_ports"⟩
  , ⟨"3.118", 3, .witness, "solved", "Ch03.ex3_118_scr"⟩
  , ⟨"3.119", 3, .theoremProof, "solved", "Ch03.ex3_119_conjunctive_port_identification"⟩
  , ⟨"3.120", 3, .theoremProof, "solved", "Ch03.ex3_120_conjunctive_port_functions"⟩
  , ⟨"3.121", 3, .theoremProof, "solved", "Ch03.ex3_121_resultant_port_functions"⟩
  , ⟨"3.122", 3, .theoremProof, "solved", "Ch03.ex3_122_every_system_is_resultant"⟩
  , ⟨"3.123", 3, .theoremProof, "solved", "Ch03.ex3_123_conjunctive_rsy_eq_csy"⟩
  , ⟨"3.124", 3, .theoremProof, "solved", "Ch03.ex3_124_simple_cascade_rsy"⟩
  , ⟨"3.125", 3, .theoremProof, "solved", "Ch03.ex3_125_simple_feedback_rsy"⟩
  , ⟨"3.126", 3, .theoremProof, "solved", "Ch03.ex3_126_simple_mixed_rsy"⟩
  , ⟨"3.127", 3, .theoremProof, "solved", "Ch03.ex3_127_resultant_conjunctive_readout"⟩
  , ⟨"3.128", 3, .theoremProof, "solved", "Ch03.ex3_128_determines_nonsingular_scr"⟩
  , ⟨"3.129", 3, .theoremProof, "solved", "Ch03.ex3_129_subsystem_iff_recipes"⟩
  , ⟨"3.130", 3, .theoremProof, "solved", "Ch03.ex3_130_subsystem_reflexive"⟩
  , ⟨"3.131", 3, .theoremProof, "solved", "Ch03.ex3_131_subsystem_transitive"⟩
  , ⟨"3.132", 3, .theoremProof, "solved", "Ch03.ex3_132_singular_cfscr_eq_closed_loop"⟩
  , ⟨"3.133", 3, .theoremProof, "solved", "Ch03.ex3_133_conjunctive_cfscr_eq_closed_loop"⟩
  , ⟨"4.66", 4, .theoremProof, "solved", "Ch04.ex4_66_null_order_elimination"⟩
  , ⟨"4.69", 4, .theoremProof, "solved", "Ch04.ex4_69_assertion_false"⟩
  , ⟨"4.71", 4, .theoremProof, "solved", "Ch04.ex4_71_construction"⟩
  , ⟨"4.72", 4, .theoremProof, "solved", "Ch04.ex4_72_consistent_elaboration"⟩
  , ⟨"4.74", 4, .theoremProof, "solved", "Ch04.ex4_74_consistent_elaboration"⟩
  , ⟨"4.80", 4, .theoremProof, "solved", "Ch04.ex4_80_himppsy_is_parameterization"⟩
  , ⟨"4.81", 4, .theoremProof, "solved", "Ch04.ex4_81_reflexive"⟩
  , ⟨"4.82", 4, .theoremProof, "solved", "Ch04.ex4_82_reflexive"⟩
  , ⟨"4.83", 4, .theoremProof, "solved", "Ch04.ex4_83_mutual_homomorphism_isomorphic"⟩
  , ⟨"4.84", 4, .theoremProof, "solved", "Ch04.ex4_84_reflexive"⟩
  , ⟨"4.85", 4, .theoremProof, "solved", "Ch04.ex4_85_rearrangement_isomorphic"⟩
  , ⟨"4.86", 4, .theoremProof, "solved", "Ch04.ex4_86_nested_coupling_isomorphic"⟩
  ]

def solvedCount : Nat :=
  (registry.filter (fun e => e.status = "solved")).length

def totalCount : Nat :=
  registry.length

end Mbse.TextbookExercises
