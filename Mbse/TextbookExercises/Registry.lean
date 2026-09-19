import Mbse.TextbookExercises.Ch02
import Mbse.TextbookExercises.Ch03
import Mbse.TextbookExercises.Ch04
import Mbse.TextbookExercises.Ch05

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
  , ⟨"5.141", 5, .theoremProof, "counterexample", "Ch05.subsystem_isSystemMode_or_counterexample"⟩
  , ⟨"5.142", 5, .theoremProof, "qualified", "Ch05.exercise5_142_unconditional"⟩
  , ⟨"5.146", 5, .theoremProof, "solved", "Ch05.selfMode_constantTime_iterate"⟩
  , ⟨"5.147", 5, .theoremProof, "solved", "Ch05.constantMode_state_at_mul"⟩
  , ⟨"5.148", 5, .theoremProof, "solved", "Ch05.variableTime_constantInput_state_at_accumulatedTime"⟩
  , ⟨"5.149", 5, .theoremProof, "solved", "Ch05.constantMode_compose_indices"⟩
  , ⟨"5.150", 5, .theoremProof, "solved", "Ch05.variableTime_compose_isSystemMode"⟩
  , ⟨"5.151", 5, .theoremProof, "solved", "Ch05.mutual_constantMode_self_d_sq_indices"⟩
  , ⟨"5.152", 5, .theoremProof, "solved", "Ch05.mutual_primary_modes_isomorphic"⟩
  , ⟨"5.153", 5, .theoremProof, "counterexample", "Ch05.mutual_modes_not_equal_counterexample"⟩
  , ⟨"5.156", 5, .theoremProof, "solved", "Ch05.not_manifest_zero_not_inMode"⟩
  , ⟨"5.157", 5, .theoremProof, "solved", "Ch05.primary_has_CNS_SMBF"⟩
  , ⟨"5.158", 5, .theoremProof, "solved", "Ch05.primary_NZ_RZ_restriction"⟩
  , ⟨"5.159", 5, .theoremProof, "solved", "Ch05.primary_manifest_persists"⟩
  , ⟨"5.160", 5, .theoremProof, "solved", "Ch05.rsysmo_isSystemParameterization"⟩
  , ⟨"5.161", 5, .theoremProof, "solved", "Ch05.reachableMode_isPrimary_exercise"⟩
  , ⟨"5.162", 5, .theoremProof, "solved", "Ch05.complement_isolated_isIsolated"⟩
  , ⟨"5.163", 5, .theoremProof, "solved", "Ch05.isolated_throughout_iff_start"⟩
  , ⟨"5.164", 5, .theoremProof, "solved", "Ch05.transient_vs_isolated_exercise"⟩
  , ⟨"5.165", 5, .theoremProof, "solved", "Ch05.transientState_generates_transientMode_exercise"⟩
  , ⟨"5.166", 5, .theoremProof, "solved", "Ch05.absorbingState_generates_absorbing_rsysmo"⟩
  , ⟨"5.167", 5, .theoremProof, "solved", "Ch05.proper_reachableMode_absorbing_exercise"⟩
  , ⟨"5.168", 5, .theoremProof, "solved", "Ch05.isolated_isAbsorbing_exercise"⟩
  , ⟨"5.169", 5, .theoremProof, "counterexample", "Ch05.constantInput_nonprimary_not_implies_constantTime"⟩
  , ⟨"5.170", 5, .theoremProof, "solved", "Ch05.fixedTimeMode_constant_indices"⟩
  , ⟨"5.171", 5, .theoremProof, "solved", "Ch05.transientComplement_isAbsorbing_exercise"⟩
  , ⟨"5.172", 5, .theoremProof, "solved", "Ch05.inevitable_admits_alternate_SMBF_exercise"⟩
  , ⟨"5.173", 5, .theoremProof, "solved", "Ch05.primary_constOutput_inevitable_exercise"⟩
  , ⟨"5.174", 5, .theoremProof, "solved", "Ch05.timeElaborateCNS_implements_inevitable_exercise"⟩
  , ⟨"5.175", 5, .theoremProof, "solved", "Ch05.primaryMode_reflexive_exercise"⟩
  , ⟨"5.176", 5, .theoremProof, "solved", "Ch05.primaryMode_transitive_exercise"⟩
  , ⟨"5.177", 5, .theoremProof, "solved", "Ch05.implements_of_mode_hom_iso_exercise"⟩
  , ⟨"5.178", 5, .theoremProof, "solved", "Ch05.iimpsys_isSystemParameterization"⟩
  , ⟨"5.179", 5, .theoremProof, "solved", "Ch05.eimpsys_isSystemParameterization"⟩
  , ⟨"5.184", 5, .theoremProof, "solved", "Ch05.primary_hiisysmo_exercise"⟩
  , ⟨"5.185", 5, .theoremProof, "solved", "Ch05.constant_hiisysmo_exercise"⟩
  , ⟨"5.186", 5, .theoremProof, "solved", "Ch05.implements_of_homImage_implements_exercise"⟩
  , ⟨"5.187", 5, .theoremProof, "solved", "Ch05.constantMode_implementedExperiment_exercise"⟩
  , ⟨"5.188", 5, .theoremProof, "counterexample", "Ch05.inevitable_mode_not_transitive"⟩
  , ⟨"5.190", 5, .theoremProof, "counterexample", "Ch05.smbf_not_unique_without_inevitable"⟩
  , ⟨"5.191", 5, .theoremProof, "solved", "Ch05.sysmo_functional_iff_exercise"⟩
  , ⟨"5.193", 5, .theoremProof, "qualified", "Ch05.hologenic_conjunctive_nonconstricting_qualified"⟩
  , ⟨"6.82", 6, .theoremProof, "solved", "Ch06.rsysmo_fsr_iff_exercise"⟩
  , ⟨"6.86", 6, .theoremProof, "solved", "Ch06.eligible_output_restriction_claim_exercise"⟩
  , ⟨"6.87", 6, .theoremProof, "solved", "Ch06.himio_himsy_reverse_claim_exercise"⟩
  , ⟨"6.88", 6, .theoremProof, "solved", "Ch06.himsy_satisfies_himio_exercise"⟩
  , ⟨"6.89", 6, .theoremProof, "solved", "Ch06.ior_iso_himsy_iff_claim_exercise"⟩
  , ⟨"6.90", 6, .theoremProof, "solved", "Ch06.subreq_equal_itr_lifts_claim_exercise"⟩
  , ⟨"6.91", 6, .theoremProof, "solved", "Ch06.canonical_subreq_claim_exercise"⟩
  , ⟨"6.93", 6, .theoremProof, "solved", "Ch06.full_itr_fsr_nonempty_claim_exercise"⟩
  , ⟨"6.94", 6, .theoremProof, "solved", "Ch06.full_itr_complete_or_empty_claim_exercise"⟩
  , ⟨"6.95", 6, .theoremProof, "solved", "Ch06.incomplete_only_fsr_exists_exercise"⟩
  , ⟨"6.97", 6, .theoremProof, "qualified", "Ch06.tsy_family_eq_normio_exercise"⟩
  , ⟨"6.99", 6, .theoremProof, "solved", "Ch06.normIO_satisfies_completely_exercise"⟩
  , ⟨"6.101", 6, .theoremProof, "solved", "Ch06.fsr_closed_under_ts_subset_exercise"⟩
  , ⟨"6.102", 6, .theoremProof, "solved", "Ch06.tsy_isSystemParameterization_exercise"⟩
  , ⟨"6.103", 6, .theoremProof, "solved", "Ch06.tsy_trajectory_characterization_exercise"⟩
  ]

def solvedCount : Nat :=
  (registry.filter (fun e => e.status = "solved")).length

def totalCount : Nat :=
  registry.length

end Mbse.TextbookExercises
