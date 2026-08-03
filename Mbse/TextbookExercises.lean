import Mbse.TextbookExercises.Predicates
import Mbse.TextbookExercises.Ch02
import Mbse.TextbookExercises.Ch03
import Mbse.TextbookExercises.Registry

/-!
# Wymore textbook exercise solutions

Curated formal solutions to selected exercises from Wayne Wymore's MBSE textbook,
with bidirectional traceability via `textbook/exercise*.json` and Lean tags.

For the paper gallery (Exercises 2.128/2.129, dual-port, accumulator), see
[`WymoreExercises`](WymoreExercises.lean).
-/

namespace Mbse.TextbookExercises

export Ch02 (ex2_117_system ex2_117_always_active ex2_117_is_trivial ex2_117_not_finite
  ex2_117_nz_ne_self ex2_118_system ex2_118_pairwise_state_dependent ex2_118_is_trivial
  ex2_118_not_finite ex2_118_literal_quantification_impossible
  ex2_121_composition ex2_121_step_fns ex2_121_stepAt ex2_122_loops
  ex2_138_time_invariance_concatenation ex2_142_reachable_concatenate
  ex2_148_sfz_card_ge_opz ex2_148_osz_eq_fsz ex2_146_osz_eq_fsz ex2_149_sz_eq_oz ex2_149_state_readout
  ex2_150_oz_eq_s1z ex2_150_readout_dichotomy
  ex2_116_i ex2_116_ii ex2_116_iii ex2_116_iv
  Ex2_116_rngNzEqSz Ex2_116_rngNzNeSz Ex2_116_rngRzEqOz Ex2_116_rngRzNeOz)

export Ch03 (scr_port_count_sum_eq_union scr_unconnected_ports_exist scr_cscr_domain_range_eq
  scr_port_counts_gt_connections cascade_scr_min_two_components pure_feedback_min_ports
  ex3_118_scr ex3_118_simple_conjunction ex3_119_conjunctive_port_identification)

end Mbse.TextbookExercises
