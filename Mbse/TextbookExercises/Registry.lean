import Mbse.TextbookExercises.Ch02

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
  ]

def solvedCount : Nat :=
  (registry.filter (fun e => e.status = "solved")).length

def totalCount : Nat :=
  registry.length

end Mbse.TextbookExercises
