import Mbse.CombinationalProperties
import Mbse.FSMProperties
import Mbse.PropertyFragment
import Mbse.TemporalLogic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

/-!
# Pathology examples for TL fragment design

Examples document where bi-implication fails and justify TL-side restrictions
(canonical synthesis, dynamics-not-readout, no `F`, no uncommitted disjunction).
-/

namespace PathologyExamples

open PropertyFragment PropertyFragment.FSM Combinational CombinationalProperties
  HomomorphismProperties SpecFromProperties FSM FSMProperties TemporalLogic

/-! ## Example 1: cardinality obstruction (combinational disjunction) -/

/-- Two-input implementation (committed to engine A). -/
abbrev implInputs := Fin 2

abbrev implOutputs := Fin 1

def implSystem : CombinationalSystem implInputs implOutputs where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := fun _ => 0

/-- Function table: always output `0` (engine A). -/
def implTable : implInputs → implOutputs := fun _ => 0

theorem impl_satisfies_table : CombSatisfiesFunction implSystem implTable := by
  rw [combSatisfiesFunction_iff]
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Four-input branching reference (paper's naive spec). -/
abbrev specInputs := Fin 4

def specSystem : CombinationalSystem specInputs implOutputs where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := fun _ => 0

/-- No surjection `implInputs → specInputs` (cardinality obstruction). -/
theorem no_surjective_input_map : ¬ ∃ f : implInputs → specInputs, Function.Surjective f := by
  rintro ⟨f, hf⟩
  have hcard : Fintype.card specInputs ≤ Fintype.card implInputs :=
    Fintype.card_le_of_surjective (α := implInputs) (β := specInputs) f hf
  simp [Fintype.card_fin] at hcard

/-- Naive four-input spec is not a homomorphic image reference for the two-input impl. -/
theorem not_comb_homomorphic_image :
    ¬ CombIsHomomorphicImage specSystem implSystem := by
  rintro ⟨w⟩
  exact no_surjective_input_map ⟨w.HI, w.HI_surjective⟩

/-- Canonical synthesized spec for the implementation table uses two inputs, not four. -/
theorem canonical_spec_hom_exists :
    CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  comb_satisfies_implies_hom implTable implSystem impl_satisfies_table

/-- The pathology sketch does not refute Stage-1 bi-implication with canonical `synthesizeSpec`. -/
theorem example1_refuted_for_canonical_spec :
    CombSatisfiesFunction implSystem implTable ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  comb_property_iff_hom implTable implSystem

/-! ## Example 2: readout-only FSM fragment (same `RZ`, different `NZ`) -/

abbrev fsmStates := Fin 2
abbrev fsmInputs := Fin 1
abbrev fsmOutputs := Fin 1

/-- Both FSMs output `0` in every state; transitions differ. -/
def sharedRZ : fsmStates → fsmOutputs := fun _ => 0

/-- Always remain in state `0`. -/
def fsmStay : FSMSystem fsmStates fsmInputs fsmOutputs where
  sz_nonempty := ⟨0⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun _ _ => 0
  RZ := sharedRZ

/-- Always move to state `1`. -/
def fsmJump : FSMSystem fsmStates fsmInputs fsmOutputs where
  sz_nonempty := ⟨0⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun _ _ => 1
  RZ := sharedRZ

theorem fsmStay_satisfies_jump_output_table :
    FSMSatisfiesOutputTable fsmJump fsmStay := by
  intro s0 f φ hmem
  rcases (mem_fsmOutputTable_iff fsmJump φ).mp hmem with ⟨s, heq⟩
  subst heq
  simpa [fsmJump, fsmStay, sharedRZ] using
    fsmTrace_satisfies_safetyOutput fsmStay s0 f s

theorem fsmJump_satisfies_stay_output_table :
    FSMSatisfiesOutputTable fsmStay fsmJump := by
  intro s0 f φ hmem
  rcases (mem_fsmOutputTable_iff fsmStay φ).mp hmem with ⟨s, heq⟩
  subst heq
  simpa [fsmJump, fsmStay, sharedRZ] using
    fsmTrace_satisfies_safetyOutput fsmJump s0 f s

theorem fsmStay_jump_not_extEqual : ¬ FSMExtEqual fsmStay fsmJump := by
  intro h
  have := h.2 0 0
  simp [fsmStay, fsmJump] at this

theorem fsmStay_jump_not_identityHom :
    ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump := by
  intro h
  exact fsmStay_jump_not_extEqual ((fsm_extEqual_iff_identityHom fsmStay fsmJump).2 h)

/-- Output-table properties fix readout but not next-state dynamics. -/
theorem example2_readout_table_incomplete :
    FSMSatisfiesOutputTable fsmJump fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
      ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump :=
  ⟨fsmStay_satisfies_jump_output_table, fsmJump_satisfies_stay_output_table, fsmStay_jump_not_identityHom⟩

/-! ## Example 3: stuttering / `F` obstruction (trace-level) -/

/-- Atomic propositions for a minimal stuttering pathology. -/
inductive StutterAtom where
  | p
  | q

/-- Trace that holds `p` at every tick (no `q`). -/
def traceNoQ : Trace StutterAtom where
  holds := fun _ a => match a with | .p => True | .q => False

/-- Trace that holds `p` everywhere but `q` at tick `2` only (stutter-visible event). -/
def traceWithQ : Trace StutterAtom where
  holds := fun t a => match a with
    | .p => True
    | .q => t = 2

theorem stutter_Gp_agree :
    traceNoQ.models (LTL.G (LTL.atom StutterAtom.p)) ↔
      traceWithQ.models (LTL.G (LTL.atom StutterAtom.p)) := by
  simp only [Trace.models, satisfiesAt, traceNoQ, traceWithQ]

theorem stutter_Fq_noQ :
    ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) := by
  intro h
  rcases h with ⟨t', _, hq⟩
  simp [satisfiesAt, traceNoQ] at hq

theorem stutter_Fq_withQ :
    traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) := by
  refine ⟨2, Nat.zero_le 2, ?_⟩
  simp [satisfiesAt, traceWithQ]

/-- `G`-only fragment cannot distinguish traces that differ only on eventual `q`. -/
theorem example3_F_obstruction :
    (∀ t, traceNoQ.holds t StutterAtom.p) ∧
      (∀ t, traceWithQ.holds t StutterAtom.p) ∧
      traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
      ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) := by
  refine ⟨fun t => by simp [traceNoQ], fun t => by simp [traceWithQ], stutter_Fq_withQ, stutter_Fq_noQ⟩

/-- `G`-only output-table properties agree; `F` mission on state distinguishes traces. -/
theorem blocked_eventuallyF_wymore :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
          ¬ (fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) := by
  refine ⟨fsm_satisfies_reflexive fsmStay, fsmJump_satisfies_stay_output_table, ?_, ?_⟩
  · simp only [Trace.models, satisfiesAt, fsmTrace, SystemToLTL.fsmTrace]
    refine ⟨1, Nat.zero_le 1, ?_⟩
    simp [fsmJump, FSM.generateStateTrajectory_succ]
  · intro h
    rcases h with ⟨t, _, ht⟩
    simp only [satisfiesAt, fsmTrace, SystemToLTL.fsmTrace] at ht
    rcases t with _ | t
    · simp [fsmStay, FSM.generateStateTrajectory_zero] at ht
    · simp [fsmStay, FSM.generateStateTrajectory_succ] at ht

end PathologyExamples
