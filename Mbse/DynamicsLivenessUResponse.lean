import Mbse.DynamicsLivenessExplore
import Mbse.BiImplicationFailures
import Mbse.PathologyExamples
import Mbse.FSMProperties
import Mbse.SystemToLTL
import Mbse.TemporalLogic
import Mbse.WymoreExercises
import Mbse.HomomorphismProperties
import Mbse.FiniteWymore
import Mbse.PropertySemantics

/-!
# U and dynamics-tied `G(p → F(q))` exploration

Machine-checked verdicts for table-progress until and response patterns.
Production Φ_dyn remains G/X-only (`EventuallyPolicy.excluded`).
-/

namespace DynamicsLivenessUResponse

open TemporalLogic SystemToLTL PathologyExamples FSMProperties
  BiImplicationFailures HomomorphismProperties WymoreExercises FSM
  DynamicsLivenessExplore PropertyFragment.FSM PropertySemantics

/-! ## A1: Naive progress-until (blocked) -/

/-- Wrong recognizer: jump straight to accept state `5` on any bit. -/
def patternAlwaysAccept : FSMSystem MatchState Bit Bit where
  sz_nonempty := ⟨0⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun _ _ => 5
  RZ := pattern01110Out

theorem patternAlwaysAccept_not_extEqual :
    ¬ FSMExtEqual pattern01110FSM patternAlwaysAccept := by
  intro ⟨_, hN⟩
  have := hN 0 false
  simp [pattern01110FSM, patternAlwaysAccept, pattern01110Next] at this

/-- Progress-until accept: `(¬state(5)) U state(5)`. -/
def acceptUntil : LTL (Atom MatchState Bit Bit) :=
  progressUntilClause (.state (5 : MatchState))

theorem patternAlwaysAccept_satisfies_acceptUntil (f : ITZ Bit) :
    (SystemToLTL.fsmTrace patternAlwaysAccept 0 f).models acceptUntil := by
  refine ⟨1, Nat.zero_le _, ?_, ?_⟩
  · change (SystemToLTL.fsmTrace patternAlwaysAccept 0 f).holds 1 (.state 5)
    simp [SystemToLTL.fsmTrace, FSM.generateStateTrajectory_succ, patternAlwaysAccept]
  · intro t'' ht0 ht1
    have ht'' : t'' = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ht1)
    subst ht''
    change ¬ (SystemToLTL.fsmTrace patternAlwaysAccept 0 f).holds 0 (.state 5)
    simp [SystemToLTL.fsmTrace, FSM.generateStateTrajectory, patternAlwaysAccept]

theorem biImpFails_naiveProgressUntil :
    SatisfactionWithoutHom
      ((SystemToLTL.fsmTrace patternAlwaysAccept 0 (fun _ => false)).models acceptUntil)
      (FSMIsIdentityHomomorphicImage pattern01110FSM patternAlwaysAccept) := by
  refine ⟨patternAlwaysAccept_satisfies_acceptUntil (fun _ => false), ?_⟩
  intro h
  exact patternAlwaysAccept_not_extEqual
    ((fsm_extEqual_iff_identityHom pattern01110FSM patternAlwaysAccept).2 h)

theorem candidate_tableProgressU_blocked :
    candidateVerdict .tableProgressU = .blocked := rfl

/-! ## A2: Path-compiled formula along word `01110` -/

/-- Nested next-state obligations along a concrete input word (X-chain). -/
def pathXChain {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ)
    (s0 : SZ) : List IZ → LTL (Atom SZ IZ OZ)
  | [] => LTL.atom (.state s0)
  | i :: rest =>
      LTL.and (LTL.atom (.state s0))
        (LTL.and (LTL.atom (.input i))
          (LTL.X (pathXChain F (F.NZ s0 i) rest)))

/-- The `01110` accepting path as an X-chain from state `0`. -/
def pattern01110_pathX : LTL (Atom MatchState Bit Bit) :=
  pathXChain pattern01110FSM 0 [false, true, true, true, false]

/-- Head of a nonempty path X-chain implies next-state atom when the remainder is empty;
    for nonempty remainder, the next formula's state conjunct holds. -/
theorem pathXChain_cons_next_state {SZ IZ OZ : Type}
    (F : FSMSystem SZ IZ OZ) (s0 : SZ) (i : IZ) (rest : List IZ)
    (σ : Trace (Atom SZ IZ OZ)) (t : Time)
    (h : satisfiesAt (pathXChain F s0 (i :: rest)) σ t) :
    satisfiesAt (pathXChain F (F.NZ s0 i) rest) σ (t + 1) := by
  simpa [pathXChain, satisfiesAt] using h.2.2

/-- Path encoding is not a full Φ_dyn substitute (wrong machine still differs on δ). -/
theorem path_encoding_no_global_compaction :
    ¬ FSMExtEqual pattern01110FSM patternAlwaysAccept :=
  patternAlwaysAccept_not_extEqual

theorem pathX_local_not_full_table :
    ¬ FSMIsIdentityHomomorphicImage pattern01110FSM patternAlwaysAccept := by
  intro h
  exact path_encoding_no_global_compaction
    ((fsm_extEqual_iff_identityHom pattern01110FSM patternAlwaysAccept).2 h)

/-! ## B1: Free `G(cmd → F(done))` (blocked) -/

/-- Free response: whenever input `0` is seen, eventually reach state `1`. -/
def freeResponse : LTL (Atom (Fin 2) (Fin 1) (Fin 1)) :=
  LTL.G (LTL.imp (LTL.atom (.input (0 : Fin 1)))
    (LTL.F (LTL.atom (.state (1 : Fin 2)))))

theorem fsmJump_satisfies_freeResponse (s0 : Fin 2) (f : ITZ (Fin 1)) :
    (SystemToLTL.fsmTrace fsmJump s0 f).models freeResponse := by
  intro t _ hIn
  refine ⟨t + 1, Nat.le_succ _, ?_⟩
  simp [satisfiesAt, SystemToLTL.fsmTrace, FSM.generateStateTrajectory_succ, fsmJump]

theorem biImpFails_freeResponse :
    SatisfactionWithoutHom
      ((SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models freeResponse)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump) :=
  ⟨fsmJump_satisfies_freeResponse 0 (fun _ => 0), fsmStay_jump_not_identityHom⟩

theorem candidate_freeResponse_blocked :
    candidateVerdict .freeMissionF = .blocked := rfl

/-! ## B2: Dynamics-tied `G(p → F(q))` (blocked as Φ substitute) -/

/-- Dynamics-tied response for one guided step of `F_spec`. -/
def dynamicsTiedResponse {SZ IZ OZ : Type} (F_spec : FSMSystem SZ IZ OZ)
    (s : SZ) (i : IZ) : LTL (Atom SZ IZ OZ) :=
  LTL.G (LTL.imp (LTL.and (LTL.atom (.state s)) (LTL.atom (.input i)))
    (LTL.F (LTL.atom (.state (F_spec.NZ s i)))))

/-- Toggle machine: not ext-equal to `fsmJump`, but hits state `1` within one step from `0`. -/
def fsmToggle : FSMSystem (Fin 2) (Fin 1) (Fin 1) where
  sz_nonempty := ⟨0⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => if s = 0 then 1 else 0
  RZ := sharedRZ

theorem fsmToggle_not_extEqual_jump :
    ¬ FSMExtEqual fsmJump fsmToggle := by
  intro ⟨_, hN⟩
  have := hN 1 0
  simp [fsmJump, fsmToggle] at this

/-- `fsmToggle` reaches state `1` now or on the next tick. -/
theorem fsmToggle_reaches_one (s0 : Fin 2) (f : ITZ (Fin 1)) (t : Nat) :
    ∃ t' ≥ t, (SystemToLTL.fsmTrace fsmToggle s0 f).holds t' (.state 1) := by
  by_cases h1 : FSM.generateStateTrajectory fsmToggle s0 f t = 1
  · exact ⟨t, le_rfl, by simpa [SystemToLTL.fsmTrace] using h1⟩
  · have h0 : FSM.generateStateTrajectory fsmToggle s0 f t = 0 := by
      apply Fin.eq_of_val_eq
      have hv := (FSM.generateStateTrajectory fsmToggle s0 f t).isLt
      have hne : (FSM.generateStateTrajectory fsmToggle s0 f t).val ≠ 1 := by
        intro hv1
        apply h1
        exact Fin.eq_of_val_eq hv1
      omega
    refine ⟨t + 1, Nat.le_succ _, ?_⟩
    change FSM.generateStateTrajectory fsmToggle s0 f (t + 1) = 1
    rw [FSM.generateStateTrajectory_succ, h0]
    simp [fsmToggle]

theorem fsmToggle_satisfies_dynTied_jump (s0 : Fin 2) (f : ITZ (Fin 1)) (s : Fin 2) (i : Fin 1) :
    (SystemToLTL.fsmTrace fsmToggle s0 f).models (dynamicsTiedResponse fsmJump s i) := by
  intro t _ _hp
  have hNZ : fsmJump.NZ s i = 1 := by simp [fsmJump]
  simp only [satisfiesAt, hNZ]
  exact fsmToggle_reaches_one s0 f t

theorem biImpFails_dynamicsTiedResponse :
    SatisfactionWithoutHom
      (∀ s i, (SystemToLTL.fsmTrace fsmToggle 0 (fun _ => 0)).models
        (dynamicsTiedResponse fsmJump s i))
      (FSMIsIdentityHomomorphicImage fsmJump fsmToggle) := by
  refine ⟨fun s i => fsmToggle_satisfies_dynTied_jump 0 (fun _ => 0) s i, ?_⟩
  intro h
  exact fsmToggle_not_extEqual_jump ((fsm_extEqual_iff_identityHom fsmJump fsmToggle).2 h)

theorem candidate_dynamicsResponse_blocked :
    candidateVerdict .dynamicsResponse = .blocked := rfl

/-! ## B3: Boundary positives — `G(p → X(q))` and `F≤1` -/

/-- Guided clause is exactly `G`-body `p → X(q)` for `q = NZ s i` (Φ_dyn sugar identity). -/
theorem guided_eq_p_imp_X_q {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ) (s : SZ) (i : IZ) :
    transitionClause F s i =
      LTL.imp (LTL.and (LTL.atom (.state s)) (LTL.atom (.input i)))
        (LTL.X (LTL.atom (.state (F.NZ s i)))) :=
  rfl

/-- If target atom is false now, `F≤1` iff `X`. -/
theorem FBounded1_eq_X_of_not_now {AP : Type} (σ : Trace AP) (t : Nat) (a : AP)
    (hNot : ¬ σ.holds t a) :
    satisfiesFBounded (LTL.atom a) σ t 1 ↔ satisfiesAt (LTL.X (LTL.atom a)) σ t := by
  rw [FBounded_one_unfold]
  constructor
  · intro h
    rcases h with h | h
    · simp [satisfiesAt] at h
      exact absurd h hNot
    · simpa [satisfiesAt] using h
  · intro h
    exact Or.inr (by simpa [satisfiesAt] using h)

theorem FBounded1_of_holds_now {AP : Type} (σ : Trace AP) (t : Nat) (a : AP)
    (hNow : σ.holds t a) :
    satisfiesFBounded (LTL.atom a) σ t 1 :=
  ⟨t, le_rfl, Nat.le_add_right _ _, by simpa [satisfiesAt] using hNow⟩

/-- Collapse: under `¬ holds t (state (NZ …))`, dynamics-tied `F≤1` matches `X`. -/
theorem dynamicsTied_FBounded1_collapses_to_X {SZ IZ OZ : Type}
    (F : FSMSystem SZ IZ OZ) (σ : Trace (Atom SZ IZ OZ)) (t : Nat) (s : SZ) (i : IZ)
    (hneq : ¬ σ.holds t (.state (F.NZ s i))) :
    satisfiesFBounded (LTL.atom (.state (F.NZ s i))) σ t 1 ↔
      satisfiesAt (LTL.X (LTL.atom (.state (F.NZ s i)))) σ t :=
  FBounded1_eq_X_of_not_now σ t _ hneq

/-- Exploration package for audits. -/
theorem u_response_exploration_summary :
    candidateVerdict .tableProgressU = .blocked ∧
      candidateVerdict .dynamicsResponse = .blocked ∧
      SatisfactionWithoutHom
        ((SystemToLTL.fsmTrace patternAlwaysAccept 0 (fun _ => false)).models acceptUntil)
        (FSMIsIdentityHomomorphicImage pattern01110FSM patternAlwaysAccept) ∧
      SatisfactionWithoutHom
        ((SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models freeResponse)
        (FSMIsIdentityHomomorphicImage fsmStay fsmJump) ∧
      ¬ FSMExtEqual pattern01110FSM patternAlwaysAccept :=
  ⟨rfl, rfl, biImpFails_naiveProgressUntil, biImpFails_freeResponse,
    path_encoding_no_global_compaction⟩

end DynamicsLivenessUResponse
