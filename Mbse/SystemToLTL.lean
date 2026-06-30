import Mbse.FiniteWymore
import Mbse.TemporalLogic
import Mathlib.Data.Finset.Basic

/-!
# Finite `FSMSystem` → propositional LTL (expressibility corollary)

**Scope:** finite state, input, and output spaces only (`Fintype` + `DecidableEq`).
Propositional LTL cannot express arbitrary infinite-state `DiscreteSystem`s.

Encodes transition and readout constraints as global (`G`) implications over atomic
state/input/output labels. Formula size is `O(|S|² · |I|)`; syntactic expressibility only.
-/

namespace SystemToLTL

open TemporalLogic FSM

variable {SZ IZ OZ : Type}
variable [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]

/-- Atomic propositions for finite Moore FSM traces. -/
inductive Atom (SZ IZ OZ : Type) where
  | state (s : SZ)
  | input (i : IZ)
  | output (o : OZ)

/-- Transition: in state `s` with input `i`, next tick is in state `NZ s i`. -/
def transitionClause (F : FSMSystem SZ IZ OZ) (s : SZ) (i : IZ) : LTL (Atom SZ IZ OZ) :=
  LTL.imp (LTL.and (LTL.atom (.state s)) (LTL.atom (.input i)))
    (LTL.X (LTL.atom (.state (F.NZ s i))))

/-- Readout: in state `s`, current output is `RZ s`. -/
def readoutClause (F : FSMSystem SZ IZ OZ) (s : SZ) : LTL (Atom SZ IZ OZ) :=
  LTL.imp (LTL.atom (.state s)) (LTL.atom (.output (F.RZ s)))

/-- Conjunction of a list of formulas. -/
def listAnd {AP : Type} (φs : List (LTL AP)) : LTL AP :=
  φs.foldr (fun ψ acc => LTL.and ψ acc) LTL.top

/-- All `(state, input)` transition clauses. -/
noncomputable def transitionClauses (F : FSMSystem SZ IZ OZ) : List (LTL (Atom SZ IZ OZ)) :=
  (Finset.univ : Finset SZ).toList.flatMap fun s =>
    (Finset.univ : Finset IZ).toList.map fun i => transitionClause F s i

/-- All readout clauses. -/
noncomputable def readoutClauses (F : FSMSystem SZ IZ OZ) : List (LTL (Atom SZ IZ OZ)) :=
  (Finset.univ : Finset SZ).toList.map fun s => readoutClause F s

/-- All transition clauses, globally. -/
noncomputable def transitionsGlobally (F : FSMSystem SZ IZ OZ) : LTL (Atom SZ IZ OZ) :=
  LTL.G (listAnd (transitionClauses F))

/-- All readout clauses, globally. -/
noncomputable def readoutsGlobally (F : FSMSystem SZ IZ OZ) : LTL (Atom SZ IZ OZ) :=
  LTL.G (listAnd (readoutClauses F))

/-- Compiled propositional LTL formula for finite Moore FSM `F`. -/
noncomputable def compileFSM (F : FSMSystem SZ IZ OZ) : LTL (Atom SZ IZ OZ) :=
  LTL.and (transitionsGlobally F) (readoutsGlobally F)

/-- Trace from FSM execution: label state, input, and output at each tick. -/
def fsmTrace (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : Trace (Atom SZ IZ OZ) where
  holds := fun t a =>
    match a with
    | .state s => generateStateTrajectory F s0 f t = s
    | .input i => f t = i
    | .output o => generateOutputTrajectory F s0 f t = some o

theorem satisfiesAt_listAnd {AP : Type} (φs : List (LTL AP)) (σ : Trace AP) (t : Time) :
    satisfiesAt (listAnd φs) σ t ↔ ∀ φ, φ ∈ φs → satisfiesAt φ σ t := by
  induction φs with
  | nil => simp [listAnd, satisfiesAt]
  | cons φ φs ih =>
    simp only [listAnd, List.foldr, satisfiesAt]
    constructor
    · rintro ⟨hφ, hrest⟩ ψ hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact hφ
      · exact ih.mp hrest ψ hmem'
    · intro h
      constructor
      · exact h φ (List.Mem.head _)
      · exact ih.mpr fun ψ hmem => h ψ (List.Mem.tail _ hmem)

theorem satisfiesAt_G {AP : Type} (φ : LTL AP) (σ : Trace AP) (t : Time) :
    satisfiesAt (LTL.G φ) σ t ↔ ∀ t', t ≤ t' → satisfiesAt φ σ t' := by
  simp [satisfiesAt]

theorem fsmTrace_satisfies_transitionClause (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ)
    (t : Time) (s : SZ) (i : IZ) :
    satisfiesAt (transitionClause F s i) (fsmTrace F s0 f) t := by
  simp only [satisfiesAt, transitionClause, fsmTrace]
  intro ⟨hs, hi⟩
  rw [FSM.generateStateTrajectory_succ, hs, hi]

theorem fsmTrace_satisfies_readoutClause (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ)
    (t : Time) (s : SZ) :
    satisfiesAt (readoutClause F s) (fsmTrace F s0 f) t := by
  simp only [satisfiesAt, readoutClause, fsmTrace]
  intro hs
  rw [FSM.generateOutputTrajectory_eq, hs]

theorem mem_transitionClauses_iff (F : FSMSystem SZ IZ OZ) (φ : LTL (Atom SZ IZ OZ)) :
    φ ∈ transitionClauses F ↔ ∃ s i, φ = transitionClause F s i := by
  constructor
  · intro h
    simp only [transitionClauses, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h
    rcases h with ⟨s, _, i, _, rfl⟩
    exact ⟨s, i, rfl⟩
  · intro ⟨s, i, heq⟩
    rw [heq]
    simp only [transitionClauses, List.mem_flatMap, List.mem_map, Finset.mem_toList]
    use s, Finset.mem_univ s, i, Finset.mem_univ i

theorem mem_readoutClauses_iff (F : FSMSystem SZ IZ OZ) (φ : LTL (Atom SZ IZ OZ)) :
    φ ∈ readoutClauses F ↔ ∃ s, φ = readoutClause F s := by
  constructor
  · intro h
    simp only [readoutClauses, List.mem_map, Finset.mem_toList] at h
    rcases h with ⟨s, _, rfl⟩
    exact ⟨s, rfl⟩
  · intro ⟨s, heq⟩
    rw [heq]
    simp only [readoutClauses, List.mem_map, Finset.mem_toList]
    use s, Finset.mem_univ s

theorem fsmTrace_models_transitionsGlobally (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    satisfiesAt (transitionsGlobally F) (fsmTrace F s0 f) 0 := by
  simp only [transitionsGlobally, satisfiesAt_G]
  intro t _
  rw [satisfiesAt_listAnd]
  intro φ hφ
  simp only [transitionClauses, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hφ
  rcases hφ with ⟨s, _, i, _, rfl⟩
  exact fsmTrace_satisfies_transitionClause F s0 f t s i

theorem fsmTrace_models_readoutsGlobally (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    satisfiesAt (readoutsGlobally F) (fsmTrace F s0 f) 0 := by
  simp only [readoutsGlobally, satisfiesAt_G]
  intro t _
  rw [satisfiesAt_listAnd]
  intro φ hφ
  simp only [readoutClauses, List.mem_map, Finset.mem_toList] at hφ
  rcases hφ with ⟨s, _, rfl⟩
  exact fsmTrace_satisfies_readoutClause F s0 f t s

/-- Canonical FSM execution trace satisfies the compiled LTL formula. -/
theorem fsm_trace_satisfies_compiled (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) :
    (fsmTrace F s0 f).models (compileFSM F) := by
  simp only [Trace.models, compileFSM, satisfiesAt]
  exact ⟨fsmTrace_models_transitionsGlobally F s0 f, fsmTrace_models_readoutsGlobally F s0 f⟩

/-- LTL atom for wrong state does not hold on canonical trace (negative test). -/
theorem fsmTrace_state_false {F : FSMSystem SZ IZ OZ} {s0 : SZ} {f : ITZ IZ} {t : Time}
    {s : SZ} (hne : generateStateTrajectory F s0 f t ≠ s) :
    ¬ (fsmTrace F s0 f).holds t (.state s) := by
  intro h
  exact hne (by simpa [fsmTrace] using h)

end SystemToLTL
