import Mbse.Wymore

/-!
# Labeled Transition Systems and Wymore Refinement (Level A → B)

**Buildability cotyledon — conceptual (Level A) to logical (Level B) bridge.**

- **Level A:** `LabeledTransitionSystem` — symmetric labeled transitions, nondeterminism allowed.
- **Level B:** `DiscreteSystem` — causal Wymore quintuple; embeddings `toSynLTSFrom` / `toIOLTSFrom`
  forget directionality into step labels.
- **Refinement:** `WymoreRefinement` / `TraceRefines` — concrete design traces are included in abstract LTS
  behaviors (via `ActionInterpretation`).

`StateEquiv` in [`Wymore`](Wymore.lean) is *observational output equivalence*, not classical LTS
bisimulation. This module introduces labeled-step semantics separately.

**Deferred (Level C):** technology systems, CPNs, timed automata, LTL model checking.
-/

namespace LTS

/-! ## Core LTS (Level A) -/

/--
  A labeled transition system `(S, Act, →)` with designated initial state.
  Transitions are given as a `Prop`-valued relation to allow nondeterminism without `Fintype`.
-/
structure LabeledTransitionSystem (S Act : Type) where
  s_nonempty : Nonempty S
  initial : S
  trans : S → Act → S → Prop

variable {S Act : Type} (L : LabeledTransitionSystem S Act)

/-- A single labeled step. -/
def Step (s : S) (a : Act) (s' : S) : Prop :=
  L.trans s a s'

/-- There exists a successor along action `a`. -/
def HasSuccessor (s : S) (a : Act) : Prop :=
  ∃ s', Step L s a s'

/-- Inductive trace (action word) starting from state `s`. -/
inductive Behav (L : LabeledTransitionSystem S Act) : S → List Act → Prop
  | nil (s : S) : Behav L s []
  | cons (s s' : S) (a : Act) (w : List Act)
      (h_step : Step L s a s') (h_rest : Behav L s' w) : Behav L s (a :: w)

/-- Behav from `s` along `w` ending at `s'`. -/
inductive BehavTo (L : LabeledTransitionSystem S Act) : S → List Act → S → Prop
  | nil (s : S) : BehavTo L s [] s
  | cons (s s' s'' : S) (a : Act) (w : List Act)
      (h_step : Step L s a s') (h_rest : BehavTo L s' w s'') : BehavTo L s (a :: w) s''

/-- State `s` is reachable from the LTS initial state. -/
def ReachableState (s : S) : Prop :=
  ∃ w, BehavTo L L.initial w s

/-- Set of action words emitted from the initial state (language). -/
def Language : Set (List Act) :=
  { w | ∃ s, BehavTo L L.initial w s }

/-- At most one successor per `(state, action)` pair. -/
def IsDeterministic : Prop :=
  ∀ (s : S) (a : Act) (s' s'' : S), Step L s a s' → Step L s a s'' → s' = s''

theorem ltsBehav_nil (s : S) : Behav L s [] :=
  Behav.nil s

theorem ltsBehavTo_nil (s : S) : BehavTo L s [] s :=
  BehavTo.nil s

theorem ltsBehavTo_cons (s s' s'' : S) (a : Act) (w : List Act)
    (h_step : Step L s a s') (h_rest : BehavTo L s' w s'') :
    BehavTo L s (a :: w) s'' :=
  BehavTo.cons s s' s'' a w h_step h_rest

theorem trace_of_traceTo (s s' : S) (w : List Act) (h : BehavTo L s w s') : Behav L s w := by
  induction h with
  | nil s => exact Behav.nil (L := L) s
  | cons s sMid sEnd a w hStep hRest ih => exact Behav.cons s sMid a w hStep ih

theorem reachable_initial : ReachableState L L.initial :=
  ⟨[], BehavTo.nil (L := L) L.initial⟩

/-! ## I/O automaton labels -/

/--
  Interleaved Moore observation and environment input labels.
  `epsilon` marks an autonomous (`none` input) step.
-/
inductive IOLabel (I O : Type)
  | observe (o : O)
  | input (i : I)
  | epsilon

/-! ## Synchronous step labels (Level B view) -/

/--
  One discrete-time tick: optional input applied and optional output observed at the pre-step state
  (Moore readout), matching `generateStateTrajectory` / `generateOutputTrajectory`.
-/
structure SynStep (I O : Type) where
  inp : Option I
  out : Option O

namespace SynStep

variable {I O : Type}

theorem ext (a b : SynStep I O) (h_inp : a.inp = b.inp) (h_out : a.out = b.out) : a = b := by
  rcases a with ⟨ai, ao⟩
  rcases b with ⟨bi, bo⟩
  simp only [SynStep.mk.injEq]
  exact ⟨h_inp, h_out⟩

/-- Build the synchronous label for one trajectory tick. -/
def ofTick (oi : Option I) (oo : Option O) : SynStep I O :=
  ⟨oi, oo⟩

/-- Expand one synchronous tick into an interleaved I/O label list (observe before input). -/
def toIOTick (lbl : SynStep I O) : List (IOLabel I O) :=
  let obs := lbl.out.map fun o => IOLabel.observe o
  let inp := match lbl.inp with
    | some i => [IOLabel.input i]
    | none => [IOLabel.epsilon]
  obs.toList ++ inp

end SynStep

/-! ## Wymore → synchronous / I/O LTS -/

namespace DiscreteSystem

variable {SZ IZ OZ : Type}

/--
  Forgetful LTS view of a Wymore system: each edge is labeled by the synchronous pair
  `(input at tick, output at pre-step state)`.
-/
def toSynLTSFrom (s0 : SZ) (Z : _root_.DiscreteSystem SZ IZ OZ) :
    LabeledTransitionSystem SZ (SynStep IZ OZ) where
  s_nonempty := Z.sz_nonempty
  initial := s0
  trans s lbl s' :=
    Z.RZ s = lbl.out ∧ Z.NZ s lbl.inp = s'

theorem synLTS_step_iff (s0 : SZ) (Z : _root_.DiscreteSystem SZ IZ OZ)
    (s : SZ) (lbl : SynStep IZ OZ) (s' : SZ)
    (h : Step (toSynLTSFrom s0 Z) s lbl s') :
    Z.RZ s = lbl.out ∧ Z.NZ s lbl.inp = s' :=
  h

theorem synLTS_deterministic (s0 : SZ) (Z : _root_.DiscreteSystem SZ IZ OZ) :
    IsDeterministic (toSynLTSFrom s0 Z) := by
  intro s a s' s'' h1 h2
  exact h1.2.symm.trans h2.2

/-- Inductive synchronous trace matching Wymore step semantics from `s`. -/
inductive SynTraceFrom (Z : _root_.DiscreteSystem SZ IZ OZ) : SZ → List (SynStep IZ OZ) → Prop
  | nil (s : SZ) : SynTraceFrom Z s []
  | cons (s s' : SZ) (lbl : SynStep IZ OZ) (w : List (SynStep IZ OZ))
      (h_out : Z.RZ s = lbl.out) (h_step : Z.NZ s lbl.inp = s')
      (h_rest : SynTraceFrom Z s' w) :
      SynTraceFrom Z s (lbl :: w)

theorem synTraceFrom_nil (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) :
    SynTraceFrom Z s [] :=
  SynTraceFrom.nil s

/-- Synchronous trace along an `ITZW` input stream for `n` steps. -/
def synTraceOfTrajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat) (f : ITZW IZ) :
    List (SynStep IZ OZ) :=
  (List.range n).map fun t =>
    SynStep.ofTick (f t) (Z.RZ (generateStateTrajectory Z s0 f t))

/-- End state after a synchronous trace. -/
def synTraceEndState (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) : List (SynStep IZ OZ) → SZ
  | [] => s
  | lbl :: w => synTraceEndState Z (Z.NZ s lbl.inp) w

theorem synTraceFrom_append (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (w w' : List (SynStep IZ OZ)) (h1 : SynTraceFrom Z s w)
    (h2 : SynTraceFrom Z (synTraceEndState Z s w) w') :
    SynTraceFrom Z s (w ++ w') := by
  induction h1 with
  | nil =>
    simpa [synTraceEndState] using h2
  | cons s s' lbl w h_out h_step h_rest ih =>
    apply SynTraceFrom.cons s s' lbl (w ++ w') h_out h_step
    have hs : synTraceEndState Z s (lbl :: w) = synTraceEndState Z s' w := by
      simp [synTraceEndState, h_step]
    rw [hs] at h2
    exact ih h2

theorem synTraceEndState_append_singleton (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (w : List (SynStep IZ OZ)) (lbl : SynStep IZ OZ) :
    synTraceEndState Z s (w ++ [lbl]) = Z.NZ (synTraceEndState Z s w) lbl.inp := by
  induction w generalizing s with
  | nil => rfl
  | cons lbl' w ih =>
    dsimp [synTraceEndState]
    exact ih (Z.NZ s lbl'.inp)

theorem synTraceOfTrajectory_succ (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    synTraceOfTrajectory Z s0 (n + 1) f =
      synTraceOfTrajectory Z s0 n f ++
        [SynStep.ofTick (f n) (Z.RZ (generateStateTrajectory Z s0 f n))] := by
  dsimp [synTraceOfTrajectory]
  rw [List.range_succ, List.map_append, List.map_singleton]

theorem synTraceEndState_eq_trajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    synTraceEndState Z s0 (synTraceOfTrajectory Z s0 n f) =
      generateStateTrajectory Z s0 f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [synTraceOfTrajectory_succ, synTraceEndState_append_singleton, ih, generateStateTrajectory_succ]
    simp [SynStep.ofTick]

theorem synTraceFrom_of_trajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    SynTraceFrom Z s0 (synTraceOfTrajectory Z s0 n f) := by
  induction n with
  | zero => exact synTraceFrom_nil Z s0
  | succ n ih =>
    rw [synTraceOfTrajectory_succ]
    apply synTraceFrom_append Z s0 _ _ ih
    rw [synTraceEndState_eq_trajectory Z s0 n f]
    have hstep := (generateStateTrajectory_succ Z s0 f n).symm
    refine SynTraceFrom.cons _ _ _ _ rfl hstep (synTraceFrom_nil Z _)

theorem synLTS_trace_of_synTraceFrom (s0 : SZ) (Z : _root_.DiscreteSystem SZ IZ OZ)
    (s : SZ) (w : List (SynStep IZ OZ)) (h : SynTraceFrom Z s w) :
    Behav (toSynLTSFrom s0 Z) s w := by
  induction h with
  | nil s => exact Behav.nil (L := toSynLTSFrom s0 Z) s
  | cons s s' lbl w h_out h_step h_rest ih =>
    apply Behav.cons s s' lbl w _ ih
    exact ⟨h_out, h_step⟩

/--
  I/O automaton view: `observe o` stutters at `s` when `RZ s = some o`;
  `input i` moves via `NZ s (some i)`; `epsilon` moves via `NZ s none`.
-/
def toIOLTSFrom (s0 : SZ) (Z : _root_.DiscreteSystem SZ IZ OZ) :
    LabeledTransitionSystem SZ (IOLabel IZ OZ) where
  s_nonempty := Z.sz_nonempty
  initial := s0
  trans := fun s =>
    fun
    | IOLabel.observe o, s' => s' = s ∧ Z.RZ s = some o
    | IOLabel.input i, s' => Z.NZ s (some i) = s'
    | IOLabel.epsilon, s' => Z.NZ s none = s'

/-- I/O LTS view; initial state is arbitrary since `trans` does not depend on it. -/
noncomputable def ioLTS (Z : _root_.DiscreteSystem SZ IZ OZ) :
    LabeledTransitionSystem SZ (IOLabel IZ OZ) :=
  toIOLTSFrom (Nonempty.some Z.sz_nonempty) Z

/-- Interleaved I/O trace matching Wymore step semantics. -/
inductive IOTraceFrom (Z : _root_.DiscreteSystem SZ IZ OZ) : SZ → List (IOLabel IZ OZ) → Prop
  | nil (s : SZ) : IOTraceFrom Z s []
  | cons (s s' : SZ) (a : IOLabel IZ OZ) (w : List (IOLabel IZ OZ))
      (h_step : Step (ioLTS Z) s a s') (h_rest : IOTraceFrom Z s' w) :
      IOTraceFrom Z s (a :: w)

theorem ioTraceFrom_nil (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) :
    IOTraceFrom Z s [] :=
  IOTraceFrom.nil s

/-- I/O trace from an `ITZW` stream for `n` synchronous ticks. -/
def ioTraceOfTrajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat) (f : ITZW IZ) :
    List (IOLabel IZ OZ) :=
  (List.range n).flatMap fun t =>
    (SynStep.ofTick (f t) (Z.RZ (generateStateTrajectory Z s0 f t))).toIOTick

theorem ioTraceOf_eq_flatMap_syn (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    ioTraceOfTrajectory Z s0 n f =
      (synTraceOfTrajectory Z s0 n f).flatMap SynStep.toIOTick := by
  dsimp [ioTraceOfTrajectory, synTraceOfTrajectory]
  rw [List.flatMap_map]

theorem ioTraceOfTrajectory_succ (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    ioTraceOfTrajectory Z s0 (n + 1) f =
      ioTraceOfTrajectory Z s0 n f ++
        (SynStep.ofTick (f n) (Z.RZ (generateStateTrajectory Z s0 f n))).toIOTick := by
  dsimp [ioTraceOfTrajectory, synTraceOfTrajectory]
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Successor state after one I/O label step. -/
def ioTraceEndState (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) : IOLabel IZ OZ → SZ
  | IOLabel.observe _ => s
  | IOLabel.input i => Z.NZ s (some i)
  | IOLabel.epsilon => Z.NZ s none

/-- End state after an interleaved I/O label list. -/
def ioTraceEndStateList (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) :
    List (IOLabel IZ OZ) → SZ
  | [] => s
  | a :: w => ioTraceEndStateList Z (ioTraceEndState Z s a) w

theorem ioTraceEndStateList_nil (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ) :
    ioTraceEndStateList Z s [] = s := rfl

theorem ioTraceEndStateList_cons (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (a : IOLabel IZ OZ) (w : List (IOLabel IZ OZ)) :
    ioTraceEndStateList Z s (a :: w) =
      ioTraceEndStateList Z (ioTraceEndState Z s a) w := rfl

theorem ioTraceEndStateList_append (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (w w' : List (IOLabel IZ OZ)) :
    ioTraceEndStateList Z s (w ++ w') =
      ioTraceEndStateList Z (ioTraceEndStateList Z s w) w' := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp [ioTraceEndStateList, ih]

theorem ioTraceStep_endState (Z : _root_.DiscreteSystem SZ IZ OZ) (s s' : SZ) (a : IOLabel IZ OZ)
    (h : Step (ioLTS Z) s a s') : ioTraceEndState Z s a = s' := by
  cases a <;> dsimp [ioLTS, toIOLTSFrom, Step, ioTraceEndState] at h ⊢ <;>
    (rcases h with ⟨rfl, _⟩ | h | h) <;> rfl

theorem ioTraceEndStateList_synTick (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (oi : Option IZ) (o : OZ) :
    ioTraceEndStateList Z s (SynStep.ofTick oi (some o)).toIOTick = Z.NZ s oi := by
  cases oi <;> simp [ioTraceEndStateList, ioTraceEndState, SynStep.toIOTick, SynStep.ofTick]

theorem ioTraceEndStateList_trajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (s0 : SZ) (n : Nat) (f : ITZW IZ) :
    ioTraceEndStateList Z s0 (ioTraceOfTrajectory Z s0 n f) =
      synTraceEndState Z s0 (synTraceOfTrajectory Z s0 n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨o, ho⟩ := hOut (generateStateTrajectory Z s0 f n)
    rw [ioTraceOfTrajectory_succ, synTraceOfTrajectory_succ, ioTraceEndStateList_append, ih,
        synTraceEndState_append_singleton, ho]
    exact ioTraceEndStateList_synTick Z _ (f n) o

theorem ioTraceFrom_of_synCons (Z : _root_.DiscreteSystem SZ IZ OZ) (s s' : SZ)
    (lbl : SynStep IZ OZ) (w : List (SynStep IZ OZ))
    (h_out : Z.RZ s = lbl.out) (h_step : Z.NZ s lbl.inp = s')
    (h_rest : IOTraceFrom Z s' (w.flatMap SynStep.toIOTick)) :
    IOTraceFrom Z s (lbl.toIOTick ++ w.flatMap SynStep.toIOTick) := by
  match lbl with
  | { inp := none, out := none } =>
    have h_eps : Step (ioLTS Z) s IOLabel.epsilon s' := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact h_step
    simpa [SynStep.toIOTick, Option.map_none, List.nil_append] using
      IOTraceFrom.cons s s' IOLabel.epsilon (w.flatMap SynStep.toIOTick) h_eps h_rest
  | { inp := some i, out := none } =>
    have h_inp : Step (ioLTS Z) s (IOLabel.input i) s' := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact h_step
    simpa [SynStep.toIOTick, Option.map_none, List.nil_append] using
      IOTraceFrom.cons s s' (IOLabel.input i) (w.flatMap SynStep.toIOTick) h_inp h_rest
  | { inp := none, out := some o } =>
    have h_obs : Step (ioLTS Z) s (IOLabel.observe o) s := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact ⟨rfl, h_out⟩
    have h_eps : Step (ioLTS Z) s IOLabel.epsilon s' := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact h_step
    simpa [SynStep.toIOTick, Option.map_some, List.singleton_append] using
      IOTraceFrom.cons s s (IOLabel.observe o)
        (IOLabel.epsilon :: w.flatMap SynStep.toIOTick) h_obs
        (IOTraceFrom.cons s s' IOLabel.epsilon (w.flatMap SynStep.toIOTick) h_eps h_rest)
  | { inp := some i, out := some o } =>
    have h_obs : Step (ioLTS Z) s (IOLabel.observe o) s := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact ⟨rfl, h_out⟩
    have h_inp : Step (ioLTS Z) s (IOLabel.input i) s' := by
      dsimp [ioLTS, toIOLTSFrom, Step]; exact h_step
    simpa [SynStep.toIOTick, Option.map_some, List.singleton_append] using
      IOTraceFrom.cons s s (IOLabel.observe o)
        (IOLabel.input i :: w.flatMap SynStep.toIOTick) h_obs
        (IOTraceFrom.cons s s' (IOLabel.input i) (w.flatMap SynStep.toIOTick) h_inp h_rest)

theorem ioTraceFrom_of_synTraceFrom (Z : _root_.DiscreteSystem SZ IZ OZ) (s : SZ)
    (w : List (SynStep IZ OZ)) (h : SynTraceFrom Z s w) :
    IOTraceFrom Z s (w.flatMap SynStep.toIOTick) := by
  induction h with
  | nil s => exact ioTraceFrom_nil Z s
  | cons s s' lbl w h_out h_step h_rest ih =>
    dsimp at ih ⊢
    exact ioTraceFrom_of_synCons Z s s' lbl w h_out h_step ih

theorem ioTraceFrom_of_trajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) (n : Nat)
    (f : ITZW IZ) :
    IOTraceFrom Z s0 (ioTraceOfTrajectory Z s0 n f) := by
  rw [ioTraceOf_eq_flatMap_syn]
  exact ioTraceFrom_of_synTraceFrom Z s0 _ (synTraceFrom_of_trajectory Z s0 n f)

theorem synTraceFrom_of_ioTrajectory (Z : _root_.DiscreteSystem SZ IZ OZ) (_hOut : AlwaysOutputs Z)
    (s0 : SZ) (n : Nat) (f : ITZW IZ) (_h : IOTraceFrom Z s0 (ioTraceOfTrajectory Z s0 n f)) :
    SynTraceFrom Z s0 (synTraceOfTrajectory Z s0 n f) :=
  synTraceFrom_of_trajectory Z s0 n f

theorem syn_trace_iff_io_trace (Z : _root_.DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (s0 : SZ) (n : Nat) (f : ITZW IZ) :
    SynTraceFrom Z s0 (synTraceOfTrajectory Z s0 n f) ↔
      IOTraceFrom Z s0 (ioTraceOfTrajectory Z s0 n f) := by
  constructor
  · intro h
    rw [ioTraceOf_eq_flatMap_syn]
    exact ioTraceFrom_of_synTraceFrom Z s0 _ h
  · intro h
    exact synTraceFrom_of_ioTrajectory Z hOut s0 n f h

end DiscreteSystem

/-! ## Refinement (Level A spec ⊇ Level B design) -/

/-- Map synchronous Wymore ticks into abstract LTS action labels. -/
structure ActionInterpretation (Act I O : Type) where
  synToAct : SynStep I O → Act

/--
  Simulation-style refinement: abstract LTS steps simulate concrete Wymore ticks
  under `stateRel` and `interp`.
-/
structure WymoreRefinement (S Act : Type) (L : LabeledTransitionSystem S Act)
    (SZ IZ OZ : Type) (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ) where
  interp : ActionInterpretation Act IZ OZ
  stateRel : S → SZ → Prop
  init_related : stateRel L.initial s0
  step_sim :
    ∀ {s sz lbl sz'},
      stateRel s sz →
      Z.RZ sz = lbl.out →
      Z.NZ sz lbl.inp = sz' →
      ∃ s', stateRel s' sz' ∧ Step L s (interp.synToAct lbl) s'

/--
  Trace inclusion: every concrete synchronous trace maps to an abstract LTS behavior
  from some reachable abstract state.
-/
def TraceRefines {S Act SZ IZ OZ : Type}
    (L : LabeledTransitionSystem S Act) (Z : _root_.DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (interp : ActionInterpretation Act IZ OZ) : Prop :=
  ∀ (w : List (SynStep IZ OZ)),
    DiscreteSystem.SynTraceFrom Z s0 w →
      ∃ s, ReachableState L s ∧ Behav L s (w.map interp.synToAct)

theorem wymoreRefinement_traceRefines {S Act SZ IZ OZ : Type}
    (L : LabeledTransitionSystem S Act) (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (R : WymoreRefinement S Act L SZ IZ OZ Z s0) :
    TraceRefines L Z s0 R.interp := by
  intro w h
  have hBeh : Behav L L.initial (w.map R.interp.synToAct) := by
    suffices ∀ (sz : SZ) (ws : List (SynStep IZ OZ)) (hSyn : DiscreteSystem.SynTraceFrom Z sz ws)
        (s_abs : S) (hRel_abs : R.stateRel s_abs sz),
        Behav L s_abs (ws.map R.interp.synToAct) by
      exact this s0 w h L.initial R.init_related
    intro sz ws hSyn s_abs hRel_abs
    induction hSyn generalizing s_abs with
    | nil _ =>
      exact ltsBehav_nil (L := L) s_abs
    | cons s s' lbl w' h_out h_step h_rest ih =>
      obtain ⟨s_a', hRel', hStep⟩ := R.step_sim hRel_abs h_out h_step
      exact Behav.cons s_abs s_a' (R.interp.synToAct lbl) (w'.map R.interp.synToAct) hStep
        (ih s_a' hRel')
  refine ⟨L.initial, reachable_initial L, hBeh⟩

/-! ## Worked examples -/

namespace Examples

/-- Toggle machine as a deterministic synchronous LTS. -/
def toggleSynLTS (s0 : Bool) : LabeledTransitionSystem Bool (SynStep Empty Bool) :=
  DiscreteSystem.toSynLTSFrom s0 toggleSystem

theorem toggleSynLTS_deterministic (s0 : Bool) :
    IsDeterministic (toggleSynLTS s0) :=
  DiscreteSystem.synLTS_deterministic s0 toggleSystem

theorem toggleSynLTS_period_two (s0 : Bool) (f : ITZW Empty) :
    BehavTo (toggleSynLTS s0) s0
      [SynStep.ofTick (f 0) (some s0), SynStep.ofTick (f 1) (some !s0)] s0 := by
  have h1 : Step (toggleSynLTS s0) s0 (SynStep.ofTick (f 0) (some s0)) !s0 := by
    dsimp [toggleSynLTS, Step, DiscreteSystem.toSynLTSFrom, toggleSystem]
    exact ⟨rfl, rfl⟩
  have h2 : Step (toggleSynLTS s0) (!s0) (SynStep.ofTick (f 1) (some (!s0))) s0 := by
    dsimp [toggleSynLTS, Step, DiscreteSystem.toSynLTSFrom, toggleSystem]
    rcases s0 with _ | _
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  exact BehavTo.cons s0 (!s0) s0 (SynStep.ofTick (f 0) (some s0))
    [SynStep.ofTick (f 1) (some (!s0))] h1
    (BehavTo.cons (!s0) s0 s0 (SynStep.ofTick (f 1) (some (!s0))) [] h2 (BehavTo.nil s0))

/-- Tiny nondeterministic abstract spec: `A` has two distinct `()`-successors. -/
inductive NondetState
  | A
  | B

def nondetSpec : LabeledTransitionSystem NondetState Unit where
  s_nonempty := ⟨NondetState.A⟩
  initial := NondetState.A
  trans := fun s _ s' =>
    s = NondetState.A ∧ (s' = NondetState.A ∨ s' = NondetState.B)

theorem nondetSpec_not_deterministic : ¬ IsDeterministic nondetSpec := by
  intro h
  have hA : Step nondetSpec NondetState.A () NondetState.A :=
    ⟨rfl, Or.inl rfl⟩
  have hB : Step nondetSpec NondetState.A () NondetState.B :=
    ⟨rfl, Or.inr rfl⟩
  exact NondetState.noConfusion (h NondetState.A () NondetState.A NondetState.B hA hB)

/-- Abstract spec with no transitions — toggle's one-step trace is not included. -/
def forbidSpec : LabeledTransitionSystem Unit Unit where
  s_nonempty := ⟨()⟩
  initial := ()
  trans := fun _ _ _ => False

/-- Collapse all synchronous ticks to `()`; toggle does not refine the empty spec. -/
def unitInterp : ActionInterpretation Unit Empty Bool :=
  { synToAct := fun _ => () }

theorem toggle_not_refines_forbid (s0 : Bool) :
    ¬ TraceRefines forbidSpec toggleSystem s0 unitInterp := by
  intro h
  have htrace : DiscreteSystem.SynTraceFrom toggleSystem s0
      [SynStep.ofTick (none : Option Empty) (some s0)] :=
    DiscreteSystem.SynTraceFrom.cons s0 (!s0)
      (SynStep.ofTick (none : Option Empty) (some s0)) [] rfl rfl
      (DiscreteSystem.SynTraceFrom.nil (!s0))
  rcases h _ htrace with ⟨_, _, hbeh⟩
  cases hbeh with
  | cons _ _ _ _ hstep _ =>
    dsimp [forbidSpec, Step] at hstep

/-- Universal self-loops on all synchronous labels refine any open Moore system. -/
def trivialSpec (I O : Type) : LabeledTransitionSystem Unit (SynStep I O) where
  s_nonempty := ⟨()⟩
  initial := ()
  trans := fun _ _ _ => True

def identityInterp {I O : Type} : ActionInterpretation (SynStep I O) I O :=
  { synToAct := id }

theorem trivial_refinement {SZ IZ OZ : Type} (Z : _root_.DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (_hOut : AlwaysOutputs Z) :
    TraceRefines (trivialSpec IZ OZ) Z s0 (@identityInterp IZ OZ) := by
  intro w h
  refine ⟨(), reachable_initial _, ?_⟩
  induction h with
  | nil _ =>
    exact ltsBehav_nil (L := trivialSpec IZ OZ) ()
  | cons _ _ lbl w' _ _ h_rest ih =>
    apply Behav.cons () () lbl (w'.map id) _ ih
    trivial

end Examples

end LTS
