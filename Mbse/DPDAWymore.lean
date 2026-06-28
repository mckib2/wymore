import Mbse.Wymore
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Deterministic Pushdown Automaton (DPDA) Wymore Systems

This file implements a DPDA-augmented version of Wayne Wymore's T3SD framework.
It upgrades the state space to a structured memory space (Control State × LIFO Stack),
allowing the formalization of context-free behaviors while maintaining compatibility
with Wymore's trajectory-matching philosophy.

## Formal model

We formalize the 7-tuple: ZDPDA = (S, P, STfin, Γ, z0, FDPDA, GDPDA)
where S/P define input/output spaces, STfin is the finite control states,
Γ is the LIFO stack alphabet, z0 is the empty-stack baseline marker, and F/G are the
stack-aware transition and readout functions.

The transition function `F` is *partial* (returns `Option`). This lets us express the genuine
determinism condition of a DPDA (`IsDeterministic`: no conflict between an ε-move and an
input-consuming move at a given control state and stack top), rather than treating determinism
as a free consequence of `F` being a total function. We additionally give a finite-word
acceptance relation (`Reaches`) and the recognized `Language`, and a bounded-stack reduction to
Wymore's `DiscreteSystem` with a proved behavioral-equivalence theorem (valid while the stack
stays within the bound).

## Coverage summary

**Implemented:** 7-tuple spec, snapshot trajectories, soundness/uniqueness, `IsDeterministic`,
`Reaches` / `Language` (final-state acceptance), `toBoundedDiscreteSystem` +
`bounded_output_agrees`.

**Intentionally omitted** (see [formalization_roadmap.md](../formalization_roadmap.md) §3):
Wymore open/closed/finite classification, reachability, state equivalence, morphisms,
time invariance / nonanticipation, ports, parameterization, Ch. 3 coupling, worked examples.

## Integration with other modules

- **Base [Wymore](Wymore.lean):** `toBoundedDiscreteSystem` maps a depth-bounded DPDA into
  `DiscreteSystem (Q × BoundedStack Γ max_depth) (Option I) O`. Unbounded stacks cannot live in
  `DiscreteSystem` directly because it requires `Fintype SZ`.
- **[GeneralizedWymore](GeneralizedWymore.lean):** Both use `Time → Option IS` input streams
  (`ITZ_opt` here, `ITZW` there). Unification is deferred to the roadmap.

## Semantic caveats

- **`stepSnapshot` halt-on-`none`:** When `F` is undefined, the machine self-loops (stays in place).
  Trajectories remain total; this is not a rejecting halt.
- **`peek` on empty stack:** Returns `z0`, so `[]` and `[z0]` are indistinguishable at the top.
  Classic DPDAs avoid this by never popping the bottom marker. A formal `WellFormedStack`
  invariant is on the roadmap.
- **`Language` acceptance mode:** By **final control state**, not by empty stack.
- **Bounded reduction:** Beyond `max_depth`, `List.take` truncation is **lossy** unless
  `bounded_output_agrees`'s depth hypothesis holds.

See [formalization_roadmap.md](../formalization_roadmap.md) for backlog and
[formalization_roadmap.md §6](formalization_roadmap.md#6-rigor-verification) for the proof-honesty checklist.
-/

namespace DPDA

/--
  A Deterministic Pushdown Automaton (DPDA) system within the Wymore framework.
  It is defined as a 7-tuple: ZDPDA = (S, P, STfin, Γ, z0, FDPDA, GDPDA)
-/
structure DPDASystem (STfin : Type) (IS : Type) (OZ : Type) (Γ : Type) where
  /-- Proof that the control state space is nonempty -/
  st_nonempty : Nonempty STfin

  /-- Proof that the control state space is finite -/
  st_finite : Fintype STfin

  /-- Proof that the input space is finite -/
  iz_finite : Fintype IS

  /-- Proof that the output space is finite -/
  oz_finite : Fintype OZ

  /-- Proof that the stack alphabet is finite -/
  gamma_finite : Fintype Γ

  /-- Decidable equality on control states -/
  st_decidable : DecidableEq STfin

  /-- Decidable equality on stack alphabet -/
  gamma_decidable : DecidableEq Γ

  /-- The initial stack symbol (baseline empty condition) -/
  z0 : Γ

  /--
    The Stack-Aware Transition Function: FDPDA : STfin → Option IS → Γ → Option (STfin × List Γ).
    Takes the current control mode, an input segment (or ε represented as `none`),
    and peeks at the top token of the stack. Returns `none` when no move is defined
    (the machine is stuck), or `some (next mode, tokens to push back onto the stack)`.
  -/
  F : STfin → Option IS → Γ → Option (STfin × List Γ)

  /-- The Memory-Augmented Readout Function: GDPDA : STfin → Γ → OZ -/
  G : STfin → Γ → OZ

variable {STfin IS OZ Γ : Type}

/-- The stack of the DPDA is represented as a List of Γ. -/
def Stack (Γ : Type) := List Γ

/-- An operational snapshot (instantaneous description) of the DPDA. -/
def Snapshot (STfin Γ : Type) := STfin × Stack Γ

/-- Helper function to peek at the top of the stack. If the stack is empty, it returns the
    default `z0`. Note: this convention means that once the base marker is popped, an empty
    stack is indistinguishable from a stack with `z0` on top; classic textbook DPDAs avoid this
    by never popping the bottom marker (see `IsDeterministic` discussion and the report). -/
def peek (z0 : Γ) : Stack Γ → Γ
  | [] => z0
  | z :: _ => z

/-- Helper function to update the stack by replacing the popped top element with a list of new
    elements. -/
def updateStack (s : Stack Γ) (new_top : List Γ) : Stack Γ :=
  match s with
  | [] => new_top
  | _ :: rest => new_top ++ rest

/-- Input trajectory over Option IS (interleaved event/epsilon stream). -/
abbrev ITZ_opt (IS : Type) := Time → Option IS

/--
  One synchronous step of the snapshot. If the transition function is undefined (`none`) the
  machine *halts in place* (self-loop), which keeps the snapshot trajectory total while still
  reflecting the partiality of `F`.
-/
def stepSnapshot (D : DPDASystem STfin IS OZ Γ) (snap : Snapshot STfin Γ) (input : Option IS) :
    Snapshot STfin Γ :=
  match snap with
  | (q, s) =>
    match D.F q input (peek D.z0 s) with
    | none => (q, s)
    | some (q', new_top) => (q', updateStack s new_top)

/-- Generates the snapshot trajectory (state trajectory) of the DPDA. -/
def generateStateTrajectory (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    Time → Snapshot STfin Γ
  | 0 => (q0, [D.z0])
  | t + 1 => stepSnapshot D (generateStateTrajectory D q0 f t) (f t)

/-- Generates the output trajectory of the DPDA. -/
def generateOutputTrajectory (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    Time → OZ :=
  fun t =>
    let (q, s) := generateStateTrajectory D q0 f t
    D.G q (peek D.z0 s)

/-- Predicate for a valid state trajectory. -/
def IsValidStateTrajectory (D : DPDASystem STfin IS OZ Γ) (f : ITZ_opt IS)
    (g : Time → Snapshot STfin Γ) : Prop :=
  ∀ t : Time, g (t + 1) = stepSnapshot D (g t) (f t)

/-- Predicate for a valid output trajectory. -/
def IsValidOutputTrajectory (D : DPDASystem STfin IS OZ Γ) (g : Time → Snapshot STfin Γ)
    (h : Time → OZ) : Prop :=
  ∀ t : Time,
    let (q, s) := g t
    h t = D.G q (peek D.z0 s)

/-! ## Simp Lemmas -/

@[simp]
theorem generateStateTrajectory_zero (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    generateStateTrajectory D q0 f 0 = (q0, [D.z0]) := rfl

@[simp]
theorem generateStateTrajectory_succ (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS)
    (t : Time) :
    generateStateTrajectory D q0 f (t + 1) =
      stepSnapshot D (generateStateTrajectory D q0 f t) (f t) := rfl

/-! ## Soundness and Uniqueness Theorems -/

theorem generateStateTrajectory_valid (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    IsValidStateTrajectory D f (generateStateTrajectory D q0 f) := by
  intro t
  rfl

theorem generateOutputTrajectory_valid (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    IsValidOutputTrajectory D (generateStateTrajectory D q0 f) (generateOutputTrajectory D q0 f) := by
  intro t
  rfl

theorem stateTrajectory_unique (D : DPDASystem STfin IS OZ Γ) (f : ITZ_opt IS)
    (g : Time → Snapshot STfin Γ) (q0 : STfin)
    (h_init : g 0 = (q0, [D.z0]))
    (h_valid : IsValidStateTrajectory D f g) :
    g = generateStateTrajectory D q0 f := by
  funext t
  induction t with
  | zero => exact h_init
  | succ t ih =>
    rw [h_valid t, generateStateTrajectory_succ, ih]

theorem outputTrajectory_unique (D : DPDASystem STfin IS OZ Γ) (g : Time → Snapshot STfin Γ)
    (h : Time → OZ) (h_valid : IsValidOutputTrajectory D g h) :
    ∀ t, h t = D.G (g t).1 (peek D.z0 (g t).2) := by
  intro t
  exact h_valid t

/-! ## Determinism

The schedule-driven trajectory above is deterministic for any fixed input stream simply because
`F` is a function. The genuine DPDA determinism condition is about the *choice* between an
ε-move and an input-consuming move: a DPDA may not have both available at the same control state
and stack top. We make this explicit. -/

/--
  A single ε-step (consumes no input). Returns `none` if no ε-move is defined.
-/
def stepEps (D : DPDASystem STfin IS OZ Γ) (snap : Snapshot STfin Γ) : Option (Snapshot STfin Γ) :=
  match snap with
  | (q, s) =>
    match D.F q none (peek D.z0 s) with
    | none => none
    | some (q', new) => some (q', updateStack s new)

/--
  A single input-consuming step on symbol `a`. Returns `none` if no such move is defined.
-/
def stepInput (D : DPDASystem STfin IS OZ Γ) (snap : Snapshot STfin Γ) (a : IS) :
    Option (Snapshot STfin Γ) :=
  match snap with
  | (q, s) =>
    match D.F q (some a) (peek D.z0 s) with
    | none => none
    | some (q', new) => some (q', updateStack s new)

/--
  The standard DPDA determinism condition: whenever an ε-move is available at control state `q`
  with stack top `Z`, no input-consuming move is available there. This guarantees that the
  computation on a given input word is unambiguous. Currently used by `deterministic_no_conflict`;
  a uniqueness-of-run theorem is on the roadmap ([formalization_roadmap.md](../formalization_roadmap.md) §3).
-/
def IsDeterministic (D : DPDASystem STfin IS OZ Γ) : Prop :=
  ∀ (q : STfin) (Z : Γ), (D.F q none Z).isSome = true → ∀ a : IS, D.F q (some a) Z = none

/--
  Under `IsDeterministic`, a configuration that can take an ε-step cannot also consume input.
  This is the operational consequence of the determinism condition.
-/
theorem deterministic_no_conflict (D : DPDASystem STfin IS OZ Γ) (hD : IsDeterministic D)
    (q : STfin) (s : Stack Γ) (a : IS)
    (he : (stepEps D (q, s)).isSome = true) : stepInput D (q, s) a = none := by
  have hsome : (D.F q none (peek D.z0 s)).isSome = true := by
    simp only [stepEps] at he
    cases hff : D.F q none (peek D.z0 s) with
    | none => rw [hff] at he; simp at he
    | some _ => rfl
  have hnone := hD q (peek D.z0 s) hsome a
  simp only [stepInput, hnone]

/-! ## Language / Acceptance over finite words

`Reaches D c w c'` means: starting from configuration `c`, the DPDA can reach configuration `c'`
while consuming exactly the input word `w` (ε-moves consume nothing). Using a relation (rather
than a recursive run function) sidesteps non-termination from ε-loops. -/

/-!
`Reaches D c w c'` — finite-word transition closure: from configuration `c`, consume exactly
word `w` (ε-moves via `stepEps` consume nothing) and arrive at `c'`. Used for language
acceptance; not yet linked to time-step trajectories `generateStateTrajectory` (roadmap P1).
-/

inductive Reaches (D : DPDASystem STfin IS OZ Γ) :
    Snapshot STfin Γ → List IS → Snapshot STfin Γ → Prop
  | refl (c : Snapshot STfin Γ) : Reaches D c [] c
  | eps {c c' c'' : Snapshot STfin Γ} {w : List IS} :
      stepEps D c = some c' → Reaches D c' w c'' → Reaches D c w c''
  | inp {c c' c'' : Snapshot STfin Γ} {a : IS} {w : List IS} :
      stepInput D c a = some c' → Reaches D c' w c'' → Reaches D c (a :: w) c''

/-- A word `w` is accepted from initial control state `q0` if some computation consuming `w`
    ends in a control state satisfying `accept` (acceptance by final state).
    Partial vs textbook PDAs: empty-stack acceptance is not modeled; see roadmap §3. -/
def Accepts (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (accept : STfin → Prop) (w : List IS) :
    Prop :=
  ∃ (q : STfin) (s : Stack Γ), Reaches D (q0, [D.z0]) w (q, s) ∧ accept q

/-- The language recognized by the DPDA from `q0` with accepting predicate `accept`.
    Word-level semantics (`Reaches`); no equivalence to `generateStateTrajectory` yet
    (roadmap P1). -/
def Language (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (accept : STfin → Prop) :
    Set (List IS) :=
  { w | Accepts D q0 accept w }

/-- The empty word is in the language whenever the initial control state is accepting. -/
theorem nil_mem_language (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (accept : STfin → Prop)
    (h : accept q0) : [] ∈ Language D q0 accept :=
  ⟨q0, [D.z0], Reaches.refl _, h⟩

/-- A one-symbol word `[a]` is accepted whenever a single input move from the start lands in an
    accepting state. -/
theorem singleton_mem_language (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (accept : STfin → Prop)
    (a : IS) (q : STfin) (s : Stack Γ)
    (hstep : stepInput D (q0, [D.z0]) a = some (q, s)) (h : accept q) :
    [a] ∈ Language D q0 accept :=
  ⟨q, s, Reaches.inp hstep (Reaches.refl _), h⟩

/-! ## Finiteness Analysis: Bounded Stack space -/

/-- Helper to generate all lists of length up to `max_depth` over a finite type. -/
def allListsUpTo (Γ : Type) [Fintype Γ] [DecidableEq Γ] : Nat → Finset (List Γ)
  | 0 => {[]}
  | n + 1 => allListsUpTo Γ n ∪ (Finset.univ.biUnion (fun x => (allListsUpTo Γ n).image (fun l => x :: l)))

theorem mem_allListsUpTo {Γ : Type} [Fintype Γ] [DecidableEq Γ] (max_depth : Nat) (l : List Γ) :
    l ∈ allListsUpTo Γ max_depth ↔ l.length ≤ max_depth := by
  induction max_depth generalizing l with
  | zero => simp [allListsUpTo]
  | succ n ih =>
    dsimp [allListsUpTo]
    simp only [Finset.mem_union, ih, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      rcases h with h_le | ⟨x, l', hl', rfl⟩
      · exact Nat.le_succ_of_le h_le
      · simp only [List.length_cons]
        exact Nat.succ_le_succ hl'
    · intro h
      cases l with
      | nil =>
        left
        exact Nat.zero_le _
      | cons x xs =>
        right
        use x, xs
        simp only [List.length_cons] at h
        have h_xs : xs.length ≤ n := Nat.le_of_succ_le_succ h
        exact ⟨h_xs, rfl⟩

/-- A stack whose length is bounded by `max_depth`. Coerced to Type for automatic Fintype support. -/
def BoundedStack (Γ : Type) [Fintype Γ] [DecidableEq Γ] (max_depth : Nat) : Type :=
  allListsUpTo Γ max_depth

instance instFintypeBoundedStack (Γ : Type) [Fintype Γ] [DecidableEq Γ] (max_depth : Nat) :
    Fintype (BoundedStack Γ max_depth) where
  elems := (allListsUpTo Γ max_depth).attach
  complete := fun _ => Finset.mem_attach _ _

section Bounded

/--
  The initial bounded configuration: control state `q0` with the base stack `[z0]` truncated to
  the bound (a no-op when `1 ≤ max_depth`).
-/
def boundedInit {Q I O G : Type}
    [Fintype G] [DecidableEq G] [Fintype Q] [DecidableEq Q] [Fintype I] [Fintype O]
    (D : DPDASystem Q I O G) (max_depth : Nat) (q0 : Q) : Q × BoundedStack G max_depth :=
  (q0, ⟨[D.z0].take max_depth, by
    rw [mem_allListsUpTo]
    exact List.length_take_le _ _⟩)

/--
  If stack depth is bounded, the infinite snapshot space collapses into a finite set,
  allowing a DPDA to be converted into a standard Wymorian `DiscreteSystem`.

  When the transition function is undefined the bounded system halts in place. When a push would
  exceed `max_depth` the new stack is truncated (`List.take`); this is a *lossy* approximation,
  faithful only while the genuine DPDA stack stays within the bound (see `bounded_output_agrees`).
-/
def toBoundedDiscreteSystem
    {Q I O G : Type}
    [Fintype G] [DecidableEq G] [Fintype Q] [DecidableEq Q] [Fintype I] [Fintype O]
    (D : DPDASystem Q I O G) (max_depth : Nat) [Inhabited Q] :
    DiscreteSystem (Q × BoundedStack G max_depth) (Option I) O where
  sz_nonempty := ⟨(default, ⟨[D.z0].take max_depth, by
    rw [mem_allListsUpTo]
    exact List.length_take_le _ _⟩)⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := D.oz_finite
  NZ := fun st input =>
    match st with
    | (q, ⟨s, hs⟩) =>
      match D.F q input (peek D.z0 s) with
      | none => (q, ⟨s, hs⟩)
      | some (q', new_top) =>
        (q', ⟨(updateStack s new_top).take max_depth, by
          rw [mem_allListsUpTo]
          exact List.length_take_le _ _⟩)
  RZ := fun st =>
    match st with
    | (q, ⟨s, _hs⟩) => D.G q (peek D.z0 s)

variable {Q I O G : Type}
    [Fintype G] [DecidableEq G] [Fintype Q] [DecidableEq Q] [Fintype I] [Fintype O] [Inhabited Q]

/--
  One-step simulation: if the bounded configuration `cB` agrees with the DPDA configuration `cD`
  (same control state and same stack contents), and the DPDA step result fits within `max_depth`,
  then the bounded `NZ` step agrees with the DPDA `stepSnapshot` step.
-/
theorem bounded_step_agrees
    (D : DPDASystem Q I O G) (max_depth : Nat)
    (cD : Snapshot Q G) (cB : Q × BoundedStack G max_depth)
    (h1 : cB.1 = cD.1) (h2 : cB.2.val = cD.2) (input : Option I)
    (hfit : (stepSnapshot D cD input).2.length ≤ max_depth) :
    ((toBoundedDiscreteSystem D max_depth).NZ cB input).1 = (stepSnapshot D cD input).1 ∧
    (((toBoundedDiscreteSystem D max_depth).NZ cB input).2).val = (stepSnapshot D cD input).2 := by
  obtain ⟨qB, sB⟩ := cB
  obtain ⟨sBval, sBmem⟩ := sB
  obtain ⟨qD, sDval⟩ := cD
  dsimp only at h1 h2
  subst h1
  subst h2
  cases hF : D.F qB input (peek D.z0 sBval) with
  | none =>
    refine ⟨?_, ?_⟩ <;> simp [toBoundedDiscreteSystem, stepSnapshot, hF]
  | some v =>
    obtain ⟨q', new⟩ := v
    simp only [stepSnapshot, hF] at hfit
    refine ⟨?_, ?_⟩
    · simp [toBoundedDiscreteSystem, stepSnapshot, hF]
    · simp only [toBoundedDiscreteSystem, stepSnapshot, hF]
      exact List.take_of_length_le hfit

/--
  Multi-step state correspondence: while the DPDA's stack never exceeds `max_depth` up to time
  `t`, the bounded `DiscreteSystem` trajectory tracks the DPDA snapshot trajectory exactly
  (same control state and same stack list).
-/
theorem bounded_state_agrees
    (D : DPDASystem Q I O G) (max_depth : Nat) (q0 : Q) (f : ITZ_opt I)
    (hmd : 1 ≤ max_depth) :
    ∀ t, (∀ τ, τ ≤ t → ((generateStateTrajectory D q0 f τ).2).length ≤ max_depth) →
      (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
          (boundedInit D max_depth q0) f t).1 = (generateStateTrajectory D q0 f t).1 ∧
      ((_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
          (boundedInit D max_depth q0) f t).2).val = (generateStateTrajectory D q0 f t).2 := by
  intro t
  induction t with
  | zero =>
    intro _hbound
    refine ⟨rfl, ?_⟩
    simp only [_root_.generateStateTrajectory_zero, generateStateTrajectory_zero, boundedInit]
    exact List.take_of_length_le (by simpa using hmd)
  | succ t ih =>
    intro hbound
    have hboundt : ∀ τ, τ ≤ t → ((generateStateTrajectory D q0 f τ).2).length ≤ max_depth :=
      fun τ hτ => hbound τ (Nat.le_succ_of_le hτ)
    obtain ⟨ih1, ih2⟩ := ih hboundt
    have hfit : (stepSnapshot D (generateStateTrajectory D q0 f t) (f t)).2.length ≤ max_depth := by
      have h := hbound (t + 1) (Nat.le_refl _)
      rwa [generateStateTrajectory_succ] at h
    have hstep := bounded_step_agrees D max_depth
      (generateStateTrajectory D q0 f t)
      (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t)
      ih1 ih2 (f t) hfit
    simpa only [_root_.generateStateTrajectory_succ, generateStateTrajectory_succ] using hstep

/--
  Behavioral equivalence: while the DPDA's stack stays within `max_depth` up to time `t`, the
  bounded `DiscreteSystem` produces exactly the same output as the DPDA. This is the real bridge
  between the context-free model and Wymore's finite `DiscreteSystem` (replacing the previous
  silent `.take` truncation, which had no correctness guarantee).
-/
theorem bounded_output_agrees
    (D : DPDASystem Q I O G) (max_depth : Nat) (q0 : Q) (f : ITZ_opt I)
    (hmd : 1 ≤ max_depth) (t : Time)
    (hbound : ∀ τ, τ ≤ t → ((generateStateTrajectory D q0 f τ).2).length ≤ max_depth) :
    _root_.generateOutputTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t = generateOutputTrajectory D q0 f t := by
  obtain ⟨h1, h2⟩ := bounded_state_agrees D max_depth q0 f hmd t hbound
  have eL : _root_.generateOutputTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t
      = D.G (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
              (boundedInit D max_depth q0) f t).1
          (peek D.z0 (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
              (boundedInit D max_depth q0) f t).2.val) := rfl
  have eR : generateOutputTrajectory D q0 f t
      = D.G (generateStateTrajectory D q0 f t).1
          (peek D.z0 (generateStateTrajectory D q0 f t).2) := rfl
  rw [eL, eR, h1, h2]

end Bounded

end DPDA
