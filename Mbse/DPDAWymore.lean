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

**Implemented:** 7-tuple spec, snapshot trajectories, soundness/uniqueness, time invariance /
nonanticipation, `IsDeterministic`, `Reaches` / `Language` (final-state acceptance),
`toBoundedDiscreteSystem` + `bounded_output_agrees` + bounded uniqueness / `IsFinite` corollaries.

**Intentionally omitted** (see [formalization_roadmap.md](../formalization_roadmap.md) §3):
Wymore reachability, state equivalence, morphisms, ports, parameterization, Ch. 3 coupling,
worked examples, `Reaches` ↔ trajectory bridge.

## Integration with other modules

- **Base [Wymore](Wymore.lean):** `toBoundedDiscreteSystem` maps a depth-bounded DPDA into
  `DiscreteSystem (Q × BoundedStack Γ max_depth) (Option I) O`. Unbounded stacks cannot live in
  `DiscreteSystem` directly because it requires `Fintype SZ`.
- **[GeneralizedWymore](GeneralizedWymore.lean):** Both use the shared base type `ITZW IS =
  Time → Option IS` (`ITZ_opt` is a DPDA-local alias).

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
  [textbook/definition2.4|partial]
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

/-- Input trajectory over Option IS (interleaved event/epsilon stream); alias of base `ITZW`. -/
abbrev ITZ_opt (IS : Type) := ITZW IS

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

/-- State trajectory from an arbitrary initial snapshot (not necessarily `(q0, [z0])`). -/
def generateStateTrajectoryFrom (D : DPDASystem STfin IS OZ Γ) (snap0 : Snapshot STfin Γ)
    (f : ITZ_opt IS) : Time → Snapshot STfin Γ
  | 0 => snap0
  | t + 1 => stepSnapshot D (generateStateTrajectoryFrom D snap0 f t) (f t)

/--
  [textbook/definition2.27/definition/state_trajectory_recurrence|partial]
  Generates the snapshot trajectory (state trajectory) of the DPDA from control state `q0`.
-/
def generateStateTrajectory (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    Time → Snapshot STfin Γ :=
  generateStateTrajectoryFrom D (q0, [D.z0]) f

theorem generateStateTrajectoryFrom_zero (D : DPDASystem STfin IS OZ Γ)
    (snap0 : Snapshot STfin Γ) (f : ITZ_opt IS) :
    generateStateTrajectoryFrom D snap0 f 0 = snap0 := rfl

theorem generateStateTrajectoryFrom_succ (D : DPDASystem STfin IS OZ Γ)
    (snap0 : Snapshot STfin Γ) (f : ITZ_opt IS) (t : Time) :
    generateStateTrajectoryFrom D snap0 f (t + 1) =
      stepSnapshot D (generateStateTrajectoryFrom D snap0 f t) (f t) := rfl

theorem generateStateTrajectory_eq_from (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS)
    (t : Time) :
    generateStateTrajectory D q0 f t = generateStateTrajectoryFrom D (q0, [D.z0]) f t :=
  rfl

/--
  [textbook/definition2.30/definition/output_trajectory_composition|partial]
  Generates the output trajectory of the DPDA.
-/
def generateOutputTrajectory (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    Time → OZ :=
  fun t =>
    let (q, s) := generateStateTrajectory D q0 f t
    D.G q (peek D.z0 s)

/-- Output readout along a trajectory from an arbitrary initial snapshot. -/
def generateOutputTrajectoryFrom (D : DPDASystem STfin IS OZ Γ) (snap0 : Snapshot STfin Γ)
    (f : ITZ_opt IS) (t : Time) : OZ :=
  let (q, s) := generateStateTrajectoryFrom D snap0 f t
  D.G q (peek D.z0 s)

theorem generateOutputTrajectory_eq_from (D : DPDASystem STfin IS OZ Γ) (q0 : STfin)
    (f : ITZ_opt IS) (t : Time) :
    generateOutputTrajectory D q0 f t =
      generateOutputTrajectoryFrom D (q0, [D.z0]) f t := by
  simp only [generateOutputTrajectory, generateOutputTrajectoryFrom, generateStateTrajectory_eq_from]

/-- [textbook/definition2.27/definition/state_trajectory_recurrence|partial] Predicate for a valid state trajectory. -/
def IsValidStateTrajectory (D : DPDASystem STfin IS OZ Γ) (f : ITZ_opt IS)
    (g : Time → Snapshot STfin Γ) : Prop :=
  ∀ t : Time, g (t + 1) = stepSnapshot D (g t) (f t)

/-- [textbook/definition2.30/definition/output_trajectory_composition|partial] Predicate for a valid output trajectory. -/
def IsValidOutputTrajectory (D : DPDASystem STfin IS OZ Γ) (g : Time → Snapshot STfin Γ)
    (h : Time → OZ) : Prop :=
  ∀ t : Time,
    let (q, s) := g t
    h t = D.G q (peek D.z0 s)

/-! ## Simp Lemmas -/

@[simp]
theorem dpda_generateStateTrajectory_zero (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    generateStateTrajectory D q0 f 0 = (q0, [D.z0]) := by
  unfold generateStateTrajectory
  exact generateStateTrajectoryFrom_zero D (q0, [D.z0]) f

@[simp]
theorem dpda_generateStateTrajectory_succ (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS)
    (t : Time) :
    generateStateTrajectory D q0 f (t + 1) =
      stepSnapshot D (generateStateTrajectory D q0 f t) (f t) := by
  unfold generateStateTrajectory
  exact generateStateTrajectoryFrom_succ D (q0, [D.z0]) f t

/-! ## Soundness and Uniqueness Theorems -/

theorem generateStateTrajectory_valid (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    IsValidStateTrajectory D f (generateStateTrajectory D q0 f) := by
  intro t
  rfl

theorem generateOutputTrajectory_valid (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f : ITZ_opt IS) :
    IsValidOutputTrajectory D (generateStateTrajectory D q0 f) (generateOutputTrajectory D q0 f) := by
  intro t
  rfl

/--
  [textbook/theorem2.29/proof/single_valuedness|partial]
  Given an initial control state and input trajectory, the snapshot trajectory is unique.
-/
theorem stateTrajectory_unique (D : DPDASystem STfin IS OZ Γ) (f : ITZ_opt IS)
    (g : Time → Snapshot STfin Γ) (q0 : STfin)
    (h_init : g 0 = (q0, [D.z0]))
    (h_valid : IsValidStateTrajectory D f g) :
    g = generateStateTrajectory D q0 f := by
  funext t
  induction t with
  | zero => exact h_init
  | succ t ih =>
    rw [h_valid t, dpda_generateStateTrajectory_succ, ih]

/-- [textbook/theorem2.32/theorem/trajectory_value|partial] Output trajectory is uniquely determined by the snapshot trajectory. -/
theorem outputTrajectory_unique (D : DPDASystem STfin IS OZ Γ) (g : Time → Snapshot STfin Γ)
    (h : Time → OZ) (h_valid : IsValidOutputTrajectory D g h) :
    ∀ t, h t = D.G (g t).1 (peek D.z0 (g t).2) := by
  intro t
  exact h_valid t

/-! ## Time invariance and nonanticipation (ported from the base engine) -/

/-- [textbook/theorem2.46/theorem/time_invariance] The snapshot trajectory engine is time invariant. -/
theorem stateTrajectory_time_invariance
    (D : DPDASystem STfin IS OZ Γ) (snap0 : Snapshot STfin Γ) (f : ITZ_opt IS) (s t : Time) :
    generateStateTrajectoryFrom D (generateStateTrajectoryFrom D snap0 f s) (translate f s) t =
    generateStateTrajectoryFrom D snap0 f (s + t) := by
  induction t with
  | zero => simp only [generateStateTrajectoryFrom_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectoryFrom_succ]
    rw [ih]
    unfold translate
    congr 1
    exact congrArg f (Nat.add_comm t s)

/-- [textbook/theorem2.48/theorem/nonanticipatory] The snapshot at time `t` depends only on the
    input restricted to `[0, t)`. -/
theorem stateTrajectory_nonanticipatory
    (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (f g : ITZ_opt IS) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory D q0 f t = generateStateTrajectory D q0 g t := by
  induction t with
  | zero => simp only [dpda_generateStateTrajectory_zero]
  | succ t ih =>
    simp only [dpda_generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i < t, f i = g i := fun i hi =>
      h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := h_agree t (Nat.lt_succ_self t)
    have h_rsn_t : RSN f {i | i < t} = RSN g {i | i < t} := by
      rw [rsn_eq_iff]; exact h_lt
    rw [ih h_rsn_t, h_eq]

/-- Output trajectory time invariance, derived from the snapshot time-invariance theorem. -/
theorem outputTrajectory_time_invariance
    (D : DPDASystem STfin IS OZ Γ) (snap0 : Snapshot STfin Γ) (f : ITZ_opt IS) (s t : Time) :
    generateOutputTrajectoryFrom D (generateStateTrajectoryFrom D snap0 f s) (translate f s) t =
    generateOutputTrajectoryFrom D snap0 f (s + t) := by
  simp only [generateOutputTrajectoryFrom]
  rw [stateTrajectory_time_invariance D snap0 f s t]

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

/-! ## Well-formed stack discipline -/

/--
  A stack is well-formed when the bottom marker `z0` is present and sits at the bottom.
  Under this invariant, `peek` on a nonempty stack reads the true top, not the empty-stack
  sentinel.
-/
def WellFormedStack (D : DPDASystem STfin IS OZ Γ) (s : Stack Γ) : Prop :=
  s.getLast? = some D.z0

/-- Transitions preserve well-formed stacks when pushes keep `z0` at the bottom. -/
def RespectsBottomMarker (D : DPDASystem STfin IS OZ Γ) : Prop :=
  ∀ (q : STfin) (inp : Option IS) (s : Stack Γ) (q' : STfin) (new_top : List Γ),
    WellFormedStack D s →
      D.F q inp (peek D.z0 s) = some (q', new_top) →
        WellFormedStack D (updateStack s new_top)

theorem wellFormed_init (D : DPDASystem STfin IS OZ Γ) : WellFormedStack D [D.z0] := by
  simp [WellFormedStack]

theorem wellFormed_snapshot_init (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) :
    WellFormedStack D (generateStateTrajectory D q0 (fun _ => none) 0).2 := by
  simp only [dpda_generateStateTrajectory_zero, wellFormed_init]

theorem wellFormed_nonempty (D : DPDASystem STfin IS OZ Γ) (s : Stack Γ)
    (h : WellFormedStack D s) : s ≠ [] := by
  intro hs
  rw [hs] at h
  simp [WellFormedStack] at h

theorem wellFormed_peek (D : DPDASystem STfin IS OZ Γ) (s : Stack Γ)
    (h : WellFormedStack D s) : peek D.z0 s = s.head (wellFormed_nonempty D s h) := by
  cases s with
  | nil => exact absurd rfl (wellFormed_nonempty D [] h)
  | cons z rest => simp [peek]

theorem stepSnapshot_preserves_wellFormed (D : DPDASystem STfin IS OZ Γ)
    (hR : RespectsBottomMarker D) (snap : Snapshot STfin Γ) (inp : Option IS)
    (hWF : WellFormedStack D snap.2) :
    WellFormedStack D (stepSnapshot D snap inp).2 := by
  unfold stepSnapshot
  cases snap with
  | mk q s =>
    cases hF : D.F q inp (peek D.z0 s) with
    | none => simpa [hF] using hWF
    | some v =>
      obtain ⟨q', new_top⟩ := v
      simpa [hF] using hR q inp s q' new_top hWF hF

theorem stepEps_preserves_wellFormed (D : DPDASystem STfin IS OZ Γ)
    (hR : RespectsBottomMarker D) (snap : Snapshot STfin Γ) (hWF : WellFormedStack D snap.2)
    (c' : Snapshot STfin Γ) (he : stepEps D snap = some c') :
    WellFormedStack D c'.2 := by
  cases snap with
  | mk q s =>
    cases hF : D.F q none (peek D.z0 s) with
    | none => simp [stepEps, hF] at he
    | some v =>
      obtain ⟨q', new_top⟩ := v
      simp [stepEps, hF] at he
      cases he
      exact hR q none s q' new_top hWF hF

theorem stepInput_preserves_wellFormed (D : DPDASystem STfin IS OZ Γ)
    (hR : RespectsBottomMarker D) (snap : Snapshot STfin Γ) (a : IS)
    (hWF : WellFormedStack D snap.2) (c' : Snapshot STfin Γ) (he : stepInput D snap a = some c') :
    WellFormedStack D c'.2 := by
  cases snap with
  | mk q s =>
    cases hF : D.F q (some a) (peek D.z0 s) with
    | none => simp [stepInput, hF] at he
    | some v =>
      obtain ⟨q', new_top⟩ := v
      simp [stepInput, hF] at he
      cases he
      exact hR q (some a) s q' new_top hWF hF

theorem stepSnapshot_none_eq_stepEps (D : DPDASystem STfin IS OZ Γ) (c c' : Snapshot STfin Γ)
    (he : stepEps D c = some c') : stepSnapshot D c none = c' := by
  cases c with
  | mk q s =>
    cases hF : D.F q none (peek D.z0 s) with
    | none => simp [stepEps, hF] at he
    | some v =>
      obtain ⟨q', new⟩ := v
      simp [stepSnapshot, stepEps, hF] at he ⊢
      cases he
      rfl

theorem stepSnapshot_some_eq_stepInput (D : DPDASystem STfin IS OZ Γ) (c c' : Snapshot STfin Γ)
    (a : IS) (he : stepInput D c a = some c') : stepSnapshot D c (some a) = c' := by
  cases c with
  | mk q s =>
    cases hF : D.F q (some a) (peek D.z0 s) with
    | none => simp [stepInput, hF] at he
    | some v =>
      obtain ⟨q', new⟩ := v
      simp [stepSnapshot, stepInput, hF] at he ⊢
      cases he
      rfl

theorem stepSnapshot_none_id (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ)
    (h : stepEps D c = none) : stepSnapshot D c none = c := by
  cases c with
  | mk q s =>
    cases hF : D.F q none (peek D.z0 s) with
    | none => simp [stepSnapshot, hF]
    | some v =>
      obtain ⟨q', new⟩ := v
      simp [stepEps, hF] at h

theorem stepSnapshot_some_id (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) (a : IS)
    (h : stepInput D c a = none) : stepSnapshot D c (some a) = c := by
  cases c with
  | mk q s =>
    cases hF : D.F q (some a) (peek D.z0 s) with
    | none => simp [stepSnapshot, hF]
    | some v =>
      obtain ⟨q', new⟩ := v
      simp [stepInput, hF] at h

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
  | stutter {c c'' : Snapshot STfin Γ} {a : IS} {w : List IS} :
      stepInput D c a = none → Reaches D c w c'' → Reaches D c (a :: w) c''

/-- Honest time-indexed run: `ScheduleRun D f c₀ T c` means the trajectory from `c₀` under
    stream `f` has length `T` and ends at `c`. Mirrors `generateStateTrajectoryFrom` one step
    at a time (including idle self-loops when `F` is undefined). -/
inductive ScheduleRun (D : DPDASystem STfin IS OZ Γ) (f : ITZ_opt IS) :
    Snapshot STfin Γ → Nat → Snapshot STfin Γ → Prop
  | zero (c₀ : Snapshot STfin Γ) : ScheduleRun D f c₀ 0 c₀
  | succ (c₀ cMid cEnd : Snapshot STfin Γ) (t : Nat) :
      ScheduleRun D f c₀ t cMid →
      stepSnapshot D cMid (f t) = cEnd →
      ScheduleRun D f c₀ (t + 1) cEnd

/-- Transitivity of `Reaches`: concatenating two computations concatenates their words.
    `Reaches` is a reflexive-transitive closure where `eps`/`inp`/`stutter` all peel a single
    step off the front of the word, so this is a direct induction on the first derivation. -/
theorem Reaches.trans (D : DPDASystem STfin IS OZ Γ) {c cMid cEnd : Snapshot STfin Γ}
    {w1 w2 : List IS} (h1 : Reaches D c w1 cMid) (h2 : Reaches D cMid w2 cEnd) :
    Reaches D c (w1 ++ w2) cEnd := by
  induction h1 with
  | refl => exact h2
  | eps he hrest ih => exact Reaches.eps he (ih h2)
  | inp he hrest ih => exact Reaches.inp he (ih h2)
  | stutter hno hrest ih => exact Reaches.stutter hno (ih h2)

/-! ## Word schedules and the Reaches ↔ trajectory bridge -/

/-- Input symbols consumed by stream `f` during times `[0, T)`. -/
def consumedWord (f : ITZ_opt IS) (T : Nat) : List IS :=
  (List.range T).filterMap f

/-- Embed a finite word into a stream; positions beyond `|w|-1` emit `none`. -/
def wordToStream (w : List IS) : ITZ_opt IS :=
  fun t => w[t]?

@[simp]
theorem consumedWord_zero (f : ITZ_opt IS) : consumedWord f 0 = [] := by
  simp [consumedWord]

theorem consumedWord_succ (f : ITZ_opt IS) (T : Nat) :
    consumedWord f (T + 1) =
      match f T with
      | none => consumedWord f T
      | some a => consumedWord f T ++ [a] := by
  simp only [consumedWord, List.range_succ, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil]
  cases hf : f T <;> simp

private theorem filterMap_range_shift_eps (f : ITZ_opt IS) (T : Nat) :
    (List.range (T + 1)).filterMap (fun t : Nat => if t = 0 then none else f (t - 1)) =
      (List.range T).filterMap f := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [show T + 1 + 1 = Nat.succ (Nat.succ T) from rfl, List.range_succ, List.filterMap_append, ih,
      List.range_succ, List.filterMap_append]
    congr 1

private theorem filterMap_range_shift_inp (a : IS) (f : ITZ_opt IS) (T : Nat) :
    (List.range (T + 1)).filterMap (fun t : Nat => if t = 0 then some a else f (t - 1)) =
      a :: (List.range T).filterMap f := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [show T + 1 + 1 = Nat.succ (Nat.succ T) from rfl, List.range_succ, List.filterMap_append, ih,
      List.range_succ, List.filterMap_append]
    congr 1

theorem consumedWord_shift_eps (f : ITZ_opt IS) (T : Nat) :
    consumedWord (fun t => if t = 0 then none else f (t - 1)) (T + 1) = consumedWord f T := by
  simp [consumedWord, filterMap_range_shift_eps]

theorem consumedWord_shift_inp (a : IS) (f : ITZ_opt IS) (T : Nat) :
    consumedWord (fun t => if t = 0 then some a else f (t - 1)) (T + 1) =
      a :: consumedWord f T := by
  simp [consumedWord, filterMap_range_shift_inp]

theorem wordToStream_cons (a : IS) (w : List IS) (t : Nat) :
    wordToStream (a :: w) t = if t = 0 then some a else wordToStream w (t - 1) := by
  cases t with
  | zero => simp [wordToStream]
  | succ t => simp [wordToStream]

@[simp]
theorem wordToStream_consumed (w : List IS) :
    consumedWord (wordToStream w) w.length = w := by
  induction w with
  | nil => simp [consumedWord, wordToStream]
  | cons a w ih =>
    have hstream :
        wordToStream (a :: w) = fun t => if t = 0 then some a else wordToStream w (t - 1) := by
      funext t
      rw [wordToStream_cons]
    rw [show (a :: w).length = w.length + 1 from rfl, hstream, consumedWord_shift_inp, ih]

/-- Greedy ε-closure with a fuel parameter (for termination). -/
def epsCloseFuel (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) : Nat → Snapshot STfin Γ
  | 0 => c
  | fuel + 1 =>
    match stepEps D c with
    | none => c
    | some c' => epsCloseFuel D c' fuel

/-- Canonical word runner: ε-close, consume one symbol, repeat. -/
def runWordFuel (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) (w : List IS) (fuel : Nat) :
    Option (Snapshot STfin Γ) :=
  match w with
  | [] => some (epsCloseFuel D c fuel)
  | a :: w' =>
    let cEps := epsCloseFuel D c fuel
    match stepInput D cEps a with
    | none => none
    | some c' => runWordFuel D c' w' fuel

def runWord (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) (w : List IS) :
    Option (Snapshot STfin Γ) :=
  runWordFuel D c w (w.length + c.2.length + 1)

/-- No ε-moves are defined (input-only fragment). -/
def NoEpsilonMoves (D : DPDASystem STfin IS OZ Γ) : Prop :=
  ∀ (q : STfin) (Z : Γ), D.F q none Z = none

theorem stepEps_eq_none (D : DPDASystem STfin IS OZ Γ) (hNE : NoEpsilonMoves D)
    (c : Snapshot STfin Γ) : stepEps D c = none := by
  rcases c with ⟨q, s⟩
  simp [stepEps, hNE q (peek D.z0 s)]

/-- Input-only word runner (no ε-moves). -/
def runWordNoEps (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) :
    List IS → Option (Snapshot STfin Γ)
  | [] => some c
  | a :: w =>
    match stepInput D c a with
    | none => runWordNoEps D c w
    | some c' => runWordNoEps D c' w

theorem runWordNoEps_nil (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) :
    runWordNoEps D c [] = some c := rfl

theorem runWordNoEps_cons (D : DPDASystem STfin IS OZ Γ) (c : Snapshot STfin Γ) (a : IS)
    (w : List IS) :
    runWordNoEps D c (a :: w) =
      match stepInput D c a with
      | none => runWordNoEps D c w
      | some c' => runWordNoEps D c' w := by
  cases h : stepInput D c a <;> simp [runWordNoEps, h]

theorem generateStateTrajectoryFrom_shift_eps (D : DPDASystem STfin IS OZ Γ)
    (c cMid : Snapshot STfin Γ) (f : ITZ_opt IS) (T : Nat)
    (he : stepEps D c = some cMid) :
    generateStateTrajectoryFrom D c (fun t => if t = 0 then none else f (t - 1)) (T + 1) =
      generateStateTrajectoryFrom D cMid f T := by
  induction T with
  | zero =>
    simp only [generateStateTrajectoryFrom_succ, generateStateTrajectoryFrom_zero]
    exact stepSnapshot_none_eq_stepEps D c cMid he
  | succ T ih =>
    let g := fun t : Nat => if t = 0 then none else f (t - 1)
    have h1 :
        generateStateTrajectoryFrom D c g (T + 2) =
          stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := by
      simp [generateStateTrajectoryFrom_succ, g]
    have h2 : generateStateTrajectoryFrom D c g (T + 1) = generateStateTrajectoryFrom D cMid f T := ih
    have hg : g (T + 1) = f T := by simp [g]
    calc
      generateStateTrajectoryFrom D c g (T + 2)
          = stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := h1
      _ = stepSnapshot D (generateStateTrajectoryFrom D cMid f T) (f T) := by rw [h2, hg]
      _ = generateStateTrajectoryFrom D cMid f (T + 1) := by simp [generateStateTrajectoryFrom_succ]

theorem generateStateTrajectoryFrom_shift_inp (D : DPDASystem STfin IS OZ Γ)
    (c cMid : Snapshot STfin Γ) (a : IS) (f : ITZ_opt IS) (T : Nat)
    (he : stepInput D c a = some cMid) :
    generateStateTrajectoryFrom D c (fun t => if t = 0 then some a else f (t - 1)) (T + 1) =
      generateStateTrajectoryFrom D cMid f T := by
  induction T with
  | zero =>
    simp only [generateStateTrajectoryFrom_succ, generateStateTrajectoryFrom_zero]
    exact stepSnapshot_some_eq_stepInput D c cMid a he
  | succ T ih =>
    let g := fun t : Nat => if t = 0 then some a else f (t - 1)
    have h1 :
        generateStateTrajectoryFrom D c g (T + 2) =
          stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := by
      simp [generateStateTrajectoryFrom_succ, g]
    have h2 : generateStateTrajectoryFrom D c g (T + 1) = generateStateTrajectoryFrom D cMid f T := ih
    have hg : g (T + 1) = f T := by simp [g]
    calc
      generateStateTrajectoryFrom D c g (T + 2)
          = stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := h1
      _ = stepSnapshot D (generateStateTrajectoryFrom D cMid f T) (f T) := by rw [h2, hg]
      _ = generateStateTrajectoryFrom D cMid f (T + 1) := by simp [generateStateTrajectoryFrom_succ]

theorem generateStateTrajectoryFrom_shift_stutter (D : DPDASystem STfin IS OZ Γ)
    (c : Snapshot STfin Γ) (a : IS) (f : ITZ_opt IS) (T : Nat)
    (hno : stepInput D c a = none) :
    generateStateTrajectoryFrom D c (fun t => if t = 0 then some a else f (t - 1)) (T + 1) =
      generateStateTrajectoryFrom D c f T := by
  induction T with
  | zero =>
    simp only [generateStateTrajectoryFrom_succ, generateStateTrajectoryFrom_zero]
    exact stepSnapshot_some_id D c a hno
  | succ T ih =>
    let g := fun t : Nat => if t = 0 then some a else f (t - 1)
    have h1 :
        generateStateTrajectoryFrom D c g (T + 2) =
          stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := by
      simp [generateStateTrajectoryFrom_succ, g]
    have h2 : generateStateTrajectoryFrom D c g (T + 1) = generateStateTrajectoryFrom D c f T := ih
    have hg : g (T + 1) = f T := by simp [g]
    calc
      generateStateTrajectoryFrom D c g (T + 2)
          = stepSnapshot D (generateStateTrajectoryFrom D c g (T + 1)) (g (T + 1)) := h1
      _ = stepSnapshot D (generateStateTrajectoryFrom D c f T) (f T) := by rw [h2, hg]
      _ = generateStateTrajectoryFrom D c f (T + 1) := by simp [generateStateTrajectoryFrom_succ]

private theorem generateStateTrajectoryFrom_agree_of_stream_agree
    (D : DPDASystem STfin IS OZ Γ) (snap : Snapshot STfin Γ) (f g : ITZ_opt IS) (T : Nat)
    (hagree : ∀ t < T, f t = g t) :
    generateStateTrajectoryFrom D snap f T = generateStateTrajectoryFrom D snap g T := by
  induction T generalizing snap with
  | zero => rfl
  | succ T ih =>
    simp only [generateStateTrajectoryFrom_succ]
    have hagree' : ∀ t < T, f t = g t := fun t ht =>
      hagree t (Nat.lt_trans ht (Nat.lt_succ_self T))
    rw [ih snap hagree', hagree T (Nat.lt_succ_self T)]

/-! ### ScheduleRun hub: trajectory ↔ word semantics -/

theorem scheduleRun_iff_trajectory (D : DPDASystem STfin IS OZ Γ) (c₀ c : Snapshot STfin Γ)
    (f : ITZ_opt IS) (T : Nat) :
    ScheduleRun D f c₀ T c ↔ generateStateTrajectoryFrom D c₀ f T = c := by
  induction T generalizing c₀ c with
  | zero =>
    constructor
    · intro h; cases h; exact generateStateTrajectoryFrom_zero _ _ f
    · intro h; rw [generateStateTrajectoryFrom_zero] at h; subst h; exact ScheduleRun.zero c₀
  | succ T ih =>
    constructor
    · intro h
      cases h
      case succ cMid hprev hstep =>
        have hmid : generateStateTrajectoryFrom D c₀ f T = cMid :=
          (ih c₀ cMid).mp hprev
        calc generateStateTrajectoryFrom D c₀ f (T + 1)
            = stepSnapshot D (generateStateTrajectoryFrom D c₀ f T) (f T) := rfl
          _ = stepSnapshot D cMid (f T) := by rw [hmid]
          _ = c := hstep
    · intro htraj
      set cMid := generateStateTrajectoryFrom D c₀ f T
      have hrun : ScheduleRun D f c₀ T cMid := (ih c₀ cMid).mpr rfl
      have hstep : stepSnapshot D cMid (f T) = c := by
        dsimp [cMid]
        rw [← htraj, generateStateTrajectoryFrom_succ]
      exact ScheduleRun.succ c₀ cMid c T hrun hstep

theorem scheduleRun_implies_reaches (D : DPDASystem STfin IS OZ Γ)
    (c₀ c : Snapshot STfin Γ) (f : ITZ_opt IS) (T : Nat)
    (hrun : ScheduleRun D f c₀ T c) :
    Reaches D c₀ (consumedWord f T) c := by
  induction T generalizing c₀ c with
  | zero =>
    cases hrun
    simp [consumedWord, Reaches.refl]
  | succ T ih =>
    cases hrun
    case succ cMid hprev hstep =>
      have ih' := ih c₀ cMid hprev
      rw [consumedWord_succ]
      cases hf : f T with
      | none =>
        rw [hf] at hstep
        cases hEps : stepEps D cMid with
        | none =>
          have hc : c = cMid := by
            rw [← hstep, stepSnapshot_none_id D cMid hEps]
          rw [hc]; exact ih'
        | some cNext =>
          have hc : c = cNext := by
            rw [← hstep, stepSnapshot_none_eq_stepEps D cMid cNext hEps]
          rw [hc]
          simpa [List.append_nil] using
            Reaches.trans D ih' (Reaches.eps hEps (Reaches.refl cNext))
      | some a =>
        rw [hf] at hstep
        cases hInp : stepInput D cMid a with
        | none =>
          have hc : c = cMid := by
            rw [← hstep, stepSnapshot_some_id D cMid a hInp]
          rw [hc]
          exact Reaches.trans D ih' (Reaches.stutter hInp (Reaches.refl cMid))
        | some cNext =>
          have hc : c = cNext := by
            rw [← hstep, stepSnapshot_some_eq_stepInput D cMid cNext a hInp]
          rw [hc]
          exact Reaches.trans D ih' (Reaches.inp hInp (Reaches.refl cNext))

theorem trajectory_implies_reaches (D : DPDASystem STfin IS OZ Γ)
    (c c' : Snapshot STfin Γ) (f : ITZ_opt IS) (T : Nat) (w : List IS)
    (hw : consumedWord f T = w)
    (htraj : generateStateTrajectoryFrom D c f T = c') :
    Reaches D c w c' := by
  have hrun : ScheduleRun D f c T c' :=
    (scheduleRun_iff_trajectory D c c' f T).mpr htraj
  exact hw ▸ scheduleRun_implies_reaches D c c' f T hrun

theorem reaches_implies_trajectory (D : DPDASystem STfin IS OZ Γ)
    (c cEnd : Snapshot STfin Γ) (word : List IS) (h : Reaches D c word cEnd) :
    ∃ (f : ITZ_opt IS) (T : Nat),
      consumedWord f T = word ∧ generateStateTrajectoryFrom D c f T = cEnd := by
  induction h with
  | refl =>
    refine ⟨fun _ => none, 0, by simp [consumedWord], by simp [generateStateTrajectoryFrom_zero]⟩
  | eps he hrest ih =>
    obtain ⟨inputStream, T, hw, htraj⟩ := ih
    refine ⟨fun t => if t = 0 then none else inputStream (t - 1), T + 1, ?_, ?_⟩
    · rw [consumedWord_shift_eps, hw]
    · exact generateStateTrajectoryFrom_shift_eps D _ _ inputStream T he ▸ htraj
  | inp he hrest ih =>
    rename_i a w
    obtain ⟨inputStream, T, hw, htraj⟩ := ih
    refine ⟨fun t => if t = 0 then some a else inputStream (t - 1), T + 1, ?_, ?_⟩
    · rw [consumedWord_shift_inp a, hw]
    · exact generateStateTrajectoryFrom_shift_inp D _ _ a inputStream T he ▸ htraj
  | stutter hno hrest ih =>
    rename_i a w
    obtain ⟨inputStream, T, hw, htraj⟩ := ih
    refine ⟨fun t => if t = 0 then some a else inputStream (t - 1), T + 1, ?_, ?_⟩
    · rw [consumedWord_shift_inp a, hw]
    · exact generateStateTrajectoryFrom_shift_stutter D _ a inputStream T hno ▸ htraj

theorem reaches_iff_trajectory (D : DPDASystem STfin IS OZ Γ)
    (c c' : Snapshot STfin Γ) (w : List IS) :
    Reaches D c w c' ↔
      ∃ (f : ITZ_opt IS) (T : Nat),
        consumedWord f T = w ∧ generateStateTrajectoryFrom D c f T = c' := by
  constructor
  · intro h
    exact reaches_implies_trajectory D c c' w h
  · intro ⟨f, T, hw, htraj⟩
    exact trajectory_implies_reaches D c c' f T w hw htraj

theorem runWordNoEps_reaches (D : DPDASystem STfin IS OZ Γ) (_hNE : NoEpsilonMoves D)
    (c c' : Snapshot STfin Γ) (w : List IS) (hrun : runWordNoEps D c w = some c') :
    Reaches D c w c' := by
  induction w generalizing c with
  | nil =>
    simp [runWordNoEps] at hrun
    subst hrun
    exact Reaches.refl c
  | cons a w ih =>
    unfold runWordNoEps at hrun
    cases hstep : stepInput D c a with
    | none =>
      simp [hstep] at hrun
      exact Reaches.stutter hstep (ih c hrun)
    | some cMid =>
      simp [hstep] at hrun
      exact Reaches.inp hstep (ih cMid hrun)

theorem runWordNoEps_of_reaches (D : DPDASystem STfin IS OZ Γ) (hNE : NoEpsilonMoves D)
    (c cEnd : Snapshot STfin Γ) (word : List IS) (h : Reaches D c word cEnd) :
    runWordNoEps D c word = some cEnd := by
  induction h with
  | refl => rfl
  | eps he hrest ih =>
    rw [stepEps_eq_none D hNE _] at he
    cases he
  | inp he hrest ih =>
    rename_i a w
    unfold runWordNoEps
    rw [he]
    exact ih
  | stutter hno hrest ih =>
    rename_i a w
    unfold runWordNoEps
    rw [hno]
    exact ih

theorem reaches_refl_dest (D : DPDASystem STfin IS OZ Γ) (c c' : Snapshot STfin Γ)
    (h : Reaches D c [] c') (hNE : NoEpsilonMoves D) : c' = c := by
  have hr := runWordNoEps_of_reaches D hNE c c' [] h
  simp [runWordNoEps] at hr
  exact hr.symm

theorem runWordNoEps_spec (D : DPDASystem STfin IS OZ Γ) (hNE : NoEpsilonMoves D)
    (c c' : Snapshot STfin Γ) (w : List IS) :
    runWordNoEps D c w = some c' ↔ Reaches D c w c' :=
  ⟨runWordNoEps_reaches D hNE c c' w, runWordNoEps_of_reaches D hNE c c' w⟩

theorem deterministic_unique_reaches (D : DPDASystem STfin IS OZ Γ) (_hD : IsDeterministic D)
    (hNE : NoEpsilonMoves D) (c c1 c2 : Snapshot STfin Γ) (w : List IS)
    (h1 : Reaches D c w c1) (h2 : Reaches D c w c2) : c1 = c2 := by
  have h1' := runWordNoEps_of_reaches D hNE c c1 w h1
  have h2' := runWordNoEps_of_reaches D hNE c c2 w h2
  exact Option.some_inj.mp (h1'.symm.trans h2')

theorem wordToStream_reaches (D : DPDASystem STfin IS OZ Γ) (c c' : Snapshot STfin Γ)
    (w : List IS)
    (htraj : generateStateTrajectoryFrom D c (wordToStream w) w.length = c') :
    Reaches D c w c' :=
  trajectory_implies_reaches D c c' (wordToStream w) w.length w (wordToStream_consumed w) htraj

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

/-! ## Acceptance by empty stack

The textbook "accept by empty stack" mode is modeled here as "only the bottom marker `z0`
remains". Under the `WellFormedStack` discipline the bottom marker is never popped
(`wellFormed_nonempty` shows a well-formed stack is never literally `[]`), so the faithful
encoding of an empty stack is the singleton `[z0]`, not `[]`. -/

/-- A word `w` is accepted by empty stack from `q0` if some computation consuming `w` returns the
    stack to the bottom marker `[z0]` (textbook empty-stack acceptance under the
    `WellFormedStack` convention; see module docs and the report). -/
def AcceptsEmptyStack (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (w : List IS) : Prop :=
  ∃ q : STfin, Reaches D (q0, [D.z0]) w (q, [D.z0])

/-- The language recognized by empty-stack (bottom-marker) acceptance. -/
def LanguageEmptyStack (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) : Set (List IS) :=
  { w | AcceptsEmptyStack D q0 w }

/-- Empty-stack acceptance entails final-state acceptance for any predicate that holds at the
    landing control state. The two modes coincide exactly when the accepting predicate is
    "the stack returned to the bottom marker". -/
theorem mem_language_of_acceptsEmptyStack (D : DPDASystem STfin IS OZ Γ) (q0 : STfin)
    (accept : STfin → Prop) (w : List IS) (q : STfin)
    (hreach : Reaches D (q0, [D.z0]) w (q, [D.z0])) (hq : accept q) :
    w ∈ Language D q0 accept :=
  ⟨q, [D.z0], hreach, hq⟩

/-- Bridge form: an empty-stack run is certified by a single trajectory evaluation at time `|w|`
    (via `wordToStream`), tying `LanguageEmptyStack` to `generateStateTrajectory`. -/
theorem acceptsEmptyStack_of_trajectory (D : DPDASystem STfin IS OZ Γ) (q0 : STfin) (w : List IS)
    (q : STfin)
    (htraj : generateStateTrajectoryFrom D (q0, [D.z0]) (wordToStream w) w.length = (q, [D.z0])) :
    AcceptsEmptyStack D q0 w :=
  ⟨q, wordToStream_reaches D (q0, [D.z0]) (q, [D.z0]) w htraj⟩

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
  [textbook/definition2.4|partial]
  If stack depth is bounded, the infinite snapshot space collapses into a finite set,
  allowing a DPDA to be converted into a standard Wymorian `DiscreteSystem`.

  Corollaries: `bounded_system_isFinite`, `bounded_stateTrajectory_unique`,
  `bounded_outputTrajectory_unique`, `bounded_output_agrees`.

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
    simp only [_root_.generateStateTrajectory_zero, dpda_generateStateTrajectory_zero, boundedInit]
    exact List.take_of_length_le (by simpa using hmd)
  | succ t ih =>
    intro hbound
    have hboundt : ∀ τ, τ ≤ t → ((generateStateTrajectory D q0 f τ).2).length ≤ max_depth :=
      fun τ hτ => hbound τ (Nat.le_succ_of_le hτ)
    obtain ⟨ih1, ih2⟩ := ih hboundt
    have hfit : (stepSnapshot D (generateStateTrajectory D q0 f t) (f t)).2.length ≤ max_depth := by
      have h := hbound (t + 1) (Nat.le_refl _)
      rwa [dpda_generateStateTrajectory_succ] at h
    have hstep := bounded_step_agrees D max_depth
      (generateStateTrajectory D q0 f t)
      (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t)
      ih1 ih2 (f t) hfit
    simpa only [_root_.generateStateTrajectory_succ, dpda_generateStateTrajectory_succ] using hstep

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

/-- [textbook/definition2.11/definition/finite_system] The bounded reduction yields a finite Wymore system. -/
theorem bounded_system_isFinite
    (D : DPDASystem Q I O G) (max_depth : Nat) :
    IsFinite (toBoundedDiscreteSystem D max_depth) :=
  discreteSystem_isFinite (toBoundedDiscreteSystem D max_depth)

/--
  State trajectory uniqueness for the bounded `DiscreteSystem`, derived from base Wymore
  `stateTrajectory_unique`.
-/
theorem bounded_stateTrajectory_unique
    (D : DPDASystem Q I O G) (max_depth : Nat) (q0 : Q) (f : ITZ_opt I)
    (g : Time → Q × BoundedStack G max_depth)
    (h_init : g 0 = boundedInit D max_depth q0)
    (h_valid : _root_.IsValidStateTrajectory (toBoundedDiscreteSystem D max_depth) f g) :
    ∀ t, g t = _root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t :=
  _root_.stateTrajectory_unique (toBoundedDiscreteSystem D max_depth) f g (boundedInit D max_depth q0)
    h_init h_valid

/--
  Output trajectory uniqueness for the bounded embedding at each time step, derived from base
  Wymore `outputTrajectory_unique`.
-/
theorem bounded_outputTrajectory_unique
    (D : DPDASystem Q I O G) (max_depth : Nat) (q0 : Q) (f : ITZ_opt I)
    (h : Time → O)
    (h_valid : _root_.IsValidOutputTrajectory (toBoundedDiscreteSystem D max_depth)
      (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f) h) (t : Time) :
    h t = _root_.generateOutputTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f t := by
  rw [_root_.outputTrajectory_unique (toBoundedDiscreteSystem D max_depth)
    (_root_.generateStateTrajectory (toBoundedDiscreteSystem D max_depth)
        (boundedInit D max_depth q0) f) h h_valid t]
  rfl

end Bounded

end DPDA
