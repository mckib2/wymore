import Mbse.Wymore

/-!
# Generalized Wymore Systems (faithful closed / open and autonomous systems)

The base `DiscreteSystem` (Definition 2.4) has two faithfulness gaps relative to the textbook's
conditional signatures:

* a *total* readout `RZ : SZ → OZ` forces `OZ` nonempty (`discreteSystem_output_nonempty`), so
  closed / empty-output systems (`RZ = ∅ if OZ empty`) are unrepresentable (`not_isClosed`);
* a transition `NZ : SZ → IZ → SZ` cannot drive a system when `IZ` is empty (no complete input
  trajectory `Time → IZ` exists), so the autonomous case `NZ ∈ FNS(SZ, SZ) if IZ empty` cannot be
  modeled.

`WymoreSystem` closes both gaps with a single, uniform generalization:

* `NZ : SZ → Option IZ → SZ` — a `none` step is an *autonomous* (input-free) transition, so
  empty-input systems evolve via the unique trajectory `fun _ => none`, and nonempty-input
  systems behave as before via `some`;
* `RZ : SZ → Option OZ` — `none` models "no output" (closed systems).

This module ports the trajectory engine and its soundness/uniqueness/time-invariance/
nonanticipation theorems, shows closed and autonomous systems are now constructible, and — for
main-line integration — gives a structure-preserving embedding `DiscreteSystem.toWymore` together
with morphism, reachability, and state-equivalence transfer results connecting the generalized
layer to the existing `DiscreteSystem` development.
-/

namespace GWymore

/--
  A generalized Wymore discrete system `Z = (SZ, IZ, OZ, NZ, RZ)`:

  * `NZ : SZ → Option IZ → SZ` — `NZ s (some i)` is an input-driven step, `NZ s none` is an
    autonomous step (used for empty-input / autonomous dynamics).
  * `RZ : SZ → Option OZ` — partial readout; `none` means "no output" (closed systems).
-/
structure WymoreSystem (SZ : Type) (IZ : Type) (OZ : Type) where
  /-- The state space is nonempty. -/
  sz_nonempty : Nonempty SZ
  /-- The state space is finite. -/
  sz_finite : Fintype SZ
  /-- The input space is finite. -/
  iz_finite : Fintype IZ
  /-- The output space is finite. -/
  oz_finite : Fintype OZ
  /-- Next-state function; `none` input denotes an autonomous (input-free) transition. -/
  NZ : SZ → Option IZ → SZ
  /-- Partial readout; `none` models "no output" (closed systems). -/
  RZ : SZ → Option OZ

variable {SZ IZ OZ : Type}

/-! ## Trajectory engine

`ITZW` is defined in the base module as `Time → Option IZ` (autonomous steps via `none`).
-/

/-! ## Trajectory engine -/

/-- The state trajectory recurrence (same shape as the base engine, with `Option` inputs). -/
def generateStateTrajectory (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : STZ SZ
  | 0 => s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)

/-- The (partial) output trajectory: `RZ` applied along the state trajectory. -/
def generateOutputTrajectory (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    Time → Option OZ :=
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)

/-- Validity predicate for a state trajectory. -/
def IsValidStateTrajectory (Z : WymoreSystem SZ IZ OZ) (f : ITZW IZ) (g : STZ SZ) : Prop :=
  ∀ t : Time, g (t + 1) = Z.NZ (g t) (f t)

/-- Validity predicate for a (partial) output trajectory. -/
def IsValidOutputTrajectory (Z : WymoreSystem SZ IZ OZ) (g : STZ SZ) (h : Time → Option OZ) :
    Prop :=
  ∀ t : Time, h t = Z.RZ (g t)

@[simp]
theorem generateStateTrajectory_zero (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    generateStateTrajectory Z s0 f 0 = s0 := rfl

@[simp]
theorem generateStateTrajectory_succ (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (t : Time) :
    generateStateTrajectory Z s0 f (t + 1) =
      Z.NZ (generateStateTrajectory Z s0 f t) (f t) := rfl

/-! ## Soundness and uniqueness -/

theorem generateStateTrajectory_valid (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    IsValidStateTrajectory Z f (generateStateTrajectory Z s0 f) := by
  intro t; rfl

theorem generateOutputTrajectory_valid (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    IsValidOutputTrajectory Z (generateStateTrajectory Z s0 f) (generateOutputTrajectory Z s0 f) := by
  intro t; rfl

theorem stateTrajectory_unique (Z : WymoreSystem SZ IZ OZ) (f : ITZW IZ) (g : STZ SZ) (s0 : SZ)
    (h_init : g 0 = s0) (h_valid : IsValidStateTrajectory Z f g) :
    ∀ t, g t = generateStateTrajectory Z s0 f t := by
  intro t
  induction t with
  | zero => exact h_init
  | succ n ih => rw [generateStateTrajectory_succ, h_valid n, ih]

theorem outputTrajectory_unique (Z : WymoreSystem SZ IZ OZ) (g : STZ SZ) (h : Time → Option OZ)
    (h_valid : IsValidOutputTrajectory Z g h) :
    ∀ t, h t = Z.RZ (g t) :=
  h_valid

/-! ## Time invariance and nonanticipation (ported from the base engine) -/

/-- [textbook/theorem2.46/theorem/time_invariance] The state trajectory engine is time invariant. -/
theorem stateTrajectory_time_invariance
    (Z : WymoreSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateStateTrajectory Z x f (s + t) := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [ih]
    unfold translate
    congr 2
    exact Nat.add_comm t s

/-- [textbook/theorem2.48/theorem/nonanticipatory] The state at time `t` depends only on the
    input restricted to `[0, t)`. -/
theorem stateTrajectory_nonanticipatory
    (Z : WymoreSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i < t, f i = g i := fun i hi =>
      h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := h_agree t (Nat.lt_succ_self t)
    have h_rsn_t : RSN f {i | i < t} = RSN g {i | i < t} := by
      rw [rsn_eq_iff]; exact h_lt
    rw [ih h_rsn_t, h_eq]

/-! ## System-theoretic concepts -/

/-- A state `s` is reachable from `s0` if some (generalized) input trajectory drives the system
    to `s`. -/
def Reachable (Z : WymoreSystem SZ IZ OZ) (s0 s : SZ) : Prop :=
  ∃ (f : ITZW IZ) (t : Time), generateStateTrajectory Z s0 f t = s

/-- The initial state is reachable from itself (at time 0). No `Inhabited` assumption is needed:
    `ITZW IZ` is always inhabited via the autonomous trajectory `fun _ => none`. -/
theorem reachable_self (Z : WymoreSystem SZ IZ OZ) (s0 : SZ) : Reachable Z s0 s0 :=
  ⟨fun _ => none, 0, rfl⟩

/-- Two states are equivalent if they yield identical (partial) output trajectories under every
    generalized input trajectory. -/
def StateEquiv (Z : WymoreSystem SZ IZ OZ) (s1 s2 : SZ) : Prop :=
  ∀ (f : ITZW IZ) (t : Time),
    generateOutputTrajectory Z s1 f t = generateOutputTrajectory Z s2 f t

theorem stateEquiv_refl (Z : WymoreSystem SZ IZ OZ) (s : SZ) : StateEquiv Z s s := by
  intro _ _; rfl

theorem stateEquiv_symm (Z : WymoreSystem SZ IZ OZ) (s1 s2 : SZ)
    (h : StateEquiv Z s1 s2) : StateEquiv Z s2 s1 := by
  intro f t; exact (h f t).symm

theorem stateEquiv_trans (Z : WymoreSystem SZ IZ OZ) (s1 s2 s3 : SZ)
    (h12 : StateEquiv Z s1 s2) (h23 : StateEquiv Z s2 s3) : StateEquiv Z s1 s3 := by
  intro f t; exact (h12 f t).trans (h23 f t)

/-! ## Closed, open, and autonomous systems are all representable -/

/-- A system is closed if both its input and output spaces are empty (Definition 2.4). -/
def IsClosed (_Z : WymoreSystem SZ IZ OZ) : Prop :=
  IsEmpty IZ ∧ IsEmpty OZ

/-- A system is open if neither its input nor output spaces are empty. -/
def IsOpen (_Z : WymoreSystem SZ IZ OZ) : Prop :=
  Nonempty IZ ∧ Nonempty OZ

/-- A concrete closed system: one state, no inputs, no outputs (`RZ = fun _ => none`). This is
    exactly the construction `DiscreteSystem` cannot express. -/
def closedSystem : WymoreSystem Unit Empty Empty where
  sz_nonempty := ⟨()⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => s
  RZ := fun _ => none

theorem closedSystem_isClosed : IsClosed closedSystem :=
  ⟨inferInstance, inferInstance⟩

/-- Closed (empty-output, empty-input) systems are genuinely constructible as `WymoreSystem`s.
    Contrast `not_isClosed`, which proves no `DiscreteSystem` can be closed. -/
theorem exists_closed_wymoreSystem :
    ∃ (Z : WymoreSystem Unit Empty Empty), IsClosed Z :=
  ⟨closedSystem, closedSystem_isClosed⟩

/-- A concrete *autonomous* system: empty input but nonempty output. State is a `Bool` that
    toggles every step with no input; it reads out its current state. This exercises the
    empty-input case `NZ ∈ FNS(SZ, SZ)` that `DiscreteSystem` cannot drive. -/
def toggleSystem : WymoreSystem Bool Empty Bool where
  sz_nonempty := ⟨true⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => !s
  RZ := fun s => some s

/-- `toggleSystem` has empty input yet a well-defined, nontrivial trajectory: it flips each step. -/
theorem toggle_step (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 1 = !s0 := rfl

/-- After two autonomous steps `toggleSystem` returns to its start: it has period 2. -/
theorem toggle_period_two (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 2 = s0 := by
  cases s0 <;> rfl

/-- `toggleSystem` is genuinely an empty-input system that is nonetheless not closed (it produces
    output), demonstrating the autonomous (nonempty-output) case. -/
theorem toggle_empty_input_open_output : IsEmpty Empty ∧ Nonempty Bool :=
  ⟨inferInstance, ⟨true⟩⟩

end GWymore

/-! ## Embedding: every `DiscreteSystem` is a `WymoreSystem` -/

/--
  The structure-preserving embedding of a `DiscreteSystem` into a `WymoreSystem`. Inputs are
  required (`some i` drives `Z.NZ`; the autonomous `none` step stutters), and the readout is
  `some ∘ Z.RZ`. This shows `WymoreSystem` conservatively generalizes the base development: the
  FSM theory is the always-`some`, always-output fragment.
-/
noncomputable def DiscreteSystem.toWymore {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ) : GWymore.WymoreSystem SZ IZ OZ where
  sz_nonempty := Z.sz_nonempty
  sz_finite := Fintype.ofFinite SZ
  iz_finite := Fintype.ofFinite IZ
  oz_finite := Fintype.ofFinite OZ
  NZ := fun s oi => match oi with
    | some i => Z.NZ s i
    | none => s
  RZ := fun s => some (Z.RZ s)

namespace GWymore

/-- Lifting a base input trajectory `Time → IZ` to a generalized one `Time → Option IZ`. -/
abbrev liftInput {IZ : Type} (f : ITZ IZ) : ITZW IZ := fun t => some (f t)

/-- The embedding preserves state trajectories exactly (under the lifted input). -/
theorem toWymore_state_trajectory {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateStateTrajectory Z.toWymore s0 (liftInput f) t =
      _root_.generateStateTrajectory Z s0 f t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ, _root_.generateStateTrajectory_succ, ih]
    rfl

/-- The embedding is behaviorally faithful: its (partial) output trajectory is exactly the base
    system's output trajectory wrapped in `Option.some` (under the lifted input). -/
theorem toWymore_output_trajectory {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZ IZ) (t : Time) :
    generateOutputTrajectory Z.toWymore s0 (liftInput f) t =
      some (_root_.generateOutputTrajectory Z s0 f t) := by
  show Z.toWymore.RZ (generateStateTrajectory Z.toWymore s0 (liftInput f) t)
      = some (Z.RZ (_root_.generateStateTrajectory Z s0 f t))
  rw [toWymore_state_trajectory]
  rfl

/-- The embedding of any `DiscreteSystem` always produces output, reflecting that it lands in the
    open/Moore fragment. -/
theorem toWymore_output_isSome {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZ IZ) (t : Time) :
    (generateOutputTrajectory Z.toWymore s0 (liftInput f) t).isSome = true := by
  rw [toWymore_output_trajectory]; rfl

/-! ## Main-line integration: morphisms, reachability, equivalence transfer -/

/-- A morphism of generalized systems. Input/readout maps respect the `Option` structure
    (`Option.map`), so autonomous (`none`) steps and absent outputs are preserved. -/
structure SystemMorphism
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : WymoreSystem SZ1 IZ1 OZ1) (Z2 : WymoreSystem SZ2 IZ2 OZ2) where
  /-- State mapping -/
  φS : SZ1 → SZ2
  /-- Input mapping -/
  φI : IZ1 → IZ2
  /-- Output mapping -/
  φO : OZ1 → OZ2
  /-- The state map commutes with transitions (autonomous steps map to autonomous steps). -/
  preserves_transition : ∀ s oi, φS (Z1.NZ s oi) = Z2.NZ (φS s) (oi.map φI)
  /-- The output map commutes with the partial readout. -/
  preserves_readout : ∀ s, (Z1.RZ s).map φO = Z2.RZ (φS s)

/-- A morphism preserves state trajectories. -/
theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : WymoreSystem SZ1 IZ1 OZ1} {Z2 : WymoreSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) (t : Time) :
    m.φS (generateStateTrajectory Z1 s0 f t) =
      generateStateTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ]
    rw [m.preserves_transition, ih]

/-- Main-line integration: every `DiscreteSystem` morphism lifts to a `WymoreSystem` morphism
    between the embedded systems, so the generalized morphism theory subsumes the base one. -/
noncomputable def _root_.SystemMorphism.toWymore
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type} [Finite SZ1] [Finite IZ1] [Finite OZ1]
    [Finite SZ2] [Finite IZ2] [Finite OZ2]
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : _root_.SystemMorphism Z1 Z2) : GWymore.SystemMorphism Z1.toWymore Z2.toWymore where
  φS := m.φS
  φI := m.φI
  φO := m.φO
  preserves_transition := by
    intro s oi
    cases oi with
    | none => rfl
    | some i => exact m.preserves_transition s i
  preserves_readout := by
    intro s
    show some (m.φO (Z1.RZ s)) = some (Z2.RZ (m.φS s))
    rw [m.preserves_readout]

/-- Main-line integration: reachability in a `DiscreteSystem` transfers to its embedding. -/
theorem toWymore_reachable {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ) (s0 s : SZ)
    (h : _root_.Reachable Z s0 s) : Reachable Z.toWymore s0 s := by
  obtain ⟨f, t, ht⟩ := h
  exact ⟨liftInput f, t, by rw [toWymore_state_trajectory]; exact ht⟩

/-- Main-line integration: generalized state equivalence of the embedding refines base state
    equivalence. (The converse fails in general because the generalized notion also quantifies
    over autonomous `none`-driven trajectories.) -/
theorem stateEquiv_toWymore_imp {SZ IZ OZ : Type} [Finite SZ] [Finite IZ] [Finite OZ]
    (Z : DiscreteSystem SZ IZ OZ) (s1 s2 : SZ)
    (h : StateEquiv Z.toWymore s1 s2) : _root_.StateEquiv Z s1 s2 := by
  intro f t
  have hh := h (liftInput f) t
  rw [toWymore_output_trajectory, toWymore_output_trajectory] at hh
  exact Option.some_injective _ hh

end GWymore
