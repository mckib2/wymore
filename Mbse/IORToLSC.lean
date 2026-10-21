import Mbse.LSC
import Mbse.WymoreRequirements

/-!
# Compiling input/output requirements to Universal LSCs

Two layers:

1. **Characteristic** `ofIOR` — lossless semantic encoding of every IOR
   (including infinite `ITR`) as one Universal LSC.  Satisfaction is
   definitionally `SatisfiesIOR`.
2. **Finite unroll** — drawable expansion when `OLR` is finite and `ITR` is
   presented by a finite covering list.  Outside `FiniteIOR`, only the
   characteristic chart is offered (graphical incompleteness is presentation-only).

**Honesty:** the main-chart obligation is full envelope membership `g ∈ ER(f)`,
not per-tick projections alone.  Bare pointwise `Allowed_t` is strictly weaker
when outputs are coupled across ticks (see `pointwiseProjection_weaker`).
-/

namespace IORToLSC

open Classical
open WymoreRequirements
open LSC

/-! ## Characteristic compilation (lossless) -/

/--
  Characteristic Universal LSC of an IOR.

  Pre-chart (cold): eligible inputs `ITR`.
  Main-chart (hot): full envelope `ER` (not pointwise projections).
  Diagram bodies are left empty; use `unroll` for drawable expansion.
-/
def ofIOR (R : InputOutputRequirement IR OR) : UniversalLSC IR OR where
  name := "IOR_characteristic"
  times := TSR R
  preInputs := R.itr
  allows f g := g ∈ R.er f
  preChart := ChartBody.empty
  mainChart := ChartBody.empty

/-- Characteristic LSC satisfaction is exactly Wymore `SatisfiesIOR`. -/
theorem satisfiesLSC_ofIOR_iff {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (R : InputOutputRequirement IR OR) (s0 : S) (T : Set Time) :
    Satisfies Z (ofIOR R) s0 T ↔ SatisfiesIOR Z R s0 T :=
  Iff.rfl

/-! ## Finite IOR presentation for drawable unrolling -/

/--
  Pad a length-`n` finite prefix to a total trajectory using a default value
  outside `{0, …, n-1}`.
-/
def padTraj {α : Type} (n : Nat) (u : Fin n → α) (default : α) : ITZ α :=
  fun t => if h : t < n then u ⟨t, h⟩ else default

/-- Agreement of a total trajectory with a finite prefix on `{0, …, n-1}`. -/
def agreesPrefix {α : Type} (n : Nat) (f : ITZ α) (u : Fin n → α) : Prop :=
  ∀ t : Fin n, f t.val = u t

theorem agreesPrefix_pad {α : Type} (n : Nat) (u : Fin n → α) (default : α) :
    agreesPrefix n (padTraj n u default) u := by
  intro t
  simp [padTraj, t.isLt]

theorem agreesOn_of_agreesPrefix {α : Type} {n : Nat} {hn : 0 < n}
    (f g : ITZ α) (u : Fin n → α)
    (hf : agreesPrefix n f u) (hg : agreesPrefix n g u) :
    agreesOn f g (timeScale (.finite n hn)) := by
  intro t ht
  have ht' : t < n := ht
  have hf' := hf ⟨t, ht'⟩
  have hg' := hg ⟨t, ht'⟩
  exact hf'.trans hg'.symm

/--
  A finite operational IOR equipped with an explicit finite covering of `ITR`
  by length-`n` input prefixes.  Required for constructive trie / path unrolling.
-/
structure FiniteIOR (IR OR : Type) where
  ior : InputOutputRequirement IR OR
  n : Nat
  hn : 0 < n
  holr : ior.olr = .finite n hn
  /-- Covering list of input prefixes (canonical paths through the input trie). -/
  inputs : List (Fin n → IR)
  inputs_nonempty : inputs ≠ []
  /-- Every eligible input agrees on `TSR` with some listed prefix. -/
  covers : ∀ f ∈ ior.itr, ∃ u ∈ inputs, agreesPrefix n f u
  /-- Every listed prefix is realized by some eligible input. -/
  sound : ∀ u ∈ inputs, ∃ f ∈ ior.itr, agreesPrefix n f u
  /-- Default pad value (used only outside `TSR` when building total maps). -/
  defaultIR : IR

theorem FiniteIOR.tsr_eq (F : FiniteIOR IR OR) :
    TSR F.ior = timeScale (.finite F.n F.hn) := by
  simp [TSR, F.holr]

/-! ## Diagrammatic path expansion -/

/-- Pre-chart messages for a concrete input prefix (Env → Sys, cold). -/
def preChartOfPrefix {IR OR : Type} (n : Nat) (u : Fin n → IR) :
    ChartBody IR OR where
  elements :=
    (List.finRange n).map fun t =>
      Element.inMsg .cold t.val (u t)

/--
  Main-chart diagram for a path: tick syncs plus a hot full-envelope condition.
  Semantic kernel remains full `ER` membership (not pointwise projections).
-/
def mainChartOfPath {IR OR : Type} (n : Nat) (pathId : Nat) :
    ChartBody IR OR where
  elements :=
    (List.finRange n).map (fun t => Element.tickSync t.val) ++
      [Element.condition .hot none s!"g ∈ ER(f_path_{pathId})"]

/-- One Universal LSC for a single input path (prefix class). -/
def pathChart (F : FiniteIOR IR OR) (u : Fin F.n → IR) (pathId : Nat) :
    UniversalLSC IR OR where
  name := s!"IOR_Spec_path_{pathId}"
  times := TSR F.ior
  preInputs := {f | f ∈ F.ior.itr ∧ agreesPrefix F.n f u}
  allows := fun f g => g ∈ F.ior.er f
  preChart := preChartOfPrefix F.n u
  mainChart := mainChartOfPath (OR := OR) F.n pathId

/--
  Constructive unroll: one Universal LSC per listed input prefix.
  Diagrammatic `pathId` is unused for satisfaction (semantic kernel is path-independent
  of the label); callers may renumber for rendering.
-/
def unroll (F : FiniteIOR IR OR) : List (UniversalLSC IR OR) :=
  F.inputs.map (fun u => pathChart F u 0)

/-! ## Unroll equivalence -/

theorem pathChart_times (F : FiniteIOR IR OR) (u : Fin F.n → IR) (pathId : Nat) :
    (pathChart F u pathId).times = TSR F.ior :=
  rfl

theorem satisfies_pathChart_of_satisfiesIOR {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (F : FiniteIOR IR OR) (s0 : S) (T : Set Time)
    (hSat : SatisfiesIOR Z F.ior s0 T) (u : Fin F.n → IR) (pathId : Nat) :
    Satisfies Z (pathChart F u pathId) s0 T := by
  obtain ⟨hNE, hSub, hAll⟩ := hSat
  refine ⟨hNE, hSub, ?_⟩
  intro f hf h hAgr
  obtain ⟨hfItr, _hfPref⟩ := hf
  exact hAll f hfItr h hAgr

theorem satisfiesChartSet_unroll_of_satisfiesIOR {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (F : FiniteIOR IR OR) (s0 : S) (T : Set Time)
    (hSat : SatisfiesIOR Z F.ior s0 T) :
    SatisfiesChartSet Z (unroll F) s0 T := by
  intro chart hChart
  simp only [unroll, List.mem_map] at hChart
  obtain ⟨u, _hu, rfl⟩ := hChart
  exact satisfies_pathChart_of_satisfiesIOR Z F s0 T hSat u 0

theorem satisfiesIOR_of_satisfiesChartSet_unroll {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (F : FiniteIOR IR OR) (s0 : S) (T : Set Time)
    (hNE : T.Nonempty) (hSub : T ⊆ TSR F.ior)
    (hCharts : SatisfiesChartSet Z (unroll F) s0 T) :
    SatisfiesIOR Z F.ior s0 T := by
  refine ⟨hNE, hSub, ?_⟩
  intro f hf h hAgr
  obtain ⟨u, huIn, hPref⟩ := F.covers f hf
  have hMem : pathChart F u 0 ∈ unroll F := by
    simp only [unroll, List.mem_map]
    exact ⟨u, huIn, rfl⟩
  have hSatC := hCharts (pathChart F u 0) hMem
  obtain ⟨_, _, hAll⟩ := hSatC
  have hfPre : f ∈ (pathChart F u 0).preInputs := ⟨hf, hPref⟩
  exact hAll f hfPre h hAgr

/-- Finite unroll preserves IOR meaning: chart-set satisfaction ↔ `SatisfiesIOR`. -/
theorem unroll_equiv_ofIOR {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (F : FiniteIOR IR OR) (s0 : S) (T : Set Time)
    (hNE : T.Nonempty) (hSub : T ⊆ TSR F.ior) :
    SatisfiesChartSet Z (unroll F) s0 T ↔ SatisfiesIOR Z F.ior s0 T := by
  constructor
  · intro h
    exact satisfiesIOR_of_satisfiesChartSet_unroll Z F s0 T hNE hSub h
  · intro h
    exact satisfiesChartSet_unroll_of_satisfiesIOR Z F s0 T h

theorem unroll_equiv_characteristic {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (F : FiniteIOR IR OR) (s0 : S) (T : Set Time)
    (hNE : T.Nonempty) (hSub : T ⊆ TSR F.ior) :
    SatisfiesChartSet Z (unroll F) s0 T ↔ Satisfies Z (ofIOR F.ior) s0 T := by
  rw [unroll_equiv_ofIOR Z F s0 T hNE hSub, satisfiesLSC_ofIOR_iff]

/-! ## Pointwise projection is strictly weaker -/

/-- Per-tick projection of an eligible set (the algorithm's `Allowed_t`). -/
def pointwiseAllowed {OR : Type} (G : Set (ITZ OR)) (t : Time) : Set OR :=
  {y | ∃ g ∈ G, g t = y}

/--
  Pointwise tick membership: at every `t ∈ T`, the value `g t` lies in the
  projected envelope.  This ignores cross-tick coupling in `ER(f)`.
-/
def PointwiseInEnvelope {OR : Type} (G : Set (ITZ OR)) (g : ITZ OR)
    (T : Set Time) : Prop :=
  ∀ t ∈ T, g t ∈ pointwiseAllowed G t

/-- Coupled envelope on horizon `{0,1}`: exactly one of `g 0`, `g 1` is `true`. -/
def coupledEnvelope : Set (ITZ Bool) :=
  {g | (g 0 = true ∧ g 1 = false) ∨ (g 0 = false ∧ g 1 = true)}

/-- A trajectory that is pointwise admissible but not in the coupled envelope. -/
def badPointwise : ITZ Bool := fun _ => true

theorem badPointwise_pointwise_ok :
    PointwiseInEnvelope coupledEnvelope badPointwise {t | t < 2} := by
  intro t ht
  match t with
  | 0 =>
    refine ⟨fun n => decide (n = 0), ?_, rfl⟩
    · left
      simp
  | 1 =>
    refine ⟨fun n => decide (n = 1), ?_, rfl⟩
    · right
      simp
  | t + 2 =>
    exact absurd ht (Nat.not_lt_of_le (Nat.le_add_left 2 t))

theorem badPointwise_not_in_envelope : badPointwise ∉ coupledEnvelope := by
  simp [coupledEnvelope, badPointwise]

/--
  Honesty witness: satisfying all per-tick projected hot conditions does **not**
  imply full envelope membership when `ER` couples ticks.
-/
theorem pointwiseProjection_weaker :
    PointwiseInEnvelope coupledEnvelope badPointwise {t | t < 2} ∧
      badPointwise ∉ coupledEnvelope :=
  ⟨badPointwise_pointwise_ok, badPointwise_not_in_envelope⟩

/-! ## Examples -/

/-- Constant-false total trajectory. -/
def constFalse : ITZ Bool := fun _ => false

/-- Constant-false finite IOR of length 2 (single input path, singleton envelope). -/
noncomputable def constFalseFinIOR : FiniteIOR Bool Bool where
  ior :=
    { olr := .finite 2 (by decide)
      itr := {constFalse}
      otr := {constFalse}
      er := fun _ => {constFalse}
      itr_nonempty := ⟨constFalse, rfl⟩
      otr_nonempty := ⟨constFalse, rfl⟩
      er_subset := by
        intro f hf g hg
        simpa [Set.mem_singleton_iff] using hg
      er_nonempty := by
        intro f _
        exact ⟨constFalse, rfl⟩
      otr_from_er := by
        intro g hg
        exact ⟨constFalse, rfl, hg⟩ }
  n := 2
  hn := by decide
  holr := rfl
  inputs := [fun _ => false]
  inputs_nonempty := by decide
  covers := by
    intro f hf
    refine ⟨fun _ => false, List.mem_singleton.mpr rfl, ?_⟩
    intro t
    simp only [Set.mem_singleton_iff] at hf
    subst hf
    rfl
  sound := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    exact ⟨constFalse, rfl, fun _ => rfl⟩
  defaultIR := false

/-- Characteristic LSC for the infinite echo IOR (no finite complete unroll). -/
noncomputable def echoCharacteristic : UniversalLSC Bool Bool :=
  ofIOR echoIOR

theorem echo_characteristic_iff {S : Type} (Z : DiscreteSystem S Bool Bool)
    (s0 : S) (T : Set Time) :
    Satisfies Z echoCharacteristic s0 T ↔ SatisfiesIOR Z echoIOR s0 T :=
  satisfiesLSC_ofIOR_iff Z echoIOR s0 T

/-- Unroll of the constant-false finite IOR yields a singleton chart list. -/
theorem constFalseFinIOR_unroll_length : (unroll constFalseFinIOR).length = 1 := by
  simp [unroll, constFalseFinIOR]

/-- Constant-false readout system satisfies the finite IOR / its unroll. -/
def constFalseSystem : DiscreteSystem Unit Bool Bool :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ => false) ⟨()⟩

theorem constFalse_tsr_subset :
    {t | t < 2} ⊆ TSR constFalseFinIOR.ior := by
  intro t ht
  simpa [TSR, constFalseFinIOR, timeScale] using ht

theorem constFalseSystem_satisfies_finIOR :
    SatisfiesIOR constFalseSystem constFalseFinIOR.ior () {t | t < 2} := by
  refine ⟨⟨0, by decide⟩, constFalse_tsr_subset, ?_⟩
  intro f _hf h _hAgr
  refine ⟨constFalse, ?_, ?_⟩
  · simp [constFalseFinIOR]
  · intro t _ht
    simp [generateOutputTrajectory, constFalseSystem, DiscreteSystem.ofTotal, constFalse]

theorem constFalseSystem_satisfies_unroll :
    SatisfiesChartSet constFalseSystem (unroll constFalseFinIOR) () {t | t < 2} :=
  (unroll_equiv_ofIOR constFalseSystem constFalseFinIOR () {t | t < 2}
    ⟨0, by decide⟩ constFalse_tsr_subset).mpr
    constFalseSystem_satisfies_finIOR

end IORToLSC
