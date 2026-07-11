import Mbse.WymoreExercises
import Mbse.PartialDynamicsHomFragment
import Mbse.HomWitnessConstruction
import Mbse.Homomorphism
import Mbse.FiniteWymore
import Mathlib.Data.Real.Basic

/-!
# Cascade composition gallery (awkward buildability)

Available kit:
* ones-counters
* `01110` recognizer / shift-register v3
* dual-port select (`01` short / `01110` long)
* real accumulator (`δ(s,u)=s+u` over `ℝ`)

Cascade intent:
1. Recognize the **10-bit** concatenation `0111001110` (`01110` then `01110`),
   assembled from two shelf `01110` matchers + a ones-counter arm latch.
2. On each full-string accept, advance accept-count `n` with readout **`3n`**,
   assembled as `Plus3Assembled` (three ones-counters + real accumulator sum).

Gallery only: the paper case-study spine is Fibonacci composition in
[`FibCaseStudy`](FibCaseStudy.lean). Main-text prose must not name Lean.
-/

namespace ComposedCaseStudy

open Homomorphism PartialDynamicsHomFragment HomWitnessConstruction
  WymoreExercises FSM

private def bitNat (b : Bit) : Nat := if b then 1 else 0

private def onesInc (n : Nat) (accept : Bit) : Nat := n + bitNat accept

/-! ## Double-`01110` recognizer (spec table + kit assembly) -/

/-- Phase `false`: matching the first `01110`. Phase `true`: matching the second.
    On completing the second half, reset to the first half for the next occurrence. -/
structure Double01110SpecState where
  phase : Bool
  progress : MatchState
  deriving DecidableEq

/-- True when this step completes a full `0111001110` (second-half accept). -/
def double01110JustAccepted (s : Double01110SpecState) (b : Bit) : Bit :=
  decide (s.phase ∧ pattern01110Out (pattern01110Next s.progress b))

def double01110SpecNext (s : Double01110SpecState) (b : Bit) : Double01110SpecState :=
  if s.phase then
    let q' := pattern01110Next s.progress b
    if pattern01110Out q' then ⟨false, 0⟩ else ⟨true, q'⟩
  else
    let q' := pattern01110Next s.progress b
    if pattern01110Out q' then ⟨true, 0⟩ else ⟨false, q'⟩

/-- Awkward recognizer: first/second shelf matchers and a ones-counter arm latch. -/
structure Double01110Assembled where
  first : MatchState
  second : MatchState
  /-- Ones-counter arm: positive while matching the second half. -/
  armed : Nat

def Double01110Assembled.empty : Double01110Assembled := ⟨0, 0, 0⟩

/-- Bit fans to `first` always; `second` held at `0` until armed; clear arm on full accept. -/
def Double01110Assembled.step (s : Double01110Assembled) (b : Bit) : Double01110Assembled :=
  let first' := pattern01110Next s.first b
  let second' : MatchState :=
    if s.armed = 0 then 0 else pattern01110Next s.second b
  let justAcc : Bit := decide (s.armed ≠ 0 ∧ pattern01110Out second')
  if justAcc then
    ⟨0, 0, 0⟩
  else if s.armed = 0 then
    ⟨first', 0, onesInc 0 (pattern01110Out first')⟩
  else
    ⟨first', second', s.armed⟩

def Double01110Assembled.justAccepted (s : Double01110Assembled) (b : Bit) : Bit :=
  let second' : MatchState :=
    if s.armed = 0 then 0 else pattern01110Next s.second b
  decide (s.armed ≠ 0 ∧ pattern01110Out second')

def doubleHS (s : Double01110Assembled) : Double01110SpecState :=
  if s.armed = 0 then ⟨false, s.first⟩ else ⟨true, s.second⟩

theorem double_preserves_transition (s : Double01110Assembled) (b : Bit) :
    doubleHS (Double01110Assembled.step s b) = double01110SpecNext (doubleHS s) b := by
  rcases s with ⟨first, second, armed⟩
  simp only [doubleHS, Double01110Assembled.step, double01110SpecNext]
  by_cases hz : armed = 0
  · subst hz
    simp only [onesInc, bitNat]
    by_cases hacc : pattern01110Out (pattern01110Next first b)
    · simp [hacc]
    · simp [hacc]
  · have hpos : ¬ armed = 0 := hz
    simp only [if_neg hpos]
    by_cases hacc : pattern01110Out (pattern01110Next second b)
    · simp [hacc, hpos]
    · simp [hacc, hpos]

theorem double_preserves_justAccepted (s : Double01110Assembled) (b : Bit) :
    Double01110Assembled.justAccepted s b = double01110JustAccepted (doubleHS s) b := by
  rcases s with ⟨first, second, armed⟩
  simp only [Double01110Assembled.justAccepted, double01110JustAccepted, doubleHS,
    pattern01110Out]
  by_cases hz : armed = 0
  · simp [hz]
  · simp [hz]

/-! ## `Plus3Assembled`: three ones + kit real accumulator as summing block -/

/-- One add step of the kit real accumulator. -/
noncomputable def realAccStep (s u : ℝ) : ℝ :=
  realAccumulator.NZ s (some u)

/-- Re-sum three Nat outputs by three kit-accumulator steps from `0`. -/
noncomputable def realSum3 (a b c : Nat) : ℝ :=
  realAccStep (realAccStep (realAccStep (0 : ℝ) (a : ℝ)) (b : ℝ)) (c : ℝ)

private theorem realAccStep_eq (s u : ℝ) : realAccStep s u = s + u := by
  simp [realAccStep, realAccumulator, DiscreteSystem.ofTotal]

private theorem realSum3_eq (a b c : Nat) :
    realSum3 a b c = ((a + b + c : Nat) : ℝ) := by
  unfold realSum3
  simp only [realAccStep_eq, zero_add]
  norm_cast

structure Plus3Assembled where
  ones1 : Nat
  ones2 : Nat
  ones3 : Nat
  sum : ℝ
  synced : ones1 = ones2 ∧ ones2 = ones3
  sum_eq : sum = realSum3 ones1 ones2 ones3

noncomputable def Plus3Assembled.empty : Plus3Assembled :=
  ⟨0, 0, 0, realSum3 0 0 0, ⟨rfl, rfl⟩, rfl⟩

noncomputable def Plus3Assembled.step (s : Plus3Assembled) (accept : Bit) : Plus3Assembled :=
  ⟨onesInc s.ones1 accept, onesInc s.ones2 accept, onesInc s.ones3 accept,
   realSum3 (onesInc s.ones1 accept) (onesInc s.ones2 accept) (onesInc s.ones3 accept),
   by
     rcases s.synced with ⟨h12, h23⟩
     constructor
     · simp [onesInc, bitNat, h12]
     · simp [onesInc, bitNat, h23],
   rfl⟩

noncomputable def Plus3Assembled.out (s : Plus3Assembled) : ℝ := s.sum

noncomputable def plus3FromOnes : DiscreteSystem Plus3Assembled Bit ℝ :=
  DiscreteSystem.ofTotal Plus3Assembled.step Plus3Assembled.out ⟨Plus3Assembled.empty⟩

theorem Plus3Assembled.out_eq_mul3 (s : Plus3Assembled) :
    Plus3Assembled.out s = ((3 * s.ones1 : Nat) : ℝ) := by
  have hs := s.sum_eq
  rcases s.synced with ⟨h12, h23⟩
  calc
    Plus3Assembled.out s = realSum3 s.ones1 s.ones2 s.ones3 := by
      simpa [Plus3Assembled.out] using hs
    _ = ((s.ones1 + s.ones2 + s.ones3 : Nat) : ℝ) := realSum3_eq _ _ _
    _ = ((s.ones1 + s.ones1 + s.ones1 : Nat) : ℝ) := by
      simp [h12, h23]
    _ = ((3 * s.ones1 : Nat) : ℝ) := by
      norm_cast
      omega

/-! ## Cascade: double-`01110` accept → count with readout `3n` -/

def cascadeSpecNext (s : Double01110SpecState × Nat) (b : Bit) : Double01110SpecState × Nat :=
  let rec' := double01110SpecNext s.1 b
  let n' := if double01110JustAccepted s.1 b then s.2 + 1 else s.2
  (rec', n')

noncomputable def cascadeSpec : DiscreteSystem (Double01110SpecState × Nat) Bit ℝ :=
  DiscreteSystem.ofTotal cascadeSpecNext (fun s => ((3 * s.2 : Nat) : ℝ)) ⟨(⟨false, 0⟩, 0)⟩

noncomputable def cascadeAwkwardNext (s : Double01110Assembled × Plus3Assembled) (b : Bit) :
    Double01110Assembled × Plus3Assembled :=
  let acc := Double01110Assembled.justAccepted s.1 b
  (Double01110Assembled.step s.1 b, Plus3Assembled.step s.2 acc)

noncomputable def cascadeAwkwardImpl :
    DiscreteSystem (Double01110Assembled × Plus3Assembled) Bit ℝ :=
  DiscreteSystem.ofTotal cascadeAwkwardNext (fun s => Plus3Assembled.out s.2)
    ⟨(Double01110Assembled.empty, Plus3Assembled.empty)⟩

def cascadeHS (s : Double01110Assembled × Plus3Assembled) : Double01110SpecState × Nat :=
  (doubleHS s.1, s.2.ones1)

theorem cascadeAwkward_preserves_transition
    (s : Double01110Assembled × Plus3Assembled) (b : Bit) :
    cascadeHS (cascadeAwkwardNext s b) = cascadeSpecNext (cascadeHS s) b := by
  rcases s with ⟨rec, cnt⟩
  simp only [cascadeHS, cascadeAwkwardNext, cascadeSpecNext]
  have hrec := double_preserves_transition rec b
  have hacc := double_preserves_justAccepted rec b
  simp only [hrec, hacc, Plus3Assembled.step, onesInc, bitNat]
  by_cases h : double01110JustAccepted (doubleHS rec) b
  · simp [h]
  · simp [h]

theorem cascadeAwkward_preserves_readout (s : Double01110Assembled × Plus3Assembled) :
    Plus3Assembled.out s.2 = ((3 * (cascadeHS s).2 : Nat) : ℝ) := by
  simpa [cascadeHS] using Plus3Assembled.out_eq_mul3 s.2

noncomputable def cascadeAwkward_witness :
    HomomorphicImageWitness cascadeSpec cascadeAwkwardImpl where
  HS := cascadeHS
  HI := id
  HO := id
  HS_surjective := by
    intro qc
    rcases qc with ⟨rec, n⟩
    rcases rec with ⟨phase, progress⟩
    cases phase with
    | false =>
      refine ⟨(⟨progress, 0, 0⟩,
        ⟨n, n, n, realSum3 n n n, ⟨rfl, rfl⟩, rfl⟩), ?_⟩
      simp [cascadeHS, doubleHS]
    | true =>
      refine ⟨(⟨0, progress, 1⟩,
        ⟨n, n, n, realSum3 n n n, ⟨rfl, rfl⟩, rfl⟩), ?_⟩
      simp [cascadeHS, doubleHS]
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun s oi => by
    cases oi with
    | none => simp [cascadeAwkwardImpl, cascadeSpec, DiscreteSystem.ofTotal, cascadeHS]
    | some b =>
      simp [cascadeAwkwardImpl, cascadeSpec, DiscreteSystem.ofTotal,
        cascadeAwkward_preserves_transition]
  preserves_readout := fun s => by
    simp [cascadeAwkwardImpl, cascadeSpec, DiscreteSystem.ofTotal, cascadeHS,
      Option.map_some, cascadeAwkward_preserves_readout]

theorem cascadeAwkward_hom :
    IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  ⟨cascadeAwkward_witness⟩

theorem cascadeAwkward_satisfies :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl :=
  partialDynamicsHom_of_hom cascadeAwkward_hom

theorem cascadeAwkward_iff_hom :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl ↔
      IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  partialDynamicsHom_iff_hom

theorem cascade_caseStudy_playbook :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl ↔
      IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  cascadeAwkward_iff_hom

end ComposedCaseStudy
