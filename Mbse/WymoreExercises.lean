import Mbse.PartialDynamicsHomFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.HomWitnessConstruction
import Mbse.FSMProperties
import Mbse.FiniteWymore
import Mbse.Homomorphism
import Mathlib.Data.Real.Basic

/-!
# Wymore textbook exercises and paper case-study systems

Faithful encodings for:
* Exercise 2.128 — count of 1-inputs (`onesCounter`)
* Exercise 2.129 — recognize string `01110` (`pattern01110`)
* Light extension — dual-port pattern select among two fixed strings
* Real accumulator — discrete-time running sum over `ℝ`

These support the paper case studies. Main-text prose must not name Lean.
-/

namespace WymoreExercises

open Homomorphism ExtensionalDynamicsFragment PartialDynamicsHomFragment
  FSM FSMProperties HomWitnessConstruction

/-! ## Exercise 2.128: count of ones -/

/-- Input alphabet `{0,1}` as `Bool` (`false` = 0, `true` = 1). -/
abbrev Bit := Bool

/-- Wymore 2.128: state = number of 1s seen; output = that count. -/
def onesCounter : DiscreteSystem Nat Bit Nat :=
  DiscreteSystem.ofTotal
    (fun n b => if b then n + 1 else n)
    id
    ⟨0⟩

theorem onesCounter_alwaysOutputs : AlwaysOutputs onesCounter :=
  ofTotal_alwaysOutputs _ _ _

/-- Spec-aligned buildable (same table). -/
def onesCounterDirect : DiscreteSystem Nat Bit Nat := onesCounter

/-- Elaborated buildable: richer state `(count, lastBit)` projecting to the count. -/
def onesCounterElab : DiscreteSystem (Nat × Bit) Bit Nat :=
  DiscreteSystem.ofTotal
    (fun (n, _) b => (if b then n + 1 else n, b))
    (fun (n, _) => n)
    ⟨(0, false)⟩

theorem onesCounterElab_alwaysOutputs : AlwaysOutputs onesCounterElab :=
  ofTotal_alwaysOutputs _ _ _

def onesCounterElab_witness : HomomorphicImageWitness onesCounter onesCounterElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun n => ⟨(n, false), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨n, _⟩ oi => by
    cases oi with
    | none => simp [onesCounterElab, onesCounter, DiscreteSystem.ofTotal]
    | some b => simp [onesCounterElab, onesCounter, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨n, _⟩ => by
    simp [onesCounterElab, onesCounter, DiscreteSystem.ofTotal, Option.map_some]

theorem onesCounterElab_hom :
    IsHomomorphicImage onesCounter onesCounterElab :=
  ⟨onesCounterElab_witness⟩

theorem onesCounterElab_satisfies_partialDynamicsHom :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterElab :=
  partialDynamicsHom_of_hom onesCounterElab_hom

theorem onesCounterElab_iff_hom :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterElab ↔
      IsHomomorphicImage onesCounter onesCounterElab :=
  partialDynamicsHom_iff_hom

theorem onesCounter_satisfies_self :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterDirect :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [onesCounterDirect, onesCounter, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [onesCounterDirect, onesCounter, DiscreteSystem.ofTotal]
  }⟩

theorem onesCounter_reflexive_iff_hom :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterDirect ↔
      IsHomomorphicImage onesCounter onesCounterDirect :=
  partialDynamicsHom_iff_hom

/-- Medium buildable: track ones and zeros; project to ones-count. -/
def onesCounterBoth : DiscreteSystem (Nat × Nat) Bit Nat :=
  DiscreteSystem.ofTotal
    (fun (ones, zeros) b =>
      if b then (ones + 1, zeros) else (ones, zeros + 1))
    (fun (ones, _) => ones)
    ⟨(0, 0)⟩

def onesCounterBoth_witness : HomomorphicImageWitness onesCounter onesCounterBoth where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun n => ⟨(n, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨ones, zeros⟩ oi => by
    cases oi with
    | none => simp [onesCounterBoth, onesCounter, DiscreteSystem.ofTotal]
    | some b =>
      cases b <;> simp [onesCounterBoth, onesCounter, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨ones, _⟩ => by
    simp [onesCounterBoth, onesCounter, DiscreteSystem.ofTotal, Option.map_some]

theorem onesCounterBoth_hom :
    IsHomomorphicImage onesCounter onesCounterBoth :=
  ⟨onesCounterBoth_witness⟩

theorem onesCounterBoth_satisfies :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterBoth :=
  partialDynamicsHom_of_hom onesCounterBoth_hom

theorem onesCounterBoth_iff_hom :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterBoth ↔
      IsHomomorphicImage onesCounter onesCounterBoth :=
  partialDynamicsHom_iff_hom

/-- Complex buildable: ones-count, tick count, last bit, and a free shadow Nat.
    Only the ones-count is visible to the reference via `HS`. -/
def onesCounterRich : DiscreteSystem (Nat × Nat × Bit × Nat) Bit Nat :=
  DiscreteSystem.ofTotal
    (fun (ones, ticks, _, shadow) b =>
      (if b then ones + 1 else ones, ticks + 1, b, shadow + ones))
    (fun (ones, _, _, _) => ones)
    ⟨(0, 0, false, 0)⟩

def onesCounterRich_witness : HomomorphicImageWitness onesCounter onesCounterRich where
  HS := fun ⟨ones, _, _, _⟩ => ones
  HI := id
  HO := id
  HS_surjective := fun n => ⟨(n, 0, false, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨ones, ticks, last, shadow⟩ oi => by
    cases oi with
    | none => simp [onesCounterRich, onesCounter, DiscreteSystem.ofTotal]
    | some b =>
      cases b <;> simp [onesCounterRich, onesCounter, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨ones, _, _, _⟩ => by
    simp [onesCounterRich, onesCounter, DiscreteSystem.ofTotal, Option.map_some]

theorem onesCounterRich_hom :
    IsHomomorphicImage onesCounter onesCounterRich :=
  ⟨onesCounterRich_witness⟩

theorem onesCounterRich_satisfies :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterRich :=
  partialDynamicsHom_of_hom onesCounterRich_hom

theorem onesCounterRich_iff_hom :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterRich ↔
      IsHomomorphicImage onesCounter onesCounterRich :=
  partialDynamicsHom_iff_hom

/-! ## Exercise 2.129: recognize `01110` -/

/-- Progress matching prefix of `01110` (length 5); state `5` means just matched. -/
abbrev MatchState := Fin 6

/-- Next match state after reading bit `b` from progress `q`. -/
def pattern01110Next (q : MatchState) (b : Bit) : MatchState :=
  match q.val, b with
  | 0, false => 1
  | 0, true  => 0
  | 1, false => 1
  | 1, true  => 2
  | 2, false => 1
  | 2, true  => 3
  | 3, false => 1
  | 3, true  => 4
  | 4, false => 5
  | 4, true  => 0
  | 5, false => 1
  | 5, true  => 0
  | _, _ => 0

def pattern01110Out (q : MatchState) : Bit :=
  decide (q.val = 5)

/-- Finite Moore reference for Wymore 2.129. -/
def pattern01110FSM : FSMSystem MatchState Bit Bit where
  sz_nonempty := ⟨0⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := pattern01110Next
  RZ := pattern01110Out

def pattern01110 : DiscreteSystem MatchState Bit Bit :=
  pattern01110FSM.toDiscreteSystem

def pattern01110Direct : DiscreteSystem MatchState Bit Bit := pattern01110

/-- Elaborated buildable: match progress plus last input bit. -/
def pattern01110Elab : DiscreteSystem (MatchState × Bit) Bit Bit :=
  DiscreteSystem.ofTotal
    (fun (q, _) b => (pattern01110Next q b, b))
    (fun (q, _) => pattern01110Out q)
    ⟨(0, false)⟩

def pattern01110Elab_witness :
    HomomorphicImageWitness pattern01110 pattern01110Elab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun q => ⟨(q, false), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨q, _⟩ oi => by
    cases oi with
    | none =>
      simp [pattern01110Elab, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    | some b =>
      simp [pattern01110Elab, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨q, _⟩ => by
    simp [pattern01110Elab, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
      DiscreteSystem.ofTotal, Option.map_some, pattern01110Out]

theorem pattern01110Elab_hom :
    IsHomomorphicImage pattern01110 pattern01110Elab :=
  ⟨pattern01110Elab_witness⟩

theorem pattern01110Elab_iff_hom :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Elab ↔
      IsHomomorphicImage pattern01110 pattern01110Elab :=
  partialDynamicsHom_iff_hom

theorem pattern01110Elab_satisfies :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Elab :=
  partialDynamicsHom_of_hom pattern01110Elab_hom

/-- Exhibit/verify maps for the elaboration (finite-tier reconstruction narrative). -/
theorem pattern01110Elab_maps_verified :
    IsHomomorphicImage pattern01110 pattern01110Elab :=
  tryConstructHomWitness_is_hom
    (Prod.fst : MatchState × Bit → MatchState) id id
    (fun s oi => by
      rcases s with ⟨q, _⟩
      cases oi with
      | none =>
        simp [pattern01110Elab, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
      | some b =>
        simp [pattern01110Elab, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
          DiscreteSystem.ofTotal])
    (fun s => by
      rcases s with ⟨q, _⟩
      simp [pattern01110Elab, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal, Option.map_some, pattern01110Out])
    (fun q => ⟨(q, false), rfl⟩)
    Function.surjective_id
    Function.surjective_id

theorem pattern01110_satisfies_self :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Direct :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [pattern01110Direct, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [pattern01110Direct, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
  }⟩

theorem pattern01110_direct_iff_hom :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Direct ↔
      IsHomomorphicImage pattern01110 pattern01110Direct :=
  partialDynamicsHom_iff_hom

/-- Medium buildable: progress plus a parallel mod-6 ones counter (shadow). -/
def pattern01110Shadow : DiscreteSystem (MatchState × Fin 6) Bit Bit :=
  DiscreteSystem.ofTotal
    (fun (q, c) b =>
      (pattern01110Next q b,
        if b then ⟨(c.val + 1) % 6, by omega⟩ else c))
    (fun (q, _) => pattern01110Out q)
    ⟨(0, 0)⟩

def pattern01110Shadow_witness :
    HomomorphicImageWitness pattern01110 pattern01110Shadow where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun q => ⟨(q, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨q, c⟩ oi => by
    cases oi with
    | none =>
      simp [pattern01110Shadow, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    | some b =>
      simp [pattern01110Shadow, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨q, _⟩ => by
    simp [pattern01110Shadow, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
      DiscreteSystem.ofTotal, Option.map_some, pattern01110Out]

theorem pattern01110Shadow_hom :
    IsHomomorphicImage pattern01110 pattern01110Shadow :=
  ⟨pattern01110Shadow_witness⟩

theorem pattern01110Shadow_satisfies :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shadow :=
  partialDynamicsHom_of_hom pattern01110Shadow_hom

theorem pattern01110Shadow_iff_hom :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shadow ↔
      IsHomomorphicImage pattern01110 pattern01110Shadow :=
  partialDynamicsHom_iff_hom

/-- Complex buildable: progress, last bit, tick count, and a free log length.
    Projects to match progress only. -/
def pattern01110Rich : DiscreteSystem (MatchState × Bit × Nat × Nat) Bit Bit :=
  DiscreteSystem.ofTotal
    (fun (q, _, ticks, logLen) b =>
      (pattern01110Next q b, b, ticks + 1, logLen + 1))
    (fun (q, _, _, _) => pattern01110Out q)
    ⟨(0, false, 0, 0)⟩

def pattern01110Rich_witness :
    HomomorphicImageWitness pattern01110 pattern01110Rich where
  HS := fun ⟨q, _, _, _⟩ => q
  HI := id
  HO := id
  HS_surjective := fun q => ⟨(q, false, 0, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨q, last, ticks, logLen⟩ oi => by
    cases oi with
    | none =>
      simp [pattern01110Rich, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    | some b =>
      simp [pattern01110Rich, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨q, _, _, _⟩ => by
    simp [pattern01110Rich, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
      DiscreteSystem.ofTotal, Option.map_some, pattern01110Out]

theorem pattern01110Rich_hom :
    IsHomomorphicImage pattern01110 pattern01110Rich :=
  ⟨pattern01110Rich_witness⟩

theorem pattern01110Rich_satisfies :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Rich :=
  partialDynamicsHom_of_hom pattern01110Rich_hom

theorem pattern01110Rich_maps_verified :
    IsHomomorphicImage pattern01110 pattern01110Rich :=
  tryConstructHomWitness_is_hom
    (fun (s : MatchState × Bit × Nat × Nat) => s.1) id id
    (fun s oi => by
      rcases s with ⟨q, last, ticks, logLen⟩
      cases oi with
      | none =>
        simp [pattern01110Rich, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
      | some b =>
        simp [pattern01110Rich, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
          DiscreteSystem.ofTotal])
    (fun s => by
      rcases s with ⟨q, _, _, _⟩
      simp [pattern01110Rich, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal, Option.map_some, pattern01110Out])
    (fun q => ⟨(q, false, 0, 0), rfl⟩)
    Function.surjective_id
    Function.surjective_id

theorem pattern01110Rich_iff_hom :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Rich ↔
      IsHomomorphicImage pattern01110 pattern01110Rich :=
  partialDynamicsHom_iff_hom

/-! ## Light extension: dual-port pattern select -/

/-- `(mode, data)`: `mode = true` tracks `01110`; `mode = false` tracks short pattern `01`. -/
abbrev SelectInput := Bit × Bit

def dualPatternNext (q : MatchState) (inp : SelectInput) : MatchState :=
  let mode := inp.1
  let b := inp.2
  if mode then pattern01110Next q b
  else
    match q.val, b with
    | 0, false => 1
    | 0, true => 0
    | 1, true => 2
    | 1, false => 1
    | 2, false => 1
    | 2, true => 0
    | _, _ => 0

/-- Accept pulse: state 5 (`01110`) or state 2 (short `01`). -/
def dualPatternOut (q : MatchState) : Bit :=
  decide (q.val = 5 ∨ q.val = 2)

def dualPatternSpec : DiscreteSystem MatchState SelectInput Bit :=
  DiscreteSystem.ofTotal dualPatternNext dualPatternOut ⟨0⟩

def dualPatternDirect : DiscreteSystem MatchState SelectInput Bit := dualPatternSpec

def dualPatternElab : DiscreteSystem (MatchState × Bit) SelectInput Bit :=
  DiscreteSystem.ofTotal
    (fun (q, _) inp => (dualPatternNext q inp, inp.1))
    (fun (q, _) => dualPatternOut q)
    ⟨(0, false)⟩

def dualPatternElab_witness :
    HomomorphicImageWitness dualPatternSpec dualPatternElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun q => ⟨(q, false), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨q, _⟩ oi => by
    cases oi with
    | none => simp [dualPatternElab, dualPatternSpec, DiscreteSystem.ofTotal]
    | some inp => simp [dualPatternElab, dualPatternSpec, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨q, _⟩ => by
    simp [dualPatternElab, dualPatternSpec, DiscreteSystem.ofTotal, Option.map_some]

theorem dualPatternElab_hom :
    IsHomomorphicImage dualPatternSpec dualPatternElab :=
  ⟨dualPatternElab_witness⟩

theorem dualPatternElab_iff_hom :
    SystemSatisfiesPartialDynamicsHom dualPatternSpec dualPatternElab ↔
      IsHomomorphicImage dualPatternSpec dualPatternElab :=
  partialDynamicsHom_iff_hom

theorem dualPatternElab_satisfies :
    SystemSatisfiesPartialDynamicsHom dualPatternSpec dualPatternElab :=
  partialDynamicsHom_of_hom dualPatternElab_hom

/-! ## Real accumulator (discrete clock, real-valued state) -/

/-- Running sum: `δ(s,u) = s + u`, readout = state. Noncomputable over `ℝ`. -/
noncomputable def realAccumulator : DiscreteSystem ℝ ℝ ℝ :=
  DiscreteSystem.ofTotal (fun s u => s + u) id ⟨(0 : ℝ)⟩

theorem realAccumulator_alwaysOutputs : AlwaysOutputs realAccumulator :=
  ofTotal_alwaysOutputs _ _ _

noncomputable def realAccumulatorDirect : DiscreteSystem ℝ ℝ ℝ := realAccumulator

/-- Elaborated: `(sum, lastInput)` projecting to the sum. -/
noncomputable def realAccumulatorElab : DiscreteSystem (ℝ × ℝ) ℝ ℝ :=
  DiscreteSystem.ofTotal
    (fun (s, _) u => (s + u, u))
    (fun (s, _) => s)
    ⟨((0 : ℝ), (0 : ℝ))⟩

noncomputable def realAccumulatorElab_witness :
    HomomorphicImageWitness realAccumulator realAccumulatorElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun s => ⟨(s, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨s, _⟩ oi => by
    cases oi with
    | none => simp [realAccumulatorElab, realAccumulator, DiscreteSystem.ofTotal]
    | some u => simp [realAccumulatorElab, realAccumulator, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨s, _⟩ => by
    simp [realAccumulatorElab, realAccumulator, DiscreteSystem.ofTotal, Option.map_some]

theorem realAccumulatorElab_hom :
    IsHomomorphicImage realAccumulator realAccumulatorElab :=
  ⟨realAccumulatorElab_witness⟩

theorem realAccumulatorElab_iff_hom :
    SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorElab ↔
      IsHomomorphicImage realAccumulator realAccumulatorElab :=
  partialDynamicsHom_iff_hom

theorem realAccumulatorElab_satisfies :
    SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorElab :=
  partialDynamicsHom_of_hom realAccumulatorElab_hom

/-- Threshold alarm buildable: state is sum; output is `(sum, alarm)` with alarm on `|s|≥θ`.
    Projects to the accumulator via `HO = Prod.fst` onto `ℝ` readout of the spec. -/
noncomputable def realThresholdElab (θ : ℝ) : DiscreteSystem ℝ ℝ (ℝ × Bit) :=
  DiscreteSystem.ofTotal
    (fun s u => s + u)
    (fun s => (s, decide (θ ≤ |s|)))
    ⟨(0 : ℝ)⟩

noncomputable def realThresholdElab_witness (θ : ℝ) :
    HomomorphicImageWitness realAccumulator (realThresholdElab θ) where
  HS := id
  HI := id
  HO := Prod.fst
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := fun s => ⟨(s, false), rfl⟩
  preserves_transition := fun s oi => by
    cases oi with
    | none => simp [realThresholdElab, realAccumulator, DiscreteSystem.ofTotal]
    | some u => simp [realThresholdElab, realAccumulator, DiscreteSystem.ofTotal]
  preserves_readout := fun s => by
    simp [realThresholdElab, realAccumulator, DiscreteSystem.ofTotal, Option.map_some]

theorem realThresholdElab_hom (θ : ℝ) :
    IsHomomorphicImage realAccumulator (realThresholdElab θ) :=
  ⟨realThresholdElab_witness θ⟩

theorem realThresholdElab_iff_hom (θ : ℝ) :
    SystemSatisfiesPartialDynamicsHom realAccumulator (realThresholdElab θ) ↔
      IsHomomorphicImage realAccumulator (realThresholdElab θ) :=
  partialDynamicsHom_iff_hom

theorem realThresholdElab_satisfies (θ : ℝ) :
    SystemSatisfiesPartialDynamicsHom realAccumulator (realThresholdElab θ) :=
  partialDynamicsHom_of_hom (realThresholdElab_hom θ)

/-- Complex real buildable: sum, last input, tick count, and a running energy proxy.
    Projects to the sum. -/
noncomputable def realAccumulatorRich : DiscreteSystem (ℝ × ℝ × Nat × ℝ) ℝ ℝ :=
  DiscreteSystem.ofTotal
    (fun (s, _, ticks, energy) u => (s + u, u, ticks + 1, energy + u * u))
    (fun (s, _, _, _) => s)
    ⟨((0 : ℝ), (0 : ℝ), (0 : Nat), (0 : ℝ))⟩

noncomputable def realAccumulatorRich_witness :
    HomomorphicImageWitness realAccumulator realAccumulatorRich where
  HS := fun ⟨s, _, _, _⟩ => s
  HI := id
  HO := id
  HS_surjective := fun s => ⟨(s, 0, 0, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨s, last, ticks, energy⟩ oi => by
    cases oi with
    | none => simp [realAccumulatorRich, realAccumulator, DiscreteSystem.ofTotal]
    | some u => simp [realAccumulatorRich, realAccumulator, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨s, _, _, _⟩ => by
    simp [realAccumulatorRich, realAccumulator, DiscreteSystem.ofTotal, Option.map_some]

theorem realAccumulatorRich_hom :
    IsHomomorphicImage realAccumulator realAccumulatorRich :=
  ⟨realAccumulatorRich_witness⟩

theorem realAccumulatorRich_satisfies :
    SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorRich :=
  partialDynamicsHom_of_hom realAccumulatorRich_hom

theorem realAccumulatorRich_iff_hom :
    SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorRich ↔
      IsHomomorphicImage realAccumulator realAccumulatorRich :=
  partialDynamicsHom_iff_hom

/-- Playbook: discrete and real elaborations satisfy Φ_dyn iff implementability. -/
theorem caseStudy_playbook :
    (SystemSatisfiesPartialDynamicsHom onesCounter onesCounterDirect ↔
      IsHomomorphicImage onesCounter onesCounterDirect) ∧
    (SystemSatisfiesPartialDynamicsHom onesCounter onesCounterBoth ↔
      IsHomomorphicImage onesCounter onesCounterBoth) ∧
    (SystemSatisfiesPartialDynamicsHom onesCounter onesCounterRich ↔
      IsHomomorphicImage onesCounter onesCounterRich) ∧
    (SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Direct ↔
      IsHomomorphicImage pattern01110 pattern01110Direct) ∧
    (SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shadow ↔
      IsHomomorphicImage pattern01110 pattern01110Shadow) ∧
    (SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Rich ↔
      IsHomomorphicImage pattern01110 pattern01110Rich) ∧
    (SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorElab ↔
      IsHomomorphicImage realAccumulator realAccumulatorElab) ∧
    (SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorRich ↔
      IsHomomorphicImage realAccumulator realAccumulatorRich) :=
  ⟨onesCounter_reflexive_iff_hom, onesCounterBoth_iff_hom, onesCounterRich_iff_hom,
    pattern01110_direct_iff_hom, pattern01110Shadow_iff_hom, pattern01110Rich_iff_hom,
    realAccumulatorElab_iff_hom, realAccumulatorRich_iff_hom⟩

end WymoreExercises
