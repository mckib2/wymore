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
  | 5, true  => 2  -- overlap: `01110`++`1` leaves prefix `01`
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

/-! ## Lifecycle v3: shift-register refactor (no explicit progress component) -/

/-- Filling-then-sliding bit history of length at most 5. -/
structure Shift5State where
  bits : List Bit
  length_le : bits.length ≤ 5
  deriving DecidableEq

/-- All bit-lists of a fixed length (newest-last / chronological order). -/
def bitLists : (n : Nat) → List (List Bit)
  | 0 => [[]]
  | n + 1 => (bitLists n).flatMap fun t => [false :: t, true :: t]

theorem bitLists_length (n : Nat) : ∀ l ∈ bitLists n, l.length = n := by
  induction n with
  | zero => intro l hl; simp [bitLists] at hl ⊢; simp [hl]
  | succ n ih =>
    intro l hl
    simp only [bitLists, List.mem_flatMap] at hl
    obtain ⟨t, ht, hmem⟩ := hl
    have htlen := ih t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h <;> simp [h, htlen]

theorem bitLists_complete (n : Nat) :
    ∀ l : List Bit, l.length = n → l ∈ bitLists n := by
  induction n with
  | zero =>
    intro l hl
    simp [bitLists, List.length_eq_zero_iff.mp hl]
  | succ n ih =>
    intro l hl
    match l with
    | [] => simp at hl
    | b :: t =>
      have ht : t.length = n := by
        simp only [List.length_cons] at hl
        exact Nat.succ.inj hl
      simp only [bitLists, List.mem_flatMap]
      refine ⟨t, ih t ht, ?_⟩
      cases b <;> simp

def Shift5State.empty : Shift5State := ⟨[], by decide⟩

/-- Append `b`; once full (length 5), drop the oldest bit. -/
def Shift5State.shiftIn (s : Shift5State) (b : Bit) : Shift5State :=
  if _h : s.bits.length < 5 then
    ⟨s.bits ++ [b], by
      have := s.length_le
      simp only [List.length_append, List.length_singleton]
      omega⟩
  else
    ⟨s.bits.tail ++ [b], by
      have hlen : s.bits.length = 5 := by
        have := s.length_le
        omega
      simp [List.length_append, List.length_tail, hlen]⟩

/-- Progress = run the reference matcher on the buffered history from state 0. -/
def Shift5State.progress (s : Shift5State) : MatchState :=
  s.bits.foldl pattern01110Next (0 : MatchState)

def Shift5State.out (s : Shift5State) : Bit :=
  decide (s.bits = [false, true, true, true, false])

/-- Flagship v3 buildable: state is only the recent input window. -/
def pattern01110Shift : DiscreteSystem Shift5State Bit Bit :=
  DiscreteSystem.ofTotal Shift5State.shiftIn Shift5State.out ⟨Shift5State.empty⟩

private def slideOk (l : List Bit) (b : Bit) : Bool :=
  decide
    ((l.tail ++ [b]).foldl pattern01110Next (0 : MatchState) =
      pattern01110Next (l.foldl pattern01110Next (0 : MatchState)) b)

private theorem slideOk_all :
    (bitLists 5).all (fun l => [false, true].all (fun b => slideOk l b)) = true := by
  native_decide

private theorem fold_slide (l : List Bit) (b : Bit) (hl : l.length = 5) :
    (l.tail ++ [b]).foldl pattern01110Next (0 : MatchState) =
      pattern01110Next (l.foldl pattern01110Next (0 : MatchState)) b := by
  have hmem := bitLists_complete 5 l hl
  have hall := List.all_eq_true.mp slideOk_all l hmem
  have hb : b ∈ ([false, true] : List Bit) := by cases b <;> simp
  have hbok := List.all_eq_true.mp hall b hb
  simpa [slideOk, decide_eq_true_eq] using hbok

private def acceptOk (l : List Bit) : Bool :=
  decide
    ((l = [false, true, true, true, false]) ↔
      l.foldl pattern01110Next (0 : MatchState) = (5 : MatchState))

private theorem acceptOk_all :
    (List.range 6).all (fun n => (bitLists n).all acceptOk) = true := by
  native_decide

private theorem accept_iff_progress5 (l : List Bit) (hle : l.length ≤ 5) :
    (l = [false, true, true, true, false]) ↔
      l.foldl pattern01110Next (0 : MatchState) = (5 : MatchState) := by
  have hn : l.length ∈ List.range 6 := by
    simp [List.mem_range]; omega
  have halln := List.all_eq_true.mp acceptOk_all l.length hn
  have hmem := bitLists_complete l.length l rfl
  -- wait, bitLists_complete needs length = n, we have length ≤ 5
  have hmem' : l ∈ bitLists l.length := bitLists_complete l.length l rfl
  have hok := List.all_eq_true.mp halln l hmem'
  simpa [acceptOk, decide_eq_true_eq] using hok

private theorem shift5_progress_shiftIn (s : Shift5State) (b : Bit) :
    Shift5State.progress (Shift5State.shiftIn s b) =
      pattern01110Next (Shift5State.progress s) b := by
  simp only [Shift5State.progress, Shift5State.shiftIn]
  by_cases h : s.bits.length < 5
  · simp only [dif_pos h, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · simp only [dif_neg h]
    have hlen : s.bits.length = 5 := by
      have := s.length_le
      omega
    exact fold_slide s.bits b hlen

private theorem shift5_out_eq_patternOut (s : Shift5State) :
    Shift5State.out s = pattern01110Out (Shift5State.progress s) := by
  simp only [Shift5State.out, Shift5State.progress, pattern01110Out]
  have h := accept_iff_progress5 s.bits s.length_le
  cases hdec : decide (s.bits = [false, true, true, true, false]) with
  | false =>
    have hne : s.bits ≠ [false, true, true, true, false] := by
      simpa using hdec
    have hp : s.bits.foldl pattern01110Next (0 : MatchState) ≠ 5 := by
      intro hp; exact hne (h.mpr hp)
    have : ¬ ((s.bits.foldl pattern01110Next (0 : MatchState)).val = 5) := by
      intro hv; exact hp (Fin.eq_of_val_eq hv)
    simp [this]
  | true =>
    have heq : s.bits = [false, true, true, true, false] := by
      simpa using hdec
    have hp : s.bits.foldl pattern01110Next (0 : MatchState) = 5 := h.mp heq
    simp [hp]

def pattern01110Shift_witness :
    HomomorphicImageWitness pattern01110 pattern01110Shift where
  HS := Shift5State.progress
  HI := id
  HO := id
  HS_surjective := by
    intro q
    match q with
    | ⟨0, _⟩ => exact ⟨Shift5State.empty, by simp [Shift5State.progress, Shift5State.empty]⟩
    | ⟨1, _⟩ =>
      refine ⟨⟨[false], by decide⟩, ?_⟩
      simp [Shift5State.progress, pattern01110Next]
    | ⟨2, _⟩ =>
      refine ⟨⟨[false, true], by decide⟩, ?_⟩
      simp [Shift5State.progress, pattern01110Next]
    | ⟨3, _⟩ =>
      refine ⟨⟨[false, true, true], by decide⟩, ?_⟩
      simp [Shift5State.progress, pattern01110Next]
    | ⟨4, _⟩ =>
      refine ⟨⟨[false, true, true, true], by decide⟩, ?_⟩
      simp [Shift5State.progress, pattern01110Next]
    | ⟨5, _⟩ =>
      refine ⟨⟨[false, true, true, true, false], by decide⟩, ?_⟩
      simp [Shift5State.progress, pattern01110Next]
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun s oi => by
    cases oi with
    | none =>
      simp [pattern01110Shift, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
    | some b =>
      simp [pattern01110Shift, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal, shift5_progress_shiftIn]
  preserves_readout := fun s => by
    simp [pattern01110Shift, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
      DiscreteSystem.ofTotal, Option.map_some, shift5_out_eq_patternOut]

theorem pattern01110Shift_hom :
    IsHomomorphicImage pattern01110 pattern01110Shift :=
  ⟨pattern01110Shift_witness⟩

theorem pattern01110Shift_satisfies :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shift :=
  partialDynamicsHom_of_hom pattern01110Shift_hom

theorem pattern01110Shift_iff_hom :
    SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shift ↔
      IsHomomorphicImage pattern01110 pattern01110Shift :=
  partialDynamicsHom_iff_hom

theorem pattern01110Shift_maps_verified :
    IsHomomorphicImage pattern01110 pattern01110Shift :=
  tryConstructHomWitness_is_hom
    Shift5State.progress id id
    (fun s oi => by
      cases oi with
      | none =>
        simp [pattern01110Shift, pattern01110, FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]
      | some b =>
        simp [pattern01110Shift, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
          DiscreteSystem.ofTotal, shift5_progress_shiftIn])
    (fun s => by
      simp [pattern01110Shift, pattern01110, pattern01110FSM, FSMSystem.toDiscreteSystem,
        DiscreteSystem.ofTotal, Option.map_some, shift5_out_eq_patternOut])
    pattern01110Shift_witness.HS_surjective
    Function.surjective_id
    Function.surjective_id

/-! ## Light extension: dual-port pattern select -/
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

/-- Playbook: lifecycle iterations satisfy Φ_dyn iff implementability.
    Pattern v3 is the shift-register refactor (Rich retained in-library). -/
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
    (SystemSatisfiesPartialDynamicsHom pattern01110 pattern01110Shift ↔
      IsHomomorphicImage pattern01110 pattern01110Shift) ∧
    (SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorElab ↔
      IsHomomorphicImage realAccumulator realAccumulatorElab) ∧
    (SystemSatisfiesPartialDynamicsHom realAccumulator realAccumulatorRich ↔
      IsHomomorphicImage realAccumulator realAccumulatorRich) :=
  ⟨onesCounter_reflexive_iff_hom, onesCounterBoth_iff_hom, onesCounterRich_iff_hom,
    pattern01110_direct_iff_hom, pattern01110Shadow_iff_hom, pattern01110Shift_iff_hom,
    realAccumulatorElab_iff_hom, realAccumulatorRich_iff_hom⟩

/-! ## Paper-facing lifecycle aliases (v1 prototype / v2 instrumented / v3 refactor) -/

abbrev onesCounterV1 := onesCounterDirect
abbrev onesCounterV2 := onesCounterBoth
abbrev onesCounterV3 := onesCounterRich

abbrev pattern01110V1 := pattern01110Direct
abbrev pattern01110V2 := pattern01110Shadow
abbrev pattern01110V3 := pattern01110Shift

noncomputable abbrev realAccumulatorV1 := realAccumulatorDirect
noncomputable abbrev realAccumulatorV2 := realAccumulatorElab
noncomputable abbrev realAccumulatorV3 := realAccumulatorRich

end WymoreExercises
