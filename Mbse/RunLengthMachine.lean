import Mbse.FragmentInvariance
import Mbse.IORTemporalFragment
import Mbse.Isomorphism
import Mbse.PartialDynamicsHomFragment
import Mbse.Wymore
import Mbse.WymoreRequirements
import Mbse.WymoreTechnology
import Mathlib.Tactic.FinCases

/-!
# Streaming run-length encoding on a four-component machine

The input is every `f : Time → Bool`. Nothing in the requirement assumes a last symbol.
One symbol is taken on each sense tick (even time); the following act tick displays the run
so far. The count is `Nat`, so there is no maximum run length.

Components, in order: tape, head, state register, instruction table. The external ports are
the tape's input (the bit stream) and the register's output (the run pair). Internal wires
are tape output to table input, table output to register input, and a head self-loop that
closes the otherwise unused head port. The head is the sense/act clock. The tape and register
are Moore pipeline stages, so the boundary requirement includes their two-tick latency.

The instruction table is not a universal machine, and this is not a claim that a program
halts with a compressed tape. The requirement is the run so far, not an eventual encoding.
-/

namespace RunLengthMachine

open Homomorphism PartialDynamicsHomFragment WymoreRequirements WymoreTechnology
open FragmentInvariance Classical Mbse.Wymore

abbrev Pair := Bool × Nat

/-- `phase = false` is sense; `phase = true` is act. -/
structure RleState where
  bit : Bool
  count : Nat
  phase : Bool
  pending : Bool
deriving DecidableEq, Repr

def rleInit : RleState := ⟨false, 0, false, false⟩

/-- Sense samples `b` and updates the run; act returns to sense and holds the pair. -/
def rleStep (s : RleState) (b : Bool) : RleState :=
  if s.phase then
    { s with phase := false }
  else
    ⟨b, if s.count ≠ 0 ∧ b = s.bit then s.count + 1 else 1, true, b⟩

def flipSt (s : RleState) : RleState := { s with phase := !s.phase }

lemma flipSt_left (s : RleState) : flipSt (flipSt s) = s := by
  cases s with
  | mk bit count phase pending =>
    simp [flipSt, Bool.not_not]

lemma flipSt_injective : Function.Injective flipSt :=
  fun a b h => by
    have := congrArg flipSt h
    simpa [flipSt_left] using this

lemma flipSt_surjective : Function.Surjective flipSt :=
  fun s => ⟨flipSt s, flipSt_left s⟩

lemma rleStep_of_sense {s : RleState} {b : Bool} (h : s.phase = false) :
    rleStep s b = ⟨b, if s.count ≠ 0 ∧ b = s.bit then s.count + 1 else 1, true, b⟩ := by
  simp [rleStep, h]

lemma rleStep_of_act {s : RleState} {b : Bool} (h : s.phase = true) :
    rleStep s b = { s with phase := false } := by
  simp [rleStep, h]

lemma sense_bit {s : RleState} {b : Bool} (h : s.phase = false) :
    (rleStep s b).bit = b := by
  simp [rleStep_of_sense h]

lemma sense_count {s : RleState} {b : Bool} (h : s.phase = false) :
    (rleStep s b).count = (if s.count ≠ 0 ∧ b = s.bit then s.count + 1 else 1) := by
  simp [rleStep_of_sense h]

lemma sense_phase {s : RleState} {b : Bool} (h : s.phase = false) :
    (rleStep s b).phase = true := by
  simp [rleStep_of_sense h]

/-! ## Components: one `DiscreteSystem` type, separated by dynamics -/

def cellNext (k : Fin 4) (s : RleState) (f : Unit → Pair) : RleState :=
  match k.1 with
  | 0 => { rleInit with bit := (f ()).1 }
  | 1 => { s with phase := !s.phase }
  | 2 => { rleInit with bit := (f ()).1, count := (f ()).2 }
  | _ => rleStep s (f ()).1

def cellRead (k : Fin 4) (s : RleState) : Unit → Pair :=
  match k.1 with
  | 0 => fun _ => (s.bit, 0)
  | 1 => fun _ => (s.phase, 0)
  | _ => fun _ => (s.bit, s.count)

def rleCell (k : Fin 4) : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) :=
  DiscreteSystem.ofTotal (fun s f => cellNext k s f) (fun s => cellRead k s) ⟨rleInit⟩

def tape : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) := rleCell 0
def head : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) := rleCell 1
def stateReg : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) := rleCell 2
def instrTable : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) := rleCell 3

/-- A signature that separates the four cells. -/
def cellSig (k : Fin 4) : Bool × Nat × Bool × Bool :=
  let s := (rleCell k).NZ rleInit (some (fun _ => (true, 3)))
  (s.phase, s.count, s.bit, s.pending)

lemma cellSig_val (k : Fin 4) :
    cellSig k = (match k with
      | 0 => (false, 0, true, false)
      | 1 => (true, 0, false, false)
      | 2 => (false, 3, true, false)
      | 3 => (true, 1, true, true)) := by
  fin_cases k <;> simp [cellSig, rleCell, DiscreteSystem.ofTotal, cellNext, rleStep, rleInit]

theorem rleCell_distinct (i j : Fin 4) (hne : i ≠ j) : ¬ HEq (rleCell i) (rleCell j) := by
  intro h
  have he : cellSig i = cellSig j := by
    have hsys : rleCell i = rleCell j := eq_of_heq h
    simp [cellSig, hsys]
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hne
    | simp [cellSig_val, Prod.mk.injEq] at he

theorem rleCell_alwaysOutputs (k : Fin 4) : AlwaysOutputs (rleCell k) :=
  fun s => ⟨cellRead k s, by simp [rleCell, DiscreteSystem.ofTotal]⟩

/-! ## Sense then act -/

theorem head_phase_flips (s : RleState) (f : Unit → Pair) :
    (head.NZ s (some f)).phase = !s.phase := by
  simp [head, rleCell, DiscreteSystem.ofTotal, cellNext]

theorem head_sense_then_act (s : RleState) (f g : Unit → Pair) :
    head.NZ (head.NZ s (some f)) (some g) = s := by
  cases s with
  | mk bit count phase pending =>
    simp [head, rleCell, DiscreteSystem.ofTotal, cellNext, Bool.not_not]

/-- A head that never changes phase. It is not a realisation of `head`. -/
def stuckHead : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) :=
  DiscreteSystem.ofTotal (fun s _ => s) (fun s => fun _ => (s.phase, 0)) ⟨rleInit⟩

theorem no_hom_stuckHead : ¬ IsHomomorphicImage head stuckHead := by
  intro ⟨w⟩
  have h := w.preserves_transition rleInit (some (fun _ => (false, 0)))
  have hp := congrArg RleState.phase h
  simp [head, stuckHead, rleCell, DiscreteSystem.ofTotal, cellNext, rleInit] at hp

/-! ## Coupling: two internal wires, external load and run-pair output -/

def rleVSCR : PortSystemVector 4 where
  SZ := fun _ => RleState
  Port := fun _ => Unit
  PortVal := fun _ _ => Pair
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Pair
  Z := rleCell
  distinct := rleCell_distinct

private abbrev RleEdge :=
  (Σ i : Fin 4, rleVSCR.OutPort i) × (Σ i : Fin 4, rleVSCR.Port i)

/-- Tape output feeds the instruction table. -/
def tapeToTable : RleEdge := (⟨0, ()⟩, ⟨3, ()⟩)

/-- Table output feeds the state register. -/
def tableToReg : RleEdge := (⟨3, ()⟩, ⟨2, ()⟩)

/-- The head closes its own port; it remains the internal sense/act clock. -/
def headLoop : RleEdge := (⟨1, ()⟩, ⟨1, ()⟩)

def rleCSCR : Set RleEdge := {tapeToTable, tableToReg, headLoop}

lemma rle_oneToOne : IsOneToOneRelation rleCSCR := by
  constructor
  · intro x y1 y2 h1 h2
    simp only [rleCSCR, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      simp_all [tapeToTable, tableToReg, headLoop]
  · intro x1 x2 y h1 h2
    simp only [rleCSCR, Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      simp_all [tapeToTable, tableToReg, headLoop]

lemma rle_properDomain : IsProperDomain rleCSCR := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy⟩ := h (⟨2, ()⟩ : Σ i, rleVSCR.OutPort i)
  simp only [rleCSCR, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy
  · simp [tapeToTable] at hy
  · simp [tableToReg] at hy
  · simp [headLoop] at hy

lemma rle_properRange : IsProperRange rleCSCR := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  obtain ⟨x, hx⟩ := h (⟨0, ()⟩ : Σ i, rleVSCR.Port i)
  simp only [rleCSCR, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · simp [tapeToTable] at hx
  · simp [tableToReg] at hx
  · simp [headLoop] at hx

lemma rle_compat : PortCompatibility rleVSCR rleCSCR := by
  intro _ _ hop
  simp only [rleCSCR, Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop <;> cases hop <;> rfl

lemma rle_connectivity : IsSystemConnectivity rleVSCR rleCSCR :=
  ⟨rle_oneToOne, rle_properDomain, rle_properRange, rle_compat⟩

def rleSCR : SystemCouplingRecipe 4 where
  VSCR := rleVSCR
  CSCR := rleCSCR
  connectivity := rle_connectivity

/-- The tape's input is unconnected: it is the load port of the algorithm. -/
theorem tape_load_unconnected :
    (⟨0, ()⟩ : Σ i, rleSCR.VSCR.Port i) ∉ CISCR rleSCR := by
  rw [mem_ciscr_iff]
  rintro ⟨op, hop⟩
  simp only [rleSCR, rleCSCR] at hop
  rcases hop with hop | hop | hop
  · simp [tapeToTable] at hop
  · simp [tableToReg] at hop
  · simp [headLoop] at hop

/-- The register's output is unconnected: it is the run-pair output. -/
theorem reg_output_unconnected :
    (⟨2, ()⟩ : Σ i, rleSCR.VSCR.OutPort i) ∉ COSCR rleSCR := by
  rintro ⟨ip, hip⟩
  simp only [rleSCR, rleCSCR] at hip
  rcases hip with hip | hip | hip
  · simp [tapeToTable] at hip
  · simp [tableToReg] at hip
  · simp [headLoop] at hip

def rleTechnology : Technology :=
  ⟨{ AnyDiscreteSystem.of tape,
      AnyDiscreteSystem.of head,
      AnyDiscreteSystem.of stateReg,
      AnyDiscreteSystem.of instrTable },
    ⟨AnyDiscreteSystem.of tape, by simp⟩⟩

theorem rle_vscr_subset : VSCRSubsetTechnology rleSCR.VSCR rleTechnology := by
  intro i
  refine memTechnology_of _ _ ?_
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [Set.mem_singleton_iff]
    rfl

theorem rle_resultant_is_buildable :
    IsBuildableWith rleTechnology rleSCR (fun k => rleCell_alwaysOutputs k)
      (rsy rleSCR (fun k => rleCell_alwaysOutputs k)) :=
  ⟨rle_vscr_subset, IsResultantOf.of_rsy rleSCR (fun k => rleCell_alwaysOutputs k)⟩

abbrev rle_hOut : ∀ k, AlwaysOutputs (rleSCR.VSCR.Z k) :=
  fun k => rleCell_alwaysOutputs k

noncomputable def rleResultant :
    DiscreteSystem (rsy_SZ rleSCR) (rsy_IZ rleSCR) (rsy_OZ rleSCR) :=
  rsy rleSCR rle_hOut

noncomputable def rle_resultant_in_bsr : BuildableSystemDesign rleTechnology where
  n := 4
  SCR := rleSCR
  hOut := fun k => rleCell_alwaysOutputs k
  SZ := rsy_SZ rleSCR
  IZ := rsy_IZ rleSCR
  OZ := rsy_OZ rleSCR
  Z := rleResultant
  buildable := rle_resultant_is_buildable

noncomputable def rleOnlyIn : UnconnInPort rleSCR :=
  ⟨⟨0, ()⟩, by simpa [UISCR] using tape_load_unconnected⟩

noncomputable def rleOnlyOut : UnconnOutPort rleSCR :=
  ⟨⟨2, ()⟩, by simpa [UOSCR] using reg_output_unconnected⟩

/-! ## The abstract pipeline at the boundary -/

/--
The state retained by the boundary reference.  It abstracts the four component
states to exactly the fields that affect future boundary behavior.
-/
@[ext] structure PipelineState where
  tapeBit : Bool
  headPhase : Bool
  reg : Pair
  table : RleState
deriving DecidableEq, Repr

def pipelineInit : PipelineState :=
  ⟨false, true, (false, 0), { rleInit with phase := true }⟩

def pipelineStep (s : PipelineState) (b : Bool) : PipelineState :=
  ⟨b, !s.headPhase, (s.table.bit, s.table.count), rleStep s.table s.tapeBit⟩

def pipelineRef : DiscreteSystem PipelineState Bool Pair :=
  DiscreteSystem.ofTotal pipelineStep PipelineState.reg ⟨pipelineInit⟩

def pipelineHS (x : rsy_SZ rleSCR) : PipelineState :=
  ⟨(x 0).bit, (x 1).phase, ((x 2).bit, (x 2).count), x 3⟩

private theorem componentReadoutAt_of_RZ {SZ IZ OutPort : Type}
    {OutPortVal : OutPort → Type}
    {Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)}
    (hOut : AlwaysOutputs Z) {x : SZ} {f : (op : OutPort) → OutPortVal op}
    (hf : Z.RZ x = some f) (op : OutPort) :
    componentReadoutAt Z hOut op x = f op := by
  have h := Classical.choose_spec (hOut x)
  have hsome : some f = some (Classical.choose (hOut x)) := hf.symm.trans h
  exact congrFun (Option.some.inj hsome).symm op

private theorem heq_of_eqRec {A B : Sort u} (h : A = B) (a : A) :
    HEq (h ▸ a) a := by
  cases h
  rfl

private theorem rsyOutAt_congr_heq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR)
    {op1 op2 : Σ j, SCR.VSCR.OutPort j} (h : op1 = op2) :
    HEq (rsyOutAt SCR hOut x op1) (rsyOutAt SCR hOut x op2) := by
  cases h
  rfl

private theorem rsy_component_input_heq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : SCR.VSCR.Port i)
    (op : Σ j, SCR.VSCR.OutPort j)
    (hop : (op, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR) :
    HEq (rsy_component_input_fun SCR hOut i extIn x port)
      (rsyOutAt SCR hOut x op) := by
  have hC : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ CISCR SCR := ⟨op, hop⟩
  have hopEq : connectedOutput SCR ⟨i, port⟩ hC = op :=
    SCR.connectivity.1.2 _ _ ⟨i, port⟩
      (connectedOutput_spec SCR ⟨i, port⟩ hC) hop
  rw [rsy_component_input_ciscr SCR hOut i extIn x port hC]
  exact HEq.trans (heq_of_eqRec _ _) (rsyOutAt_congr_heq SCR hOut x hopEq)

lemma rle_input_tape (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    rsy_component_input_fun rleSCR rle_hOut 0 ext x () = ext rleOnlyIn := by
  simpa [rleOnlyIn] using
    rsy_component_input_uiscr rleSCR rle_hOut 0 ext x () rleOnlyIn.property

lemma rle_input_table (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    rsy_component_input_fun rleSCR rle_hOut 3 ext x () = ((x 0).bit, 0) := by
  have h := rsy_component_input_heq rleSCR rle_hOut 3 ext x ()
    (⟨0, ()⟩ : Σ j, rleSCR.VSCR.OutPort j) (Or.inl rfl)
  have hout : rsyOutAt rleSCR rle_hOut x ⟨0, ()⟩ = ((x 0).bit, 0) := by
    rw [rsyOutAt_eq_componentReadoutAt]
    exact componentReadoutAt_of_RZ (rle_hOut 0) rfl ()
  exact (eq_of_heq h).trans hout

lemma rle_input_reg (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    rsy_component_input_fun rleSCR rle_hOut 2 ext x () =
      ((x 3).bit, (x 3).count) := by
  have h := rsy_component_input_heq rleSCR rle_hOut 2 ext x ()
    (⟨3, ()⟩ : Σ j, rleSCR.VSCR.OutPort j) (Or.inr (Or.inl rfl))
  have hout : rsyOutAt rleSCR rle_hOut x ⟨3, ()⟩ =
      ((x 3).bit, (x 3).count) := by
    rw [rsyOutAt_eq_componentReadoutAt]
    exact componentReadoutAt_of_RZ (rle_hOut 3) rfl ()
  exact (eq_of_heq h).trans hout

lemma rleResultant_NZ_none (x : rsy_SZ rleSCR) :
    rleResultant.NZ x none = x := by
  funext i
  fin_cases i <;> rfl

lemma rleResultant_NZ_tape (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    (rleResultant.NZ x (some ext) 0).bit = (ext rleOnlyIn).1 := by
  show (rsy_component_input_fun rleSCR rle_hOut 0 ext x ()).1 = _
  rw [rle_input_tape]

lemma rleResultant_NZ_head (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    (rleResultant.NZ x (some ext) 1).phase = !(x 1).phase := by
  rfl

lemma rleResultant_NZ_reg (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    ((rleResultant.NZ x (some ext) 2).bit,
      (rleResultant.NZ x (some ext) 2).count) =
      ((x 3).bit, (x 3).count) := by
  show (rsy_component_input_fun rleSCR rle_hOut 2 ext x (),
      rsy_component_input_fun rleSCR rle_hOut 2 ext x ()).1 = _
  rw [rle_input_reg]

lemma rleResultant_NZ_table (ext : rsy_IZ rleSCR) (x : rsy_SZ rleSCR) :
    rleResultant.NZ x (some ext) 3 = rleStep (x 3) (x 0).bit := by
  show rleStep (x 3)
      (rsy_component_input_fun rleSCR rle_hOut 3 ext x ()).1 = _
  rw [rle_input_table]

lemma rleResultant_out_reg (x : rsy_SZ rleSCR) :
    rsyOutAt rleSCR rle_hOut x ⟨2, ()⟩ = ((x 2).bit, (x 2).count) := by
  rw [rsyOutAt_eq_componentReadoutAt]
  exact componentReadoutAt_of_RZ (rle_hOut 2) rfl ()

noncomputable def pipelineHom : HomomorphicImageWitness pipelineRef rleResultant where
  HS := pipelineHS
  HI := fun ext => (ext rleOnlyIn).1
  HO := fun out => out rleOnlyOut
  HS_surjective := by
    intro s
    refine ⟨fun i =>
      if i = 0 then { rleInit with bit := s.tapeBit }
      else if i = 1 then { rleInit with phase := s.headPhase }
      else if i = 2 then { rleInit with bit := s.reg.1, count := s.reg.2 }
      else s.table, ?_⟩
    cases s
    simp [pipelineHS]
  HI_surjective := fun b => ⟨fun _ => (b, 0), rfl⟩
  HO_surjective := fun p => ⟨fun _ => p, rfl⟩
  preserves_transition := by
    intro x oi
    cases oi with
    | none =>
      rw [rleResultant_NZ_none]
      rfl
    | some ext =>
      apply PipelineState.ext
      · exact rleResultant_NZ_tape ext x
      · exact rleResultant_NZ_head ext x
      · exact rleResultant_NZ_reg ext x
      · exact rleResultant_NZ_table ext x
  preserves_readout := by
    intro x
    have hout := rleResultant_out_reg x
    simp [rleResultant, rsy, rsy_RZ, pipelineRef, DiscreteSystem.ofTotal,
      pipelineHS, Option.map, rleOnlyOut, hout]

theorem rleResultant_realises_pipeline :
    IsHomomorphicImage pipelineRef rleResultant :=
  ⟨pipelineHom⟩

theorem rleResultant_satisfies_pipeline_fragment :
    SystemSatisfiesPartialDynamicsHom pipelineRef rleResultant :=
  partialDynamicsHom_of_hom rleResultant_realises_pipeline

theorem rleResultant_pipeline_fragment_iff_hom :
    SystemSatisfiesPartialDynamicsHom pipelineRef rleResultant ↔
      IsHomomorphicImage pipelineRef rleResultant :=
  partialDynamicsHom_iff_hom

/-! ## The run so far, with no state space -/

/-- Symbol `k` is the input on sense tick `2k`. Act-tick inputs are ignored. -/
def symbolAt (f : ITZ Bool) (k : Nat) : Bool := f (2 * k)

def runLen (f : ITZ Bool) : Nat → Nat
  | 0 => 1
  | k + 1 => if symbolAt f (k + 1) = symbolAt f k then runLen f k + 1 else 1

def runPair (f : ITZ Bool) (k : Nat) : Pair := (symbolAt f k, runLen f k)

/--
Output of the pure boundary formula. Time `0` holds `(false, 0)` before any symbol.
An act tick `2k+1` emits `(symbol k, runLen k)`. The next sense tick holds that pair.
-/
def phiOut (f : ITZ Bool) : Time → Pair
  | 0 => (false, 0)
  | t + 1 => if t % 2 = 0 then runPair f (t / 2) else phiOut f t

def specState (f : ITZ Bool) : Time → RleState
  | 0 => rleInit
  | t + 1 => rleStep (specState f t) (f t)

lemma runLen_pos (f : ITZ Bool) : ∀ k, 0 < runLen f k
  | 0 => by simp [runLen]
  | k + 1 => by
    simp only [runLen]
    split <;> omega

lemma even_succ_mod (t : Nat) (h : t % 2 = 0) : (t + 1) % 2 = 1 := by
  simp [Nat.add_mod, h]

lemma odd_succ_mod (t : Nat) (h : t % 2 = 1) : (t + 1) % 2 = 0 := by
  simp [Nat.add_mod, h]

lemma phase_bit_even (t : Nat) (h : t % 2 = 0) : (t % 2 == 1) = false := by
  simp [h]

lemma phase_bit_odd (t : Nat) (h : t % 2 = 1) : (t % 2 == 1) = true := by
  simp [h]

lemma phase_bit_succ_even (t : Nat) (h : t % 2 = 0) : ((t + 1) % 2 == 1) = true := by
  simp [even_succ_mod t h]

lemma phase_bit_succ_odd (t : Nat) (h : t % 2 = 1) : ((t + 1) % 2 == 1) = false := by
  simp [odd_succ_mod t h]

lemma two_mul_div_of_even (t : Nat) (h : t % 2 = 0) : 2 * (t / 2) = t := by
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)

lemma symbolAt_of_even (f : ITZ Bool) (t : Nat) (h : t % 2 = 0) :
    symbolAt f (t / 2) = f t := by
  simp [symbolAt, two_mul_div_of_even t h]

lemma phiOut_succ_even (f : ITZ Bool) (t : Nat) (h : t % 2 = 0) :
    phiOut f (t + 1) = runPair f (t / 2) := by
  simp [phiOut, h]

lemma phiOut_succ_odd (f : ITZ Bool) (t : Nat) (h : t % 2 = 1) :
    phiOut f (t + 1) = phiOut f t := by
  have hne : ¬ t % 2 = 0 := by omega
  simp [phiOut, hne]

lemma phiOut_odd (f : ITZ Bool) (k : Nat) : phiOut f (2 * k + 1) = runPair f k := by
  have h : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
  simp [phiOut, h, Nat.mul_div_cancel_left k (by decide : 0 < 2)]

lemma phiOut_even_pos (f : ITZ Bool) (t : Nat) (h : t % 2 = 0) (hpos : 0 < t) :
    phiOut f t = runPair f (t / 2 - 1) := by
  let m := t / 2 - 1
  have hdiv : 0 < t / 2 := by
    have ht := two_mul_div_of_even t h
    have hne : t ≠ 0 := Nat.ne_of_gt hpos
    omega
  have hm : t / 2 = m + 1 := by
    dsimp [m]
    omega
  have ht : t = 2 * (m + 1) := by
    rw [← hm]
    exact (two_mul_div_of_even t h).symm
  rw [show phiOut f t = phiOut f (2 * (m + 1)) by rw [ht]]
  have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [show phiOut f (2 * (m + 1)) = phiOut f ((2 * m + 1) + 1) by rw [hstep]]
  rw [phiOut_succ_odd f (2 * m + 1) (by omega)]
  exact phiOut_odd f m

lemma next_count_eq_runLen (f : ITZ Bool) (t : Nat) (ht : t % 2 = 0)
    (hpair : ((specState f t).bit, (specState f t).count) = phiOut f t) :
    (if (specState f t).count ≠ 0 ∧ f t = (specState f t).bit then
      (specState f t).count + 1 else 1) = runLen f (t / 2) := by
  by_cases h0 : t = 0
  · subst h0
    simp [specState, rleInit, runLen]
  · have hpos : 0 < t := Nat.pos_of_ne_zero h0
    have hprev := phiOut_even_pos f t ht hpos
    have hbit : (specState f t).bit = symbolAt f (t / 2 - 1) := by
      have := congrArg Prod.fst hpair
      simpa [hprev, runPair] using this
    have hcount : (specState f t).count = runLen f (t / 2 - 1) := by
      have := congrArg Prod.snd hpair
      simpa [hprev, runPair] using this
    have hcount_ne : (specState f t).count ≠ 0 := by
      rw [hcount]
      exact Nat.ne_of_gt (runLen_pos f (t / 2 - 1))
    have hm : (t / 2 - 1) + 1 = t / 2 := by
      have hdiv : 0 < t / 2 := by
        have ht' := two_mul_div_of_even t ht
        omega
      omega
    have hsym : symbolAt f ((t / 2 - 1) + 1) = f t := by
      simp [symbolAt]
      have : 2 * ((t / 2 - 1) + 1) = t := by
        rw [hm, two_mul_div_of_even t ht]
      simp [this]
    have hiff : f t = (specState f t).bit ↔
        symbolAt f ((t / 2 - 1) + 1) = symbolAt f (t / 2 - 1) := by
      rw [hbit, hsym]
    rw [← hm, runLen, hcount]
    by_cases hb : f t = (specState f t).bit
    · have hc : (specState f t).count ≠ 0 ∧ f t = (specState f t).bit := ⟨hcount_ne, hb⟩
      simp [hc, hiff.mp hb]
    · have hs : symbolAt f ((t / 2 - 1) + 1) ≠ symbolAt f (t / 2 - 1) := by
        intro h
        exact hb (hiff.mpr h)
      simp [hb, hs]

theorem spec_inv (f : ITZ Bool) (t : Nat) :
    ((specState f t).bit, (specState f t).count) = phiOut f t ∧
      (specState f t).phase = (t % 2 == 1) := by
  induction t with
  | zero =>
    simp [specState, rleInit, phiOut]
  | succ t ih =>
    rcases ih with ⟨hpair, hphase⟩
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have hph : (specState f t).phase = false := by
        rw [hphase, phase_bit_even t ht]
      constructor
      · apply Prod.ext
        · rw [show specState f (t + 1) = rleStep (specState f t) (f t) from rfl,
            sense_bit hph, phiOut_succ_even f t ht, runPair, symbolAt_of_even f t ht]
        · rw [show specState f (t + 1) = rleStep (specState f t) (f t) from rfl,
            sense_count hph, phiOut_succ_even f t ht, runPair]
          exact next_count_eq_runLen f t ht hpair
      · rw [show specState f (t + 1) = rleStep (specState f t) (f t) from rfl, sense_phase hph,
          phase_bit_succ_even t ht]
    · have hph : (specState f t).phase = true := by
        rw [hphase, phase_bit_odd t ht]
      constructor
      · rw [show specState f (t + 1) = rleStep (specState f t) (f t) from rfl, rleStep_of_act hph,
          phiOut_succ_odd f t ht]
        simpa using hpair
      · rw [show specState f (t + 1) = rleStep (specState f t) (f t) from rfl, rleStep_of_act hph,
          phase_bit_succ_odd t ht]

/-- Reference: store `(bit, count)` and the sense/act phase. Readout is the pair. -/
def rleRef : DiscreteSystem RleState Bool Pair :=
  DiscreteSystem.ofTotal rleStep (fun s => (s.bit, s.count)) ⟨rleInit⟩

lemma specState_eq (f : ITZ Bool) (t : Time) :
    _root_.generateStateTrajectory rleRef rleInit (liftInput f) t = specState f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [_root_.generateStateTrajectory_succ, ih, specState]
    simp [liftInput, rleRef, DiscreteSystem.ofTotal]

theorem rle_out (f : ITZ Bool) (t : Time) :
    _root_.generateOutputTrajectory rleRef rleInit (liftInput f) t = some (phiOut f t) := by
  rw [_root_.generateOutputTrajectory_val, specState_eq]
  simp [rleRef, DiscreteSystem.ofTotal]
  exact (spec_inv f t).1

/-- `Φ_IO`: the output trajectory is the run so far. No state space. -/
def phiIO (f : ITZ Bool) (g : ITZ Pair) : Prop :=
  ∀ t, g t = phiOut f t

def rleEr (f : ITZ Bool) : Set (ITZ Pair) :=
  {g | phiIO f g}

def rleOtr : Set (ITZ Pair) :=
  {g | ∃ f, phiIO f g}

def rleIOR : InputOutputRequirement Bool Pair where
  olr := .infinite
  itr := Set.univ
  otr := rleOtr
  er := rleEr
  itr_nonempty := ⟨fun _ => false, Set.mem_univ _⟩
  otr_nonempty := ⟨phiOut (fun _ => false), fun _ => false, fun _ => rfl⟩
  er_subset := by
    intro f _ g hg
    exact ⟨f, hg⟩
  er_nonempty := by
    intro f _
    exact ⟨phiOut f, fun _ => rfl⟩
  otr_from_er := by
    intro g hg
    rcases hg with ⟨f, hphi⟩
    exact ⟨f, Set.mem_univ _, hphi⟩

theorem rleRef_satisfies : SatisfiesIOR rleRef rleIOR rleInit Set.univ := by
  refine ⟨⟨0, trivial⟩, by simp [rleIOR, TSR, timeScale], ?_⟩
  intro f _ h hAgr
  have heq : h = f := by
    funext t
    exact hAgr t (by simp [rleIOR, TSR, timeScale])
  refine ⟨phiOut f, fun _ => rfl, ?_⟩
  intro t _
  rw [heq]
  exact rle_out f t

/--
`SatisfiesIOR` for `rleIOR` is exactly `Φ_IO` of the generated output. The equivalence is
for this encoding only, not for an arbitrary temporal formula.
-/
theorem rle_satisfies_iff_phiIO {S : Type} (Z : DiscreteSystem S Bool Pair) (s0 : S) :
    SatisfiesIOR Z rleIOR s0 Set.univ ↔
      ∀ f t, generateOutputTrajectory Z s0 (liftInput f) t = some (phiOut f t) := by
  constructor
  · rintro ⟨_, _, hsat⟩ f t
    have hAgr : agreesOn f f (TSR rleIOR) := fun _ _ => rfl
    obtain ⟨g, hg, hout⟩ := hsat f (Set.mem_univ _) f hAgr
    have hgf : g = phiOut f := by
      funext τ
      exact hg τ
    subst g
    exact hout t (Set.mem_univ _)
  · intro hout
    refine ⟨Set.univ_nonempty, by simp [rleIOR, TSR, timeScale], ?_⟩
    intro f _ h hAgr
    have hhf : h = f := by
      funext t
      exact hAgr t (by simp [rleIOR, TSR, timeScale])
    refine ⟨phiOut f, fun _ => rfl, ?_⟩
    intro t _
    rw [hhf]
    exact hout f t

theorem rleRef_satisfies_phiIO :
    ∀ f t, generateOutputTrajectory rleRef rleInit (liftInput f) t = some (phiOut f t) :=
  rle_out

def rleRef_fsd : FunctionalSystemDesign rleIOR where
  S := RleState
  Z := rleRef
  DSZ := rleInit
  TSZ := Set.univ
  satisfies := rleRef_satisfies

/-! ## The pure boundary law of the coupled pipeline -/

/--
The tape and register each contribute one Moore delay.  Before the pipeline is
full the boundary holds `(false, 0)`; thereafter it is the run-so-far trajectory
shifted by two ticks.
-/
def pipelineOut (f : ITZ Bool) (t : Time) : Pair :=
  if t < 2 then (false, 0) else phiOut f (t - 2)

def pipelineSpec (f : ITZ Bool) : Time → PipelineState
  | 0 => pipelineInit
  | t + 1 => pipelineStep (pipelineSpec f t) (f t)

lemma pipelineSpec_tape_succ (f : ITZ Bool) (t : Time) :
    (pipelineSpec f (t + 1)).tapeBit = f t := rfl

lemma pipelineSpec_table_succ (f : ITZ Bool) (t : Time) :
    (pipelineSpec f (t + 1)).table = specState f t := by
  induction t with
  | zero =>
    simp [pipelineSpec, pipelineInit, pipelineStep, rleStep, rleInit, specState]
  | succ t ih =>
    change rleStep (pipelineSpec f (t + 1)).table
      (pipelineSpec f (t + 1)).tapeBit = rleStep (specState f t) (f t)
    rw [ih, pipelineSpec_tape_succ]

lemma pipelineSpec_reg_two_succ (f : ITZ Bool) (t : Time) :
    (pipelineSpec f (t + 2)).reg = phiOut f t := by
  change ((pipelineSpec f (t + 1)).table.bit,
    (pipelineSpec f (t + 1)).table.count) = phiOut f t
  rw [pipelineSpec_table_succ]
  exact (spec_inv f t).1

lemma pipelineSpec_eq (f : ITZ Bool) (t : Time) :
    generateStateTrajectory pipelineRef pipelineInit (liftInput f) t =
      pipelineSpec f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [_root_.generateStateTrajectory_succ, ih]
    rfl

theorem pipelineRef_out (f : ITZ Bool) (t : Time) :
    generateOutputTrajectory pipelineRef pipelineInit (liftInput f) t =
      some (pipelineOut f t) := by
  rw [generateOutputTrajectory_val, pipelineSpec_eq]
  simp [pipelineRef, DiscreteSystem.ofTotal]
  cases t with
  | zero => simp [pipelineOut, pipelineSpec, pipelineInit]
  | succ t =>
    cases t with
    | zero => simp [pipelineOut, pipelineSpec, pipelineInit, pipelineStep, rleInit]
    | succ t =>
      simp only [Nat.succ_eq_add_one]
      have hreg := pipelineSpec_reg_two_succ f t
      simpa [pipelineOut] using hreg

def pipelineIOR : InputOutputRequirement Bool Pair :=
  IORTemporalFragment.functionalIOR pipelineOut

theorem pipeline_satisfies_iff {S : Type} (Z : DiscreteSystem S Bool Pair) (s0 : S) :
    SatisfiesIOR Z pipelineIOR s0 Set.univ ↔
      ∀ f t, generateOutputTrajectory Z s0 (liftInput f) t =
        some (pipelineOut f t) := by
  simpa [pipelineIOR] using
    IORTemporalFragment.satisfies_functionalIOR_iff
      (IR := Bool) (OR := Pair) Z pipelineOut s0

theorem pipelineRef_satisfies :
    SatisfiesIOR pipelineRef pipelineIOR pipelineInit Set.univ :=
  (pipeline_satisfies_iff pipelineRef pipelineInit).mpr pipelineRef_out

def pipelineRef_fsd : FunctionalSystemDesign pipelineIOR where
  S := PipelineState
  Z := pipelineRef
  DSZ := pipelineInit
  TSZ := Set.univ
  satisfies := pipelineRef_satisfies

def rleInitialState : rsy_SZ rleSCR
  | 0 => rleInit
  | 1 => { rleInit with phase := true }
  | 2 => rleInit
  | 3 => { rleInit with phase := true }

lemma pipelineHS_initial : pipelineHS rleInitialState = pipelineInit := rfl

def rleBoundaryInput (f : ITZ Bool) : ITZ (rsy_IZ rleSCR) :=
  fun t _ => (f t, 0)

theorem rleResultant_boundary_output (f : ITZ Bool) (t : Time) :
    (generateOutputTrajectory rleResultant rleInitialState
      (liftInput (rleBoundaryInput f)) t).map pipelineHom.HO =
        some (pipelineOut f t) := by
  rw [homomorphicImage_preserves_output_trajectory pipelineHom]
  simp [pipelineHom, rleBoundaryInput, pipelineHS_initial]
  exact pipelineRef_out f t

/-! ## Trace `0,0,1` and a finite cap -/

/-- Symbols at times `0, 2, 4` are `0, 0, 1`. Other ticks are unused by the run. -/
def trace001 : ITZ Bool := fun t => t == 4

theorem trace_001 :
    phiOut trace001 1 = (false, 1) ∧
    phiOut trace001 3 = (false, 2) ∧
    phiOut trace001 5 = (true, 1) := by
  decide

theorem pipeline_trace_001 :
    pipelineOut trace001 3 = (false, 1) ∧
    pipelineOut trace001 5 = (false, 2) ∧
    pipelineOut trace001 7 = (true, 1) := by
  decide

/-- Count capped at `n`. Agrees with the infinite step whenever the current count is below `n`. -/
def rleStepCap (n : Nat) (s : RleState) (b : Bool) : RleState :=
  let s' := rleStep s b
  { s' with count := min s'.count n }

lemma rleStep_count_le (s : RleState) (b : Bool) {n : Nat} (h : s.count < n) :
    (rleStep s b).count ≤ n := by
  unfold rleStep
  by_cases hp : s.phase
  · simp [hp]
    omega
  · simp [hp]
    by_cases hc : s.count ≠ 0 ∧ b = s.bit
    · simp [hc]
      omega
    · simp [hc]
      omega

theorem rleStep_cap_eq {n : Nat} {s : RleState} {b : Bool} (h : s.count < n) :
    rleStepCap n s b = rleStep s b := by
  have hle := rleStep_count_le s b h
  simp [rleStepCap, Nat.min_eq_left hle]

/-- The runs of `0,0,1` stay below any cap of `4`, so that truncation matches the infinite step. -/
theorem trace_001_runs_below_four :
    runLen trace001 0 < 4 ∧ runLen trace001 1 < 4 ∧ runLen trace001 2 < 4 := by
  decide

/-! ## The table realises the reference; the fragment is that fact -/

def tableHom : HomomorphicImageWitness rleRef instrTable where
  HS := id
  HI := fun f => (f ()).1
  HO := fun g => g ()
  HS_surjective := Function.surjective_id
  HI_surjective := fun b => ⟨fun _ => (b, 0), rfl⟩
  HO_surjective := fun p => ⟨fun _ => p, rfl⟩
  preserves_transition := by
    intro s oi
    cases oi with
    | none => simp [instrTable, rleCell, rleRef, DiscreteSystem.ofTotal]
    | some f => simp [instrTable, rleCell, rleRef, DiscreteSystem.ofTotal, cellNext]
  preserves_readout := by
    intro s
    simp [instrTable, rleCell, rleRef, DiscreteSystem.ofTotal, cellRead]

theorem table_realises : IsHomomorphicImage rleRef instrTable :=
  ⟨tableHom⟩

theorem table_satisfies_fragment :
    SystemSatisfiesPartialDynamicsHom rleRef instrTable :=
  partialDynamicsHom_of_hom table_realises

theorem table_fragment_iff_hom :
    SystemSatisfiesPartialDynamicsHom rleRef instrTable ↔
      IsHomomorphicImage rleRef instrTable :=
  partialDynamicsHom_iff_hom

/--
Port maps of `tableHom` are projections, not identities, so Theorem 6.58 does not apply.
The output trajectory still transports along those maps.
-/
theorem table_output_transports (s0 : RleState) (f : ITZW (Unit → Pair)) (t : Time) :
    (generateOutputTrajectory instrTable s0 f t).map tableHom.HO =
      generateOutputTrajectory rleRef (tableHom.HS s0) (fun τ => (f τ).map tableHom.HI) t :=
  homomorphicImage_preserves_output_trajectory tableHom s0 f t

/-- Component conformance lifts along any further elaboration of the table. -/
theorem table_conformance_lifts {S I O : Type} {Z' : DiscreteSystem S I O}
    (h : IsHomomorphicImage instrTable Z') :
    SystemSatisfiesPartialDynamicsHom rleRef Z' :=
  satisfies_of_impl_hom table_satisfies_fragment h

/-! ## One re-encoding of the table: the opposite phase convention -/

/-- Same step, storing the complementary phase. -/
def tableFlip : DiscreteSystem RleState (Unit → Pair) (Unit → Pair) :=
  DiscreteSystem.ofTotal
    (fun s f => flipSt (rleStep (flipSt s) (f ()).1))
    (fun s => fun _ => (s.bit, s.count))
    ⟨rleInit⟩

def tableFlipIso : IsomorphismWitness instrTable tableFlip where
  HS := flipSt
  HI := id
  HO := id
  HS_surjective := flipSt_surjective
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro s oi
    cases oi with
    | none => simp [instrTable, tableFlip, rleCell, DiscreteSystem.ofTotal, flipSt]
    | some f =>
      simp [instrTable, tableFlip, rleCell, DiscreteSystem.ofTotal, cellNext, flipSt]
  preserves_readout := by
    intro s
    simp [instrTable, tableFlip, rleCell, DiscreteSystem.ofTotal, cellRead, Option.map, flipSt]
  HS_injective := flipSt_injective
  HI_injective := Function.injective_id
  HO_injective := Function.injective_id

/-- The run-length fragment does not see this re-encoding of the table. -/
theorem table_fragment_invariant :
    SystemSatisfiesPartialDynamicsHom rleRef instrTable ↔
      SystemSatisfiesPartialDynamicsHom rleRef tableFlip :=
  satisfies_iff_of_impl_iso ⟨tableFlipIso⟩

/-! ## The table, built in the same technology -/

def tableVSCR : PortSystemVector 1 where
  SZ := fun _ => RleState
  Port := fun _ => Unit
  PortVal := fun _ _ => Pair
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Pair
  Z := fun _ => instrTable
  distinct := by
    intro i j hne
    exact absurd (Subsingleton.elim i j) hne

def tableSCR : SystemCouplingRecipe 1 where
  VSCR := tableVSCR
  CSCR := ∅
  connectivity := empty_scr_connectivity tableVSCR ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩

lemma tableSCR_conjunctive : IsConjunctive tableSCR := rfl

lemma table_hOut : ∀ k, AlwaysOutputs (tableSCR.VSCR.Z k) :=
  fun _ => rleCell_alwaysOutputs 3

theorem table_vscr_subset : VSCRSubsetTechnology tableSCR.VSCR rleTechnology := by
  intro i
  refine memTechnology_of _ _ ?_
  fin_cases i
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [Set.mem_singleton_iff]
  rfl

noncomputable def tableOnlyIn : UnconnInPort tableSCR :=
  ⟨⟨0, ()⟩, mem_uiscr_conjunctive tableSCR tableSCR_conjunctive _⟩

noncomputable def tableOnlyOut : UnconnOutPort tableSCR :=
  ⟨⟨0, ()⟩, mem_uoscr_conjunctive tableSCR tableSCR_conjunctive _⟩

noncomputable def tableResultant :
    DiscreteSystem (rsy_SZ tableSCR) (rsy_IZ tableSCR) (rsy_OZ tableSCR) :=
  rsy tableSCR table_hOut

lemma table_readout_eq (s : RleState) :
    instrTable.RZ s = some (fun _ => (s.bit, s.count)) := by
  simp [instrTable, rleCell, DiscreteSystem.ofTotal, cellRead]

lemma table_choose_readout (s : RleState) :
    Classical.choose (table_hOut 0 s) = fun _ => (s.bit, s.count) :=
  Trajectory.choose_alwaysOutputs instrTable (table_hOut 0) s (table_readout_eq s)

noncomputable def tableResultantHom : HomomorphicImageWitness rleRef tableResultant where
  HS := fun x => x 0
  HI := fun ext => (ext tableOnlyIn).1
  HO := fun out => out tableOnlyOut
  HS_surjective := fun s => ⟨fun _ => s, rfl⟩
  HI_surjective := fun b => ⟨fun _ => (b, 0), rfl⟩
  HO_surjective := fun p => ⟨fun _ => p, rfl⟩
  preserves_transition := by
    intro x oi
    cases oi with
    | none =>
      simp [tableResultant, rsy, rsy_NZ, tableSCR, tableVSCR, instrTable, rleCell, rleRef,
        DiscreteSystem.ofTotal]
    | some ext =>
      simp [tableResultant, rsy, rsy_NZ, tableSCR, tableVSCR, instrTable, rleCell, rleRef,
        DiscreteSystem.ofTotal, cellNext]
      apply congrArg (fun p : Pair => rleStep (x 0) p.1)
      simpa [tableOnlyIn] using
        rsy_component_input_uiscr tableSCR table_hOut 0 ext x () tableOnlyIn.property
  preserves_readout := by
    intro x
    have hread := rsyOutAt_eq_componentReadoutAt tableSCR table_hOut 0 () x
    simp [tableResultant, rsy, rsy_RZ, rleRef, DiscreteSystem.ofTotal, Option.map, hread,
      componentReadoutAt, table_choose_readout, tableOnlyOut]

theorem table_resultant_buildable :
    IsBuildableWith rleTechnology tableSCR table_hOut tableResultant :=
  ⟨table_vscr_subset, IsResultantOf.of_rsy tableSCR table_hOut⟩

theorem table_resultant_satisfies_fragment :
    SystemSatisfiesPartialDynamicsHom rleRef tableResultant :=
  partialDynamicsHom_of_hom ⟨tableResultantHom⟩

end RunLengthMachine
