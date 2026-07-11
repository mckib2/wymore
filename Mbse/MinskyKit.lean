import Mbse.PartialDynamicsHomFragment
import Mbse.HomWitnessConstruction
import Mbse.Homomorphism
import Mbse.WymoreCore

/-!
# Nat Minsky kit (paper case-study Parts 1–2)

Shelf primitives for the three-part case study:
* `counterInc` — enable-gated increment (INC)
* `counterDec` — enable-gated saturating decrement (DEC)
* `natAdder` — hold / clear / add (Nat accumulator)
* `zeroTest` — Moore zero-test (JZ)

Part 1: each has a direct (identity) buildable.
Part 2: alternate buildables for the same specs (binary-shift INC, instrumented DEC,
two zero-test encodings).

Main-text prose must not name Lean. Gallery modules (`WymoreExercises`, `ComposedCaseStudy`)
remain available but are not the paper case-study spine.
-/

namespace MinskyKit

open Homomorphism PartialDynamicsHomFragment HomWitnessConstruction

/-! ## Part 1: reference systems and direct buildables -/

/-- Enable-gated increment: on `true` do `n+1`, else hold; readout is the count. -/
def counterInc : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal
    (fun n b => if b then n + 1 else n)
    id
    ⟨0⟩

def counterIncDirect : DiscreteSystem Nat Bool Nat := counterInc

theorem counterInc_satisfies_self :
    SystemSatisfiesPartialDynamicsHom counterInc counterIncDirect :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [counterIncDirect, counterInc, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [counterIncDirect, counterInc, DiscreteSystem.ofTotal]
  }⟩

theorem counterInc_reflexive_iff_hom :
    SystemSatisfiesPartialDynamicsHom counterInc counterIncDirect ↔
      IsHomomorphicImage counterInc counterIncDirect :=
  partialDynamicsHom_iff_hom

/-- Enable-gated saturating decrement: on `true` do `n-1`, else hold. -/
def counterDec : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal
    (fun n b => if b then n - 1 else n)
    id
    ⟨0⟩

def counterDecDirect : DiscreteSystem Nat Bool Nat := counterDec

theorem counterDec_satisfies_self :
    SystemSatisfiesPartialDynamicsHom counterDec counterDecDirect :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [counterDecDirect, counterDec, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [counterDecDirect, counterDec, DiscreteSystem.ofTotal]
  }⟩

theorem counterDec_reflexive_iff_hom :
    SystemSatisfiesPartialDynamicsHom counterDec counterDecDirect ↔
      IsHomomorphicImage counterDec counterDecDirect :=
  partialDynamicsHom_iff_hom

/-- Adder commands: hold, clear to `0`, or add a Nat. -/
inductive AddCmd where
  | hold
  | clear
  | add (u : Nat)
  deriving DecidableEq, Repr

/-- Nat accumulator with hold / clear / add. -/
def natAdder : DiscreteSystem Nat AddCmd Nat :=
  DiscreteSystem.ofTotal
    (fun s cmd =>
      match cmd with
      | .hold => s
      | .clear => 0
      | .add u => s + u)
    id
    ⟨0⟩

def natAdderDirect : DiscreteSystem Nat AddCmd Nat := natAdder

theorem natAdder_satisfies_self :
    SystemSatisfiesPartialDynamicsHom natAdder natAdderDirect :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [natAdderDirect, natAdder, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [natAdderDirect, natAdder, DiscreteSystem.ofTotal]
  }⟩

theorem natAdder_reflexive_iff_hom :
    SystemSatisfiesPartialDynamicsHom natAdder natAdderDirect ↔
      IsHomomorphicImage natAdder natAdderDirect :=
  partialDynamicsHom_iff_hom

/-- Moore zero-test: next state / readout is whether the sampled Nat is `0`. -/
def zeroTest : DiscreteSystem Bool Nat Bool :=
  DiscreteSystem.ofTotal
    (fun _ n => decide (n = 0))
    id
    ⟨true⟩

def zeroTestDirect : DiscreteSystem Bool Nat Bool := zeroTest

theorem zeroTest_satisfies_self :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDirect :=
  partialDynamicsHom_of_hom ⟨{
    HS := id, HI := id, HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := fun s oi => by
      simp [zeroTestDirect, zeroTest, DiscreteSystem.ofTotal]
    preserves_readout := fun s => by
      simp [zeroTestDirect, zeroTest, DiscreteSystem.ofTotal]
  }⟩

theorem zeroTest_reflexive_iff_hom :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDirect ↔
      IsHomomorphicImage zeroTest zeroTestDirect :=
  partialDynamicsHom_iff_hom

/-! ## Part 2: alternate buildables (same specs) -/

/-! ### Binary-shift counter for `counterInc` -/

abbrev Bit := Bool

/-- Little-endian bit list value. -/
def bitsValue : List Bit → Nat
  | [] => 0
  | b :: t => (if b then 1 else 0) + 2 * bitsValue t

/-- Binary increment with carry (little-endian). -/
def bitsInc : List Bit → List Bit
  | [] => [true]
  | false :: t => true :: t
  | true :: t => false :: bitsInc t

theorem bitsValue_bitsInc (bs : List Bit) :
    bitsValue (bitsInc bs) = bitsValue bs + 1 := by
  induction bs with
  | nil => simp [bitsInc, bitsValue]
  | cons b t ih =>
    cases b with
    | false =>
      simp [bitsInc, bitsValue]
      omega
    | true =>
      simp [bitsInc, bitsValue, ih]
      omega

/-- Canonical little-endian bits of a Nat (inverse of `bitsValue`). -/
def bitsOf : Nat → List Bit
  | 0 => []
  | n + 1 =>
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)
    (decide ((n + 1) % 2 = 1)) :: bitsOf ((n + 1) / 2)

theorem bitsValue_bitsOf (n : Nat) : bitsValue (bitsOf n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [bitsOf, bitsValue]
    | succ n =>
      simp only [bitsOf, bitsValue]
      have ih' := ih ((n + 1) / 2) (Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2))
      have hmod : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := Nat.mod_two_eq_zero_or_one (n + 1)
      rcases hmod with h0 | h1
      · simp [h0, ih']
        -- n+1 = 2 * ((n+1)/2) when even
        have := Nat.div_add_mod (n + 1) 2
        omega
      · simp [h1, ih']
        have := Nat.div_add_mod (n + 1) 2
        omega

/-- Flagship alternate INC: state is only a bit list; `h_S = bitsValue`. -/
def counterIncShift : DiscreteSystem (List Bit) Bool Nat :=
  DiscreteSystem.ofTotal
    (fun bs b => if b then bitsInc bs else bs)
    bitsValue
    ⟨[]⟩

def counterIncShift_witness : HomomorphicImageWitness counterInc counterIncShift where
  HS := bitsValue
  HI := id
  HO := id
  HS_surjective := fun n => ⟨bitsOf n, bitsValue_bitsOf n⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun bs oi => by
    cases oi with
    | none => simp [counterIncShift, counterInc, DiscreteSystem.ofTotal]
    | some b =>
      cases b with
      | false => simp [counterIncShift, counterInc, DiscreteSystem.ofTotal]
      | true =>
        simp [counterIncShift, counterInc, DiscreteSystem.ofTotal, bitsValue_bitsInc]
  preserves_readout := fun bs => by
    simp [counterIncShift, counterInc, DiscreteSystem.ofTotal, Option.map_some]

theorem counterIncShift_hom :
    IsHomomorphicImage counterInc counterIncShift :=
  ⟨counterIncShift_witness⟩

theorem counterIncShift_satisfies :
    SystemSatisfiesPartialDynamicsHom counterInc counterIncShift :=
  partialDynamicsHom_of_hom counterIncShift_hom

theorem counterIncShift_iff_hom :
    SystemSatisfiesPartialDynamicsHom counterInc counterIncShift ↔
      IsHomomorphicImage counterInc counterIncShift :=
  partialDynamicsHom_iff_hom

/-! ### Instrumented DEC for `counterDec` -/

/-- Tracks value and total successful-looking decrement pulses; projects to value. -/
def counterDecElab : DiscreteSystem (Nat × Nat) Bool Nat :=
  DiscreteSystem.ofTotal
    (fun (n, k) b =>
      if b then (n - 1, k + 1) else (n, k))
    (fun (n, _) => n)
    ⟨(0, 0)⟩

def counterDecElab_witness : HomomorphicImageWitness counterDec counterDecElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun n => ⟨(n, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨n, k⟩ oi => by
    cases oi with
    | none => simp [counterDecElab, counterDec, DiscreteSystem.ofTotal]
    | some b =>
      cases b <;> simp [counterDecElab, counterDec, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨n, _⟩ => by
    simp [counterDecElab, counterDec, DiscreteSystem.ofTotal, Option.map_some]

theorem counterDecElab_hom :
    IsHomomorphicImage counterDec counterDecElab :=
  ⟨counterDecElab_witness⟩

theorem counterDecElab_satisfies :
    SystemSatisfiesPartialDynamicsHom counterDec counterDecElab :=
  partialDynamicsHom_of_hom counterDecElab_hom

theorem counterDecElab_iff_hom :
    SystemSatisfiesPartialDynamicsHom counterDec counterDecElab ↔
      IsHomomorphicImage counterDec counterDecElab :=
  partialDynamicsHom_iff_hom

/-! ### Alternate zero-test encodings -/

/-- Richer latch: stores `(isZero, lastSample)`; projects to the flag. -/
def zeroTestElab : DiscreteSystem (Bool × Nat) Nat Bool :=
  DiscreteSystem.ofTotal
    (fun _ n => (decide (n = 0), n))
    (fun (z, _) => z)
    ⟨(true, 0)⟩

def zeroTestElab_witness : HomomorphicImageWitness zeroTest zeroTestElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun z => ⟨(z, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨_, _⟩ oi => by
    cases oi with
    | none => simp [zeroTestElab, zeroTest, DiscreteSystem.ofTotal]
    | some n => simp [zeroTestElab, zeroTest, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨z, _⟩ => by
    simp [zeroTestElab, zeroTest, DiscreteSystem.ofTotal, Option.map_some]

theorem zeroTestElab_hom :
    IsHomomorphicImage zeroTest zeroTestElab :=
  ⟨zeroTestElab_witness⟩

theorem zeroTestElab_satisfies :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestElab :=
  partialDynamicsHom_of_hom zeroTestElab_hom

theorem zeroTestElab_iff_hom :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestElab ↔
      IsHomomorphicImage zeroTest zeroTestElab :=
  partialDynamicsHom_iff_hom

/-- Dual encoding: flag stored twice; projects to first copy. -/
def zeroTestDual : DiscreteSystem (Bool × Bool) Nat Bool :=
  DiscreteSystem.ofTotal
    (fun _ n =>
      let z := decide (n = 0)
      (z, z))
    Prod.fst
    ⟨(true, true)⟩

def zeroTestDual_witness : HomomorphicImageWitness zeroTest zeroTestDual where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun z => ⟨(z, z), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨_, _⟩ oi => by
    cases oi with
    | none => simp [zeroTestDual, zeroTest, DiscreteSystem.ofTotal]
    | some n => simp [zeroTestDual, zeroTest, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨z, _⟩ => by
    simp [zeroTestDual, zeroTest, DiscreteSystem.ofTotal, Option.map_some]

theorem zeroTestDual_hom :
    IsHomomorphicImage zeroTest zeroTestDual :=
  ⟨zeroTestDual_witness⟩

theorem zeroTestDual_satisfies :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDual :=
  partialDynamicsHom_of_hom zeroTestDual_hom

theorem zeroTestDual_iff_hom :
    SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDual ↔
      IsHomomorphicImage zeroTest zeroTestDual :=
  partialDynamicsHom_iff_hom

/-! ## Playbook -/

theorem minskyKit_playbook :
    (SystemSatisfiesPartialDynamicsHom counterInc counterIncDirect ↔
      IsHomomorphicImage counterInc counterIncDirect) ∧
    (SystemSatisfiesPartialDynamicsHom counterInc counterIncShift ↔
      IsHomomorphicImage counterInc counterIncShift) ∧
    (SystemSatisfiesPartialDynamicsHom counterDec counterDecDirect ↔
      IsHomomorphicImage counterDec counterDecDirect) ∧
    (SystemSatisfiesPartialDynamicsHom counterDec counterDecElab ↔
      IsHomomorphicImage counterDec counterDecElab) ∧
    (SystemSatisfiesPartialDynamicsHom natAdder natAdderDirect ↔
      IsHomomorphicImage natAdder natAdderDirect) ∧
    (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDirect ↔
      IsHomomorphicImage zeroTest zeroTestDirect) ∧
    (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestElab ↔
      IsHomomorphicImage zeroTest zeroTestElab) ∧
    (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDual ↔
      IsHomomorphicImage zeroTest zeroTestDual) :=
  ⟨counterInc_reflexive_iff_hom, counterIncShift_iff_hom,
    counterDec_reflexive_iff_hom, counterDecElab_iff_hom,
    natAdder_reflexive_iff_hom,
    zeroTest_reflexive_iff_hom, zeroTestElab_iff_hom, zeroTestDual_iff_hom⟩

/-! ## Kit helpers used by Fibonacci composition -/

/-- Clear then add `u` using shelf `natAdder.NZ`. -/
def kitAssign (u : Nat) : Nat :=
  natAdder.NZ (natAdder.NZ 0 (some .clear)) (some (.add u))

theorem kitAssign_eq (u : Nat) : kitAssign u = u := by
  simp [kitAssign, natAdder, DiscreteSystem.ofTotal]

/-- Clear then add `a` then add `b` using shelf `natAdder.NZ`. -/
def kitSum2 (a b : Nat) : Nat :=
  natAdder.NZ (natAdder.NZ (natAdder.NZ 0 (some .clear)) (some (.add a))) (some (.add b))

theorem kitSum2_eq (a b : Nat) : kitSum2 a b = a + b := by
  simp [kitSum2, natAdder, DiscreteSystem.ofTotal]

end MinskyKit
