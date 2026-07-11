import Mbse.MinskyKit
import Mbse.PartialDynamicsHomFragment
import Mbse.HomWitnessConstruction
import Mbse.Homomorphism
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci composition case study (paper Part 3)

Kit: `counterInc`, `counterDec`, `natAdder`, `zeroTest` from `MinskyKit`.

Intent: on receipt of `n`, output `Nat.fib n`.

* `fibSpec` — monolithic reference table (control + registers)
* `fibAwkwardImpl` — kit-assembled product of shelf component states with wired `NZ`/`RZ`
* Shelf wiring lemmas — each coupled update applies a kit `NZ`/`RZ`
* `fibSpec_computes_fib` — functional correctness
* `fibAwkward_iff_hom` — Φ↔hom

Main-text prose must not name Lean.
-/

namespace FibCaseStudy

open Homomorphism PartialDynamicsHomFragment HomWitnessConstruction MinskyKit

/-! ## Control phases and inputs -/

inductive FibPhase where
  | idle | check | summing | moveA | moveB | decr | done
  deriving DecidableEq, Repr

inductive FibCmd where
  | load (n : Nat)
  | step
  deriving DecidableEq, Repr

structure FibSpecState where
  phase : FibPhase
  a : Nat
  b : Nat
  t : Nat
  countdown : Nat
  deriving DecidableEq

def FibSpecState.idle : FibSpecState := ⟨.idle, 0, 0, 0, 0⟩

def fibSpecNext (s : FibSpecState) (cmd : FibCmd) : FibSpecState :=
  match cmd with
  | .load n => ⟨.check, 0, 1, 0, n⟩
  | .step =>
    match s.phase with
    | .idle => s
    | .check =>
      if s.countdown = 0 then ⟨.done, s.a, s.b, s.t, s.countdown⟩
      else ⟨.summing, s.a, s.b, s.t, s.countdown⟩
    | .summing => ⟨.moveA, s.a, s.b, s.a + s.b, s.countdown⟩
    | .moveA => ⟨.moveB, s.b, s.b, s.t, s.countdown⟩
    | .moveB => ⟨.decr, s.a, s.t, s.t, s.countdown⟩
    | .decr => ⟨.check, s.a, s.b, s.t, s.countdown - 1⟩
    | .done => s

def fibSpecOut (s : FibSpecState) : Nat := s.a

def fibSpec : DiscreteSystem FibSpecState FibCmd Nat :=
  DiscreteSystem.ofTotal fibSpecNext fibSpecOut ⟨FibSpecState.idle⟩

/-! ## Kit-assembled buildable: shelf component product -/

structure FibAwkwardState where
  phase : FibPhase
  a : Nat
  b : Nat
  t : Nat
  countdown : Nat
  zeroFlag : Bool
  pulses : Nat

def FibAwkwardState.idle : FibAwkwardState := ⟨.idle, 0, 0, 0, 0, true, 0⟩

def fibAwkwardNext (s : FibAwkwardState) (cmd : FibCmd) : FibAwkwardState :=
  match cmd with
  | .load n =>
    let a' := kitAssign 0
    let b' := kitAssign 1
    let t' := kitAssign 0
    let z' := zeroTest.NZ s.zeroFlag (some n)
    let p' := kitAssign 0
    ⟨.check, a', b', t', n, z', p'⟩
  | .step =>
    match s.phase with
    | .idle => s
    | .check =>
      let z' := zeroTest.NZ s.zeroFlag (some s.countdown)
      let isZero := (zeroTest.RZ z').getD false
      if isZero then
        ⟨.done, s.a, s.b, s.t, s.countdown, z', s.pulses⟩
      else
        ⟨.summing, s.a, s.b, s.t, s.countdown, z', s.pulses⟩
    | .summing =>
      let t' := kitSum2 s.a s.b
      ⟨.moveA, s.a, s.b, t', s.countdown, s.zeroFlag, s.pulses⟩
    | .moveA =>
      let a' := kitAssign s.b
      ⟨.moveB, a', s.b, s.t, s.countdown, s.zeroFlag, s.pulses⟩
    | .moveB =>
      let b' := kitAssign s.t
      ⟨.decr, s.a, b', s.t, s.countdown, s.zeroFlag, s.pulses⟩
    | .decr =>
      let c' := counterDec.NZ s.countdown (some true)
      let p' := counterInc.NZ s.pulses (some true)
      ⟨.check, s.a, s.b, s.t, c', s.zeroFlag, p'⟩
    | .done => s

def fibAwkwardOut (s : FibAwkwardState) : Nat := (natAdder.RZ s.a).getD 0

def fibAwkwardImpl : DiscreteSystem FibAwkwardState FibCmd Nat :=
  DiscreteSystem.ofTotal fibAwkwardNext fibAwkwardOut ⟨FibAwkwardState.idle⟩

def fibHS (s : FibAwkwardState) : FibSpecState :=
  ⟨s.phase, s.a, s.b, s.t, s.countdown⟩

/-! ## Shelf NZ/RZ wiring lemmas -/

theorem fibAwkward_load_uses_shelf (s : FibAwkwardState) (n : Nat) :
    let s' := fibAwkwardNext s (.load n)
    s'.a = kitAssign 0 ∧
    s'.b = kitAssign 1 ∧
    s'.t = kitAssign 0 ∧
    s'.zeroFlag = zeroTest.NZ s.zeroFlag (some n) ∧
    s'.pulses = kitAssign 0 ∧
    s'.countdown = n := by
  simp [fibAwkwardNext]

theorem fibAwkward_check_uses_zeroTest (a b t c : Nat) (z : Bool) (p : Nat) :
    let s : FibAwkwardState := ⟨.check, a, b, t, c, z, p⟩
    let s' := fibAwkwardNext s .step
    s'.zeroFlag = zeroTest.NZ z (some c) ∧
    (zeroTest.RZ (zeroTest.NZ z (some c))).getD false = decide (c = 0) := by
  simp [fibAwkwardNext, zeroTest, DiscreteSystem.ofTotal, Option.getD]
  by_cases hc : c = 0 <;> simp [hc]

theorem fibAwkward_summing_uses_natAdder (a b t c : Nat) (z : Bool) (p : Nat) :
    let s : FibAwkwardState := ⟨.summing, a, b, t, c, z, p⟩
    (fibAwkwardNext s .step).t = kitSum2 a b ∧ kitSum2 a b = a + b := by
  simp [fibAwkwardNext, kitSum2_eq]

theorem fibAwkward_moveA_uses_natAdder (a b t c : Nat) (z : Bool) (p : Nat) :
    let s : FibAwkwardState := ⟨.moveA, a, b, t, c, z, p⟩
    (fibAwkwardNext s .step).a = kitAssign b ∧ kitAssign b = b := by
  simp [fibAwkwardNext, kitAssign_eq]

theorem fibAwkward_moveB_uses_natAdder (a b t c : Nat) (z : Bool) (p : Nat) :
    let s : FibAwkwardState := ⟨.moveB, a, b, t, c, z, p⟩
    (fibAwkwardNext s .step).b = kitAssign t ∧ kitAssign t = t := by
  simp [fibAwkwardNext, kitAssign_eq]

theorem fibAwkward_decr_uses_dec_and_inc (a b t c : Nat) (z : Bool) (p : Nat) :
    let s : FibAwkwardState := ⟨.decr, a, b, t, c, z, p⟩
    let s' := fibAwkwardNext s .step
    s'.countdown = counterDec.NZ c (some true) ∧
    s'.pulses = counterInc.NZ p (some true) ∧
    counterDec.NZ c (some true) = c - 1 ∧
    counterInc.NZ p (some true) = p + 1 := by
  simp [fibAwkwardNext, counterDec, counterInc, DiscreteSystem.ofTotal]

theorem fibAwkward_readout_uses_natAdder (s : FibAwkwardState) :
    fibAwkwardOut s = (natAdder.RZ s.a).getD 0 ∧
    (natAdder.RZ s.a).getD 0 = s.a := by
  simp [fibAwkwardOut, natAdder, DiscreteSystem.ofTotal]

theorem fibAwkward_uses_shelf_components :
    (∀ s n, (fibAwkwardNext s (.load n)).a = kitAssign 0) ∧
    (∀ s n, (fibAwkwardNext s (.load n)).b = kitAssign 1) ∧
    (∀ s n, (fibAwkwardNext s (.load n)).zeroFlag = zeroTest.NZ s.zeroFlag (some n)) ∧
    (∀ a b t c z p,
      (fibAwkwardNext ⟨.check, a, b, t, c, z, p⟩ .step).zeroFlag =
        zeroTest.NZ z (some c)) ∧
    (∀ a b t c z p,
      (fibAwkwardNext ⟨.summing, a, b, t, c, z, p⟩ .step).t = kitSum2 a b) ∧
    (∀ a b t c z p,
      (fibAwkwardNext ⟨.moveA, a, b, t, c, z, p⟩ .step).a = kitAssign b) ∧
    (∀ a b t c z p,
      (fibAwkwardNext ⟨.moveB, a, b, t, c, z, p⟩ .step).b = kitAssign t) ∧
    (∀ a b t c z p,
      (fibAwkwardNext ⟨.decr, a, b, t, c, z, p⟩ .step).countdown =
        counterDec.NZ c (some true) ∧
      (fibAwkwardNext ⟨.decr, a, b, t, c, z, p⟩ .step).pulses =
        counterInc.NZ p (some true)) ∧
    (∀ s, fibAwkwardOut s = (natAdder.RZ s.a).getD 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s n; simp [fibAwkwardNext]
  · intro s n; simp [fibAwkwardNext]
  · intro s n; simp [fibAwkwardNext]
  · intro a b t c z p
    simp [fibAwkwardNext, zeroTest, DiscreteSystem.ofTotal, Option.getD]
    by_cases hc : c = 0 <;> simp [hc]
  · intro a b t c z p; simp [fibAwkwardNext]
  · intro a b t c z p; simp [fibAwkwardNext]
  · intro a b t c z p; simp [fibAwkwardNext]
  · intro a b t c z p; simp [fibAwkwardNext]
  · intro s; rfl

/-! ## Homomorphism -/

theorem fibAwkward_preserves_transition (s : FibAwkwardState) (cmd : FibCmd) :
    fibHS (fibAwkwardNext s cmd) = fibSpecNext (fibHS s) cmd := by
  rcases s with ⟨phase, a, b, t, c, z, p⟩
  cases cmd with
  | load n =>
    simp [fibAwkwardNext, fibSpecNext, fibHS, kitAssign_eq]
  | step =>
    cases phase with
    | idle => simp [fibAwkwardNext, fibSpecNext, fibHS]
    | check =>
      simp [fibAwkwardNext, fibSpecNext, fibHS, zeroTest, DiscreteSystem.ofTotal, Option.getD]
      by_cases hc : c = 0 <;> simp [hc]
    | summing => simp [fibAwkwardNext, fibSpecNext, fibHS, kitSum2_eq]
    | moveA => simp [fibAwkwardNext, fibSpecNext, fibHS, kitAssign_eq]
    | moveB => simp [fibAwkwardNext, fibSpecNext, fibHS, kitAssign_eq]
    | decr => simp [fibAwkwardNext, fibSpecNext, fibHS, counterDec, DiscreteSystem.ofTotal]
    | done => simp [fibAwkwardNext, fibSpecNext, fibHS]

theorem fibAwkward_preserves_readout (s : FibAwkwardState) :
    fibAwkwardOut s = fibSpecOut (fibHS s) := by
  simp [fibAwkwardOut, fibSpecOut, fibHS, natAdder, DiscreteSystem.ofTotal]

def fibAwkward_witness : HomomorphicImageWitness fibSpec fibAwkwardImpl where
  HS := fibHS
  HI := id
  HO := id
  HS_surjective := by
    intro s
    refine ⟨⟨s.phase, s.a, s.b, s.t, s.countdown, decide (s.countdown = 0), 0⟩, ?_⟩
    simp [fibHS]
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun s oi => by
    cases oi with
    | none => simp [fibAwkwardImpl, fibSpec, DiscreteSystem.ofTotal, fibHS]
    | some cmd =>
      simp [fibAwkwardImpl, fibSpec, DiscreteSystem.ofTotal, fibAwkward_preserves_transition]
  preserves_readout := fun s => by
    simp [fibAwkwardImpl, fibSpec, DiscreteSystem.ofTotal, Option.map_some,
      fibAwkward_preserves_readout]

theorem fibAwkward_hom : IsHomomorphicImage fibSpec fibAwkwardImpl := ⟨fibAwkward_witness⟩

theorem fibAwkward_satisfies :
    SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl :=
  partialDynamicsHom_of_hom fibAwkward_hom

theorem fibAwkward_iff_hom :
    SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl ↔
      IsHomomorphicImage fibSpec fibAwkwardImpl :=
  partialDynamicsHom_iff_hom

theorem fib_caseStudy_playbook :
    SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl ↔
      IsHomomorphicImage fibSpec fibAwkwardImpl :=
  fibAwkward_iff_hom

/-! ## Functional correctness -/

theorem fibSpec_after_load (n : Nat) :
    fibSpecNext FibSpecState.idle (.load n) = ⟨.check, 0, 1, 0, n⟩ := rfl

def fibIter (s : FibSpecState) : FibSpecState :=
  fibSpecNext (fibSpecNext (fibSpecNext (fibSpecNext (fibSpecNext s .step) .step) .step) .step) .step

theorem fibIter_from_check (a b t k : Nat) :
    fibIter ⟨.check, a, b, t, k + 1⟩ = ⟨.check, b, a + b, a + b, k⟩ := by
  simp [fibIter, fibSpecNext]

def fibIterN : Nat → FibSpecState → FibSpecState
  | 0, s => s
  | k + 1, s => fibIter (fibIterN k s)

/-- After `j` iterations from the post-load state:
    phase `check`, `a = fib j`, `b = fib (j+1)`, countdown `n - j`. -/
theorem fibIterN_from_load (n j : Nat) (hj : j ≤ n) :
    (fibIterN j ⟨.check, 0, 1, 0, n⟩).phase = .check ∧
    (fibIterN j ⟨.check, 0, 1, 0, n⟩).a = Nat.fib j ∧
    (fibIterN j ⟨.check, 0, 1, 0, n⟩).b = Nat.fib (j + 1) ∧
    (fibIterN j ⟨.check, 0, 1, 0, n⟩).countdown = n - j := by
  induction j with
  | zero =>
    simp [fibIterN, Nat.fib_zero, Nat.fib_one]
  | succ j ih =>
    obtain ⟨hp, ha, hb, hc⟩ := ih (Nat.le_of_succ_le hj)
    simp only [fibIterN]
    cases hgen : fibIterN j ⟨.check, 0, 1, 0, n⟩ with
    | mk ph a b t c =>
      simp only [hgen] at hp ha hb hc ⊢
      cases hp
      subst a; subst b; subst c
      have hcd : n - j = (n - (j + 1)) + 1 := by omega
      rw [hcd, fibIter_from_check]
      exact ⟨rfl, rfl, (Nat.fib_add_two (n := j)).symm, rfl⟩

theorem fibIterN_n (n : Nat) :
    let s := fibIterN n ⟨.check, 0, 1, 0, n⟩
    s.phase = .check ∧ s.countdown = 0 ∧ s.a = Nat.fib n := by
  have ⟨hp, ha, _, hc⟩ := fibIterN_from_load n n (Nat.le_refl n)
  exact ⟨hp, by simpa using hc, ha⟩

def fibRun (n : Nat) : FibSpecState :=
  fibIterN n (fibSpecNext FibSpecState.idle (.load n))

theorem fibSpec_at_check_zero_is_fib (n : Nat) :
    (fibRun n).phase = .check ∧
    (fibRun n).countdown = 0 ∧
    (fibRun n).a = Nat.fib n := by
  simpa [fibRun, fibSpec_after_load] using fibIterN_n n

theorem fibSpec_computes_fib (n : Nat) :
    fibSpecOut (fibSpecNext (fibRun n) .step) = Nat.fib n := by
  have ⟨hp, hc, ha⟩ := fibSpec_at_check_zero_is_fib n
  simp [fibSpecOut, fibSpecNext, hp, hc, ha]

end FibCaseStudy
