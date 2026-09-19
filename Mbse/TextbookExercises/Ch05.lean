import Mbse.WymoreSystemModes
import Mbse.WymoreCouplingStructure

/-!
# Chapter 5 — system-mode exercises

Exercises 5.141, 5.142, 5.146, 5.147, and 5.148.

Two different relations meet here.  `Mbse.Wymore.IsSubsystemOf` is *recipe based*:
it asserts the existence of coupling recipes, an injective component embedding,
and the `CSCR` restriction clause, tying the systems to the recipes only through
`HEq Z (rsy SCR hOut)`.  `WymoreSystemModes.IsSystemMode` is *behavioral*: it
asserts the existence of an SMBF witness together with typed embeddings of
states, inputs and outputs, and a readout-graph inclusion.

Both directions of the textbook's claims fail, and the two failures have quite
different formal status:

* 5.141 is refuted outright.  Two concrete resultants are built (a lone
  component, and that component cascaded into a state-hiding component).  The
  lone component *is* a subsystem of the pair by an explicit recipe witness,
  and it is *not* a mode of the pair, because coupling internalises its output
  port: the exhibitor's readout is constant, so no injective output embedding
  can satisfy Definition 5.6 (vi).  Nothing is assumed.

* 5.142 is refuted relative to one clearly isolated principle.  A sampled mode
  is exhibited, and the recipe-level obstruction is proved unconditionally:
  a subrecipe embedding forces the resultant state cardinality to *divide* that
  of the larger resultant.  Turning that into `¬ IsSubsystemOf` needs to move
  cardinality information across `HEq Z (rsy SCR hOut)`, which requires
  injectivity of the `DiscreteSystem` type former — not derivable in Lean's type
  theory.  It is therefore exposed as the explicit proposition
  `DiscreteSystemStateReflection` and discharged as a hypothesis, so the
  dependency is visible in the statement rather than hidden in prose.
-/

namespace Mbse.TextbookExercises.Ch05

open WymoreSystemModes
open Mbse.Wymore

variable {S I O : Type}
variable {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
variable {Z : DiscreteSystem S I O}
variable {Z₁ : DiscreteSystem S₁ I₁ O₁}
variable {Z₂ : DiscreteSystem S₂ I₂ O₂}

private lemma fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

/-! ## Exercise 5.141: a subsystem that is not a system mode

The two components share one input port and one output port, both carrying
`Bool`, so all port-type embeddings needed by `IsSubrecipeOf` are reflexivity.
-/

/-- Component whose readout publishes its state on its output port. -/
def revealing : DiscreteSystem Bool (Unit → Bool) (Unit → Bool) :=
  DiscreteSystem.ofTotal (fun _ p => p ()) (fun x _ => x) ⟨false⟩

/-- Component whose readout is constant, so its state is externally invisible. -/
def blind : DiscreteSystem Bool (Unit → Bool) (Unit → Bool) :=
  DiscreteSystem.ofTotal (fun x _ => x) (fun _ _ => false) ⟨false⟩

lemma revealing_alwaysOutputs : AlwaysOutputs revealing := fun x => ⟨fun _ => x, rfl⟩

lemma blind_alwaysOutputs : AlwaysOutputs blind := fun _ => ⟨fun _ => false, rfl⟩

lemma revealing_ne_blind : ¬ HEq revealing blind := by
  intro h
  have he : revealing = blind := eq_of_heq h
  have h2 : (some (fun _ => true) : Option (Unit → Bool)) = some (fun _ => false) :=
    congrArg (fun W => W.RZ true) he
  have h3 : (true : Bool) = false :=
    congrArg (fun g => g ()) (Option.some_injective _ h2)
  exact absurd h3 (by decide)

/-- The one-component vector holding only the revealing component. -/
def loneVSCR : PortSystemVector 1 where
  SZ := fun _ => Bool
  Port := fun _ => Unit
  PortVal := fun _ _ => Bool
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Bool
  Z := fun _ => revealing
  distinct := fun i j hne => absurd (Trajectory.fin_one_eq i j) hne

/-- Singular recipe (`CSCR = ∅`) around the revealing component. -/
def loneSCR : SystemCouplingRecipe 1 where
  VSCR := loneVSCR
  CSCR := ∅
  connectivity := empty_scr_connectivity loneVSCR ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩

def pairZ (i : Fin 2) : DiscreteSystem Bool (Unit → Bool) (Unit → Bool) :=
  Fin.cases revealing (fun _ => blind) i

lemma pairZ_distinct (i j : Fin 2) (hne : i ≠ j) : ¬ HEq (pairZ i) (pairZ j) := by
  rcases fin2_eq_zero_or_one i with hi | hi <;> rcases fin2_eq_zero_or_one j with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · subst hi; subst hj; exact revealing_ne_blind
  · subst hi; subst hj; exact fun h => revealing_ne_blind (HEq.symm h)
  · exact absurd (hi.trans hj.symm) hne

/-- The two-component vector: the revealing component followed by the blind one. -/
def pairVSCR : PortSystemVector 2 where
  SZ := fun _ => Bool
  Port := fun _ => Unit
  PortVal := fun _ _ => Bool
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Bool
  Z := pairZ
  distinct := pairZ_distinct

/-- The single connection: the revealing component's output feeds the blind one's input. -/
def feedPair :
    (Σ (i : Fin 2), pairVSCR.OutPort i) × (Σ (i : Fin 2), pairVSCR.Port i) :=
  (⟨0, ()⟩, ⟨1, ()⟩)

def pairCSCR : Set ((Σ (i : Fin 2), pairVSCR.OutPort i) × (Σ (i : Fin 2), pairVSCR.Port i)) :=
  {feedPair}

lemma pairCSCR_connectivity : IsSystemConnectivity pairVSCR pairCSCR := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro _ y1 y2 h1 h2
    have e1 : y1 = feedPair.2 := congrArg Prod.snd h1
    have e2 : y2 = feedPair.2 := congrArg Prod.snd h2
    rw [e1, e2]
  · intro x1 x2 _ h1 h2
    have e1 : x1 = feedPair.1 := congrArg Prod.fst h1
    have e2 : x2 = feedPair.1 := congrArg Prod.fst h2
    rw [e1, e2]
  · intro h
    have hmem : (⟨1, ()⟩ : Σ (i : Fin 2), pairVSCR.OutPort i) ∈
        {x | ∃ y, (x, y) ∈ pairCSCR} := by
      rw [h]; trivial
    obtain ⟨y, hy⟩ := hmem
    have hpair : ((⟨1, ()⟩ : Σ (i : Fin 2), pairVSCR.OutPort i), y) = feedPair := hy
    have h10 : (1 : Fin 2) = 0 := congrArg (fun q => q.1.1) hpair
    exact absurd h10 (by decide)
  · intro h
    have hmem : (⟨0, ()⟩ : Σ (i : Fin 2), pairVSCR.Port i) ∈
        {y | ∃ x, (x, y) ∈ pairCSCR} := by
      rw [h]; trivial
    obtain ⟨x, hx⟩ := hmem
    have hpair : (x, (⟨0, ()⟩ : Σ (i : Fin 2), pairVSCR.Port i)) = feedPair := hx
    have h01 : (0 : Fin 2) = 1 := congrArg (fun q => q.2.1) hpair
    exact absurd h01 (by decide)
  · intro _ _ _
    rfl

/-- Cascade recipe: revealing component wired into the blind component. -/
def pairSCR : SystemCouplingRecipe 2 where
  VSCR := pairVSCR
  CSCR := pairCSCR
  connectivity := pairCSCR_connectivity

lemma loneSCR_hOut : ∀ i, AlwaysOutputs (loneSCR.VSCR.Z i) :=
  fun _ => revealing_alwaysOutputs

lemma pairSCR_hOut : ∀ i, AlwaysOutputs (pairSCR.VSCR.Z i) := by
  intro i
  rcases fin2_eq_zero_or_one i with h | h
  · subst h; exact revealing_alwaysOutputs
  · subst h; exact blind_alwaysOutputs

/-- `Z₁`: the resultant of the lone revealing component. -/
noncomputable def loneSystem := rsy loneSCR loneSCR_hOut

/-- `Z₂`: the resultant of the cascade. -/
noncomputable def pairSystem := rsy pairSCR pairSCR_hOut

/-- The lone component's output port is external in the singular recipe. -/
def lonePort : UnconnOutPort loneSCR :=
  ⟨⟨0, ()⟩, by
    simp only [UOSCR, Set.mem_compl_iff, COSCR, Set.mem_setOf_eq, not_exists]
    intro ip hip
    exact hip.elim⟩

lemma loneSystem_readout (x : rsy_SZ loneSCR) :
    loneSystem.RZ x = some (fun _ => x 0) := by
  show rsy_RZ loneSCR loneSCR_hOut x = _
  unfold rsy_RZ
  refine congrArg some ?_
  funext op
  obtain ⟨⟨i, u⟩, hmem⟩ := op
  have hi : i = 0 := Trajectory.fin_one_eq i 0
  subst hi
  have hrz : (loneSCR.VSCR.Z 0).RZ (x 0) = some (fun _ => x 0) := rfl
  rw [rsyOutAt_eq_componentReadoutAt loneSCR loneSCR_hOut 0 u x,
    componentReadoutAt_eq_choose, Trajectory.choose_alwaysOutputs _ _ _ hrz]

/--
Coupling internalises the revealing component's output port, so the cascade's
readout is the blind component's constant value at every state.
-/
lemma pairSystem_readout (y : rsy_SZ pairSCR) :
    pairSystem.RZ y = some (fun _ => false) := by
  show rsy_RZ pairSCR pairSCR_hOut y = _
  unfold rsy_RZ
  refine congrArg some ?_
  funext op
  obtain ⟨⟨i, u⟩, hmem⟩ := op
  have hi : i = 1 := by
    rcases fin2_eq_zero_or_one i with h0 | h1
    · exfalso
      apply hmem
      refine ⟨⟨1, ()⟩, ?_⟩
      show ((⟨i, u⟩ : Σ (k : Fin 2), pairVSCR.OutPort k),
        (⟨1, ()⟩ : Σ (k : Fin 2), pairVSCR.Port k)) = feedPair
      subst h0
      rfl
    · exact h1
  subst hi
  have hrz : (pairSCR.VSCR.Z 1).RZ (y 1) = some (fun _ => false) := rfl
  rw [rsyOutAt_eq_componentReadoutAt pairSCR pairSCR_hOut 1 u y,
    componentReadoutAt_eq_choose, Trajectory.choose_alwaysOutputs _ _ _ hrz]

/-- Textbook clauses (iii)–(iv) of Definition 3.97 for the cascade's first component. -/
theorem lone_isSubrecipe : IsSubrecipeOf (fun _ => (0 : Fin 2)) loneSCR pairSCR where
  inj := fun a b _ => Trajectory.fin_one_eq a b
  outPort := fun _ => HEq.rfl
  inPort := fun _ => HEq.rfl
  component := fun _ => HEq.rfl
  cscr := by
    intro p
    constructor
    · intro hp
      exact hp.elim
    · rintro ⟨hmem, -⟩
      have hpair :
          scrEmbedCscrPair (fun _ => (0 : Fin 2)) loneSCR pairSCR
            (fun _ => HEq.rfl) (fun _ => HEq.rfl) p = feedPair := hmem
      have h01 : (0 : Fin 2) = 1 := congrArg (fun q => q.2.1) hpair
      exact absurd h01 (by decide)

/-- The lone component is a subsystem of the cascade, with all recipe witnesses named. -/
theorem lone_isSubsystemVia :
    IsSubsystemVia loneSystem pairSystem loneSCR pairSCR loneSCR_hOut pairSCR_hOut
      (fun _ => (0 : Fin 2)) :=
  ⟨lone_isSubrecipe, HEq.rfl, HEq.rfl⟩

theorem lone_isSubsystem : IsSubsystemOf loneSystem pairSystem :=
  IsSubsystemVia.isSubsystemOf lone_isSubsystemVia

/--
No system mode exists: Definition 5.6 (vi) demands an injective output embedding
carrying the subsystem's readout onto the exhibitor's, but the exhibitor's
readout is constant while the subsystem's separates its two states.
-/
theorem lone_not_isSystemMode : ¬ IsSystemMode loneSystem pairSystem := by
  rintro ⟨M⟩
  have key : ∀ x : rsy_SZ loneSCR, M.outputMap (fun _ => x 0) = fun _ => false := by
    intro x
    have h := M.readout x
    rw [loneSystem_readout x, pairSystem_readout (M.stateMap x)] at h
    exact Option.some_injective _ h
  have hTrue := key (fun _ => true)
  have hFalse := key (fun _ => false)
  have hfun : (fun _ => true : rsy_OZ loneSCR) = fun _ => false :=
    M.outputMap_injective (hTrue.trans hFalse.symm)
  have hbool : (true : Bool) = false := congrArg (fun g => g lonePort) hfun
  exact absurd hbool (by decide)

/--
  [textbook/exercise5.141/source/exercise]
  [textbook/exercise5.141/plan/subsystem_isSystemMode_or_counterexample]
  [textbook/exercise5.141/counterexample/literal_claim]

Ex. 5.141 — the assertion is **false**, with a fully checked finite
counterexample: `RSY` of the lone revealing component is a subsystem of `RSY` of
the cascade, yet it is not a system mode of it.  No hypotheses are assumed.
-/
theorem subsystem_isSystemMode_or_counterexample :
    IsSubsystemOf loneSystem pairSystem ∧ ¬ IsSystemMode loneSystem pairSystem :=
  ⟨lone_isSubsystem, lone_not_isSystemMode⟩

/-! ## Exercise 5.142: a system mode that is not a subsystem -/

/-- Three-cycle exhibitor: one anonymous input, readout equal to the state. -/
def cycleExhibitor : DiscreteSystem (Fin 3) Unit (Fin 3) :=
  DiscreteSystem.ofTotal (fun x _ => x + 1) id ⟨0⟩

/-- The sampled mode of the three-cycle: every mode step is two exhibitor steps. -/
def cycleSampledMode : DiscreteSystem (Fin 3) Unit (Fin 3) :=
  DiscreteSystem.ofTotal (fun x _ => x + 2) id ⟨0⟩

def cycleSampledModeWitness : SystemMode cycleSampledMode cycleExhibitor where
  stateMap := id
  inputMap := id
  outputMap := id
  stateMap_injective := Function.injective_id
  inputMap_injective := Function.injective_id
  outputMap_injective := Function.injective_id
  behavior :=
    { input := fun _ _ _ => ()
      duration := fun _ _ => 2
      duration_pos := fun _ _ => by decide }
  behavior_initial := fun _ _ => rfl
  transition := by decide
  readout := by decide

lemma cycleSampledMode_constantInput : HasConstantInput cycleSampledModeWitness :=
  fun _ _ _ => rfl

lemma cycleSampledMode_constantTimeIndex :
    HasConstantTimeIndex cycleSampledModeWitness 2 :=
  ⟨by decide, fun _ _ => rfl⟩

/-- Two-state mode of the three-cycle, with a variable time index (`1` then `2`). -/
def twoStateMode : DiscreteSystem (Fin 2) Unit (Fin 2) :=
  DiscreteSystem.ofTotal (fun x _ => x + 1) id ⟨0⟩

/-- The state embedding `{0, 1} ↪ {0, 1, 2}` of the two-state mode. -/
def embed01 : Fin 2 → Fin 3 := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by decide)⟩

lemma embed01_injective : Function.Injective embed01 := by
  intro a b h
  have hv : (embed01 a).val = (embed01 b).val := congrArg Fin.val h
  exact Fin.ext hv

def twoStateModeWitness : SystemMode twoStateMode cycleExhibitor where
  stateMap := embed01
  inputMap := id
  outputMap := embed01
  stateMap_injective := embed01_injective
  inputMap_injective := Function.injective_id
  outputMap_injective := embed01_injective
  behavior :=
    { input := fun _ _ _ => ()
      duration := fun x _ => x.val + 1
      duration_pos := fun _ _ => Nat.succ_pos _ }
  behavior_initial := fun _ _ => rfl
  transition := by decide
  readout := by decide

/--
Unconditional semantic content of Ex. 5.142: the mode's transition is not the
exhibitor's transition restricted to the embedded states, since one mode step
from state `1` samples two exhibitor steps.
-/
theorem twoStateMode_transition_not_restriction :
    embed01 (twoStateMode.NZ 1 (some ())) ≠ cycleExhibitor.NZ (embed01 1) (some ()) := by
  decide

/--
Injectivity of the `DiscreteSystem` type former in its state argument.

This is the named Prop package for Def 3.97 `HEq` packaging (see also
[`Homomorphism.DiscreteSystemStateReflectionDoc`] in `CouplingPortMaps.lean`):
not a new axiom, but a reusable hypothesis for subsystem arguments such as
Exercise 5.142.  `HEq Z (rsy SCR hOut)` yields only equality of the two
`DiscreteSystem` *applications*, and Lean proves no injectivity for type
formers, so the state type of `Z` cannot otherwise be identified with
`rsy_SZ SCR`.  Nor can cardinality substitute for it: a recipe whose components
all have one state has resultant state cardinality `1` and resultant readout
cardinality unconstrained, so `Nat.card (DiscreteSystem A B C)` — the only
invariant a type equality transports — is matched by such recipes for every
`A`, `B`, `C`, and `1` divides everything.  Every cardinality argument
therefore collapses, which is why the principle is named and taken as a
hypothesis here instead of being assumed silently.  It holds in the standard
set-theoretic semantics of Lean's type theory.
-/
def DiscreteSystemStateReflection : Prop :=
  ∀ {A B C A' B' C' : Type}, DiscreteSystem A B C = DiscreteSystem A' B' C' → A = A'

/--
Unconditional recipe-level obstruction: a component embedding makes the smaller
resultant's state cardinality divide the larger one's, because resultant states
are products over components and `φ` is injective.
-/
theorem resultant_state_card_dvd {n1 n2 : Nat} {φ : Fin n1 → Fin n2}
    {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    (hinj : Function.Injective φ)
    (hcard : ∀ i, Nat.card (SCR1.VSCR.SZ i) = Nat.card (SCR2.VSCR.SZ (φ i))) :
    Nat.card (rsy_SZ SCR1) ∣ Nat.card (rsy_SZ SCR2) := by
  classical
  have h1 : Nat.card (rsy_SZ SCR1) = ∏ i : Fin n1, Nat.card (SCR2.VSCR.SZ (φ i)) := by
    show Nat.card ((i : Fin n1) → SCR1.VSCR.SZ i) = _
    rw [Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => hcard i
  have h2 : Nat.card (rsy_SZ SCR2) = ∏ j : Fin n2, Nat.card (SCR2.VSCR.SZ j) := by
    show Nat.card ((j : Fin n2) → SCR2.VSCR.SZ j) = _
    rw [Nat.card_pi]
  have himage : (∏ i : Fin n1, Nat.card (SCR2.VSCR.SZ (φ i))) =
      ∏ j ∈ Finset.univ.map ⟨φ, hinj⟩, Nat.card (SCR2.VSCR.SZ j) := by
    rw [Finset.prod_map]
    rfl
  rw [h1, h2, himage]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

/-- Transported to the systems themselves, the obstruction constrains `IsSubsystemOf`. -/
theorem subsystem_state_card_dvd (H : DiscreteSystemStateReflection)
    {A B C A' B' C' : Type} {W₁ : DiscreteSystem A B C} {W₂ : DiscreteSystem A' B' C'}
    (h : IsSubsystemOf W₁ W₂) : Nat.card A ∣ Nat.card A' := by
  obtain ⟨n1, n2, SCR1, SCR2, hOut1, hOut2, φ, hOutPort, hInPort, hinj, hcomp, hZ1, hZ2, -⟩ := h
  have e1 : A = rsy_SZ SCR1 := H (type_eq_of_heq hZ1)
  have e2 : A' = rsy_SZ SCR2 := H (type_eq_of_heq hZ2)
  have ec : ∀ i, Nat.card (SCR1.VSCR.SZ i) = Nat.card (SCR2.VSCR.SZ (φ i)) := fun i =>
    congrArg Nat.card (H (type_eq_of_heq (hcomp i)))
  rw [e1, e2]
  exact resultant_state_card_dvd hinj ec

/--
  [textbook/exercise5.142/source/exercise|partial]
  [textbook/exercise5.142/plan/exercise5_142_unconditional|partial]

Unconditional charitable answer to Exercise 5.142: the two-state sampled mode
of the three-cycle is a system mode, and no injective component embedding with
matching component state cards can realize resultant cards `2` and `3`.
-/
theorem exercise5_142_unconditional :
    IsSystemMode twoStateMode cycleExhibitor ∧
      ∀ {n1 n2 : Nat} {φ : Fin n1 → Fin n2}
        {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2},
        Function.Injective φ →
        (∀ i, Nat.card (SCR1.VSCR.SZ i) = Nat.card (SCR2.VSCR.SZ (φ i))) →
        Nat.card (rsy_SZ SCR1) = 2 → Nat.card (rsy_SZ SCR2) = 3 → False := by
  refine ⟨⟨twoStateModeWitness⟩, ?_⟩
  intro n1 n2 φ SCR1 SCR2 hinj hcard h2 h3
  have hdvd := resultant_state_card_dvd hinj hcard
  rw [h2, h3] at hdvd
  exact absurd hdvd (by decide)

/--
  [textbook/exercise5.142/plan/systemMode_not_subsystem_counterexample|partial]
  [textbook/exercise5.142/counterexample/literal_claim|partial]

Conditional packaging under `DiscreteSystemStateReflection`: Lean cannot derive
type-former injectivity from `HEq` on `DiscreteSystem`, so `¬ IsSubsystemOf`
needs that named hypothesis.  The unconditional content is
`exercise5_142_unconditional`.
-/
theorem systemMode_not_subsystem_counterexample (H : DiscreteSystemStateReflection) :
    IsSystemMode twoStateMode cycleExhibitor ∧
      ¬ IsSubsystemOf twoStateMode cycleExhibitor := by
  refine ⟨⟨twoStateModeWitness⟩, fun h => ?_⟩
  have hdvd := subsystem_state_card_dvd H h
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
  exact absurd hdvd (by decide)

/-! ## Constant trajectories -/

def constantState (Z : DiscreteSystem S I O) (x : S) (p : I) (t : Time) : S :=
  generateStateTrajectory Z x (liftInput (fun _ => p)) t

lemma constantState_zero (Z : DiscreteSystem S I O) (x : S) (p : I) :
    constantState Z x p 0 = x := rfl

lemma constantState_succ (Z : DiscreteSystem S I O) (x : S) (p : I) (t : Time) :
    constantState Z x p (t + 1) = Z.NZ (constantState Z x p t) (some p) := rfl

lemma constantState_add (Z : DiscreteSystem S I O) (x : S) (p : I) (a b : Time) :
    constantState Z x p (a + b) = constantState Z (constantState Z x p a) p b := by
  symm
  exact Trajectory.stateTrajectory_time_invariance Z x (liftInput (fun _ => p)) a b

/-! ## Exercise 5.146 -/

/--
  [textbook/exercise5.146/source/exercise]
  [textbook/exercise5.146/plan/selfMode_constantTime_iterate]

The substantive induction behind Exercise 5.146.  If every constant-input
`d`-step evolution equals one step, then the same is true after
`k * (d - 1) + 1` steps for every positive `k`.
-/
theorem selfMode_constantTime_iterate
    (hbase : ∀ x p, constantState Z x p d = Z.NZ x (some p))
    (hd : 0 < d) :
    ∀ k, 0 < k → ∀ x p,
      constantState Z x p (k * (d - 1) + 1) = Z.NZ x (some p) := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  clear hk
  intro x p
  have hstable : ∀ y, constantState Z (Z.NZ y (some p)) p (d - 1) =
      Z.NZ y (some p) := by
    intro y
    have hsplit := constantState_add Z y p 1 (d - 1)
    have hd_eq : 1 + (d - 1) = d :=
      Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
    rw [hd_eq, hbase] at hsplit
    exact hsplit.symm
  induction n generalizing x with
  | zero =>
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))]
        using hbase x p
  | succ n ih =>
      have harith :
          (n.succ.succ * (d - 1) + 1) =
            (n.succ * (d - 1) + 1) + (d - 1) := by
        simp only [Nat.succ_mul]
        omega
      rw [harith]
      rw [constantState_add]
      rw [ih]
      exact hstable x

/--
The exercise's system-mode conclusion, with the source's implicit identity
inclusions made explicit.  The new witness has constant input and the claimed
time index.
-/
def selfModeAtIteratedTime
    (M : SystemMode Z Z)
    (hstate : M.stateMap = id) (hinputMap : M.inputMap = id)
    (houtput : M.outputMap = id)
    (hconstant : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (k : Time) (hk : 0 < k) :
    SystemMode Z Z where
  stateMap := id
  inputMap := id
  outputMap := id
  stateMap_injective := Function.injective_id
  inputMap_injective := Function.injective_id
  outputMap_injective := Function.injective_id
  behavior :=
    { input := fun _ p _ => p
      duration := fun _ _ => k * (d - 1) + 1
      duration_pos := fun _ _ => Nat.zero_lt_succ _ }
  behavior_initial := fun _ _ => rfl
  transition := by
    intro x p
    have hbase : ∀ y q, constantState Z y q d = Z.NZ y (some q) := by
      intro y q
      have htrans := M.transition y q
      rw [hstate] at htrans
      simp only [Function.id_def] at htrans
      have hduration := htime.2 y q
      change M.behavior.duration y q = d at hduration
      rw [hduration] at htrans
      have hfun : M.inputIndex y q = fun _ => q := by
        funext t
        simpa [hinputMap] using hconstant y q t
      change M.behavior.input y q = fun _ => q at hfun
      rw [hfun] at htrans
      exact htrans.symm
    exact (selfMode_constantTime_iterate hbase htime.1 k hk x p).symm
  readout := by
    intro x
    have hr := M.readout x
    rw [hstate, houtput] at hr
    exact hr

theorem selfModeAtIteratedTime_hasIndices
    (M : SystemMode Z Z)
    (hstate : M.stateMap = id) (hinputMap : M.inputMap = id)
    (houtput : M.outputMap = id)
    (hconstant : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (k : Time) (hk : 0 < k) :
    HasConstantInput (selfModeAtIteratedTime M hstate hinputMap houtput hconstant d htime k hk) ∧
      HasConstantTimeIndex
        (selfModeAtIteratedTime M hstate hinputMap houtput hconstant d htime k hk)
        (k * (d - 1) + 1) :=
  ⟨fun _ _ _ => rfl, Nat.zero_lt_succ _, fun _ _ => rfl⟩

/-! ## Exercise 5.147 -/

/--
  [textbook/exercise5.147/source/exercise]
  [textbook/exercise5.147/plan/constantMode_state_at_mul]

`m` mode steps take `d * m` exhibitor steps.
-/
theorem constantMode_state_at_mul
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (d : Time) (htime : HasConstantTimeIndex M d)
    (x : S₁) (p : I₁) (m : Time) :
    M.stateMap (constantState Z₁ x p m) =
      constantState Z₂ (M.stateMap x) (M.inputMap p) (d * m) := by
  have h := constant_compiled_state M hinput d htime x (fun _ => p) m
  simpa [constantState, expandConstantInput] using h.symm

/-! ## Exercise 5.148 -/

/-- The recursively accumulated exhibitor time `H` from Exercise 5.148. -/
def accumulatedModeTime (M : SystemMode Z₁ Z₂) (x : S₁) (p : I₁) : Time → Time
  | 0 => 0
  | t + 1 => accumulatedModeTime M x p t + M.timeIndex (constantState Z₁ x p t) p

lemma accumulatedModeTime_eq_compiledElapsed
    (M : SystemMode Z₁ Z₂) (x : S₁) (p : I₁) :
    ∀ t, accumulatedModeTime M x p t = compiledElapsed M x (fun _ => p) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [accumulatedModeTime, compiledElapsed]
      rw [ih]
      rfl

lemma compiledInput_eq_constant_of_constantInput
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (x : S₁) (p : I₁) :
    ∀ n t, compiledInput M x (fun _ => p) n t = M.inputMap p := by
  intro n
  induction n with
  | zero =>
      intro t
      exact hinput x p t
  | succ n ih =>
      intro t
      simp only [compiledInput]
      unfold concatenate
      split
      · exact ih t
      · apply hinput

/--
  [textbook/exercise5.148/source/exercise]
  [textbook/exercise5.148/plan/variableTime_constantInput_state_at_accumulatedTime]

The corrected variable-time law, proved for every time by the general
concatenation induction.  No constant-time assumption is used.
-/
theorem variableTime_constantInput_state_at_accumulatedTime
    (M : SystemMode Z₁ Z₂) (hinput : HasConstantInput M)
    (x : S₁) (p : I₁) :
    ∀ t,
      M.stateMap (constantState Z₁ x p t) =
        constantState Z₂ (M.stateMap x) (M.inputMap p)
          (accumulatedModeTime M x p t) := by
  intro t
  have hcompiled := compiled_state M x (fun _ => p) t
  have hfun : compiledInput M x (fun _ => p) t = fun _ => M.inputMap p := by
    funext u
    exact compiledInput_eq_constant_of_constantInput M hinput x p t u
  rw [hfun, ← accumulatedModeTime_eq_compiledElapsed M x p t] at hcompiled
  exact hcompiled.symm

end Mbse.TextbookExercises.Ch05
