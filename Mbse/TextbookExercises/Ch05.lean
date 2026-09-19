import Mbse.WymoreSystemModes
import Mbse.WymoreCouplingStructure
import Mbse.WymoreImplementation
import Mbse.Isomorphism

/-!
# Chapter 5 — system-mode exercises

Exercises 5.141, 5.142, 5.146–5.153, and 5.156–5.179.

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

/-! ## Exercise 5.149 -/

variable {S₃ I₃ O₃ : Type}
variable {Z₃ : DiscreteSystem S₃ I₃ O₃}

/-- Constant-input modes compose via `SystemMode.trans`. -/
def constantMode_compose
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (_hIn₁₂ : HasConstantInput M₁₂) (_e : Time) (_hE : HasConstantTimeIndex M₁₂ _e)
    (_hIn₂₃ : HasConstantInput M₂₃) (_d : Time) (_hD : HasConstantTimeIndex M₂₃ _d) :
    SystemMode Z₁ Z₃ :=
  M₁₂.trans M₂₃

/--
  [textbook/exercise5.149/source/exercise]
  [textbook/exercise5.149/plan/constantMode_compose_indices]

Constant-input modes of times `e` and `d` compose to a constant-input mode of
time `e * d`.
-/
theorem constantMode_compose_indices
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (hIn₁₂ : HasConstantInput M₁₂) (e : Time) (hE : HasConstantTimeIndex M₁₂ e)
    (hIn₂₃ : HasConstantInput M₂₃) (d : Time) (hD : HasConstantTimeIndex M₂₃ d) :
    HasConstantInput (constantMode_compose M₁₂ M₂₃ hIn₁₂ e hE hIn₂₃ d hD) ∧
      HasConstantTimeIndex (constantMode_compose M₁₂ M₂₃ hIn₁₂ e hE hIn₂₃ d hD)
        (e * d) :=
  SystemMode.trans_constant M₁₂ M₂₃ hIn₁₂ e hE hIn₂₃ d hD

/-! ## Exercise 5.150 -/

/-- Variable-time composition spine (`SystemMode.trans`). -/
def variableTime_compose
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (_hIn₁₂ : HasConstantInput M₁₂) (_hIn₂₃ : HasConstantInput M₂₃) :
    SystemMode Z₁ Z₃ :=
  M₁₂.trans M₂₃

/--
  [textbook/exercise5.150/source/exercise]
  [textbook/exercise5.150/plan/variableTime_compose_isSystemMode]

Variable-time constant-input composition: the composite duration is the
compiled elapsed time `TI` of the second mode along the first mode's constant
trajectory (the book's sum).
-/
theorem variableTime_compose_isSystemMode
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (hIn₁₂ : HasConstantInput M₁₂) (hIn₂₃ : HasConstantInput M₂₃) :
    IsSystemMode Z₁ Z₃ :=
  ⟨variableTime_compose M₁₂ M₂₃ hIn₁₂ hIn₂₃⟩

theorem variableTime_compose_TI
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (hIn₁₂ : HasConstantInput M₁₂) (hIn₂₃ : HasConstantInput M₂₃)
    (x : S₁) (p : I₁) :
    (variableTime_compose M₁₂ M₂₃ hIn₁₂ hIn₂₃).timeIndex x p =
      compiledElapsed M₂₃ (M₁₂.stateMap x) (fun _ => M₁₂.inputMap p)
        (M₁₂.timeIndex x p) := by
  change compiledElapsed M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
      (M₁₂.timeIndex x p) = _
  congr 1
  funext u
  exact hIn₁₂ x p u

theorem variableTime_compose_constantInput
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₃ : SystemMode Z₂ Z₃)
    (hIn₁₂ : HasConstantInput M₁₂) (hIn₂₃ : HasConstantInput M₂₃) :
    HasConstantInput (variableTime_compose M₁₂ M₂₃ hIn₁₂ hIn₂₃) := by
  intro x p t
  change compiledInput M₂₃ (M₁₂.stateMap x) (M₁₂.inputIndex x p)
      (M₁₂.timeIndex x p) t = (M₂₃.inputMap ∘ M₁₂.inputMap) p
  have hfun : M₁₂.inputIndex x p = fun _ => M₁₂.inputMap p := by
    funext u; exact hIn₁₂ x p u
  rw [hfun]
  simpa [Function.comp_apply] using
    compiledInput_constant M₂₃ hIn₂₃ (M₁₂.stateMap x) (M₁₂.inputMap p)
      (M₁₂.timeIndex x p) t

/-! ## Exercise 5.151 -/

/-- Round-trip self-mode at `d * d` from mutual constant modes. -/
def mutual_constantMode_self_d_sq
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₁ : SystemMode Z₂ Z₁)
    (hIn₁₂ : HasConstantInput M₁₂) (hIn₂₁ : HasConstantInput M₂₁)
    (d : Time) (h₁₂ : HasConstantTimeIndex M₁₂ d)
    (h₂₁ : HasConstantTimeIndex M₂₁ d) :
    SystemMode Z₁ Z₁ :=
  constantMode_compose M₁₂ M₂₁ hIn₁₂ d h₁₂ hIn₂₁ d h₂₁

/--
  [textbook/exercise5.151/source/exercise]
  [textbook/exercise5.151/plan/mutual_constantMode_self_d_sq_indices]

Mutual constant modes of common duration `d` yield, via 5.149, a self-mode of
each system at time `d * d` after the round-trip embeddings.
-/
theorem mutual_constantMode_self_d_sq_indices
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₁ : SystemMode Z₂ Z₁)
    (hIn₁₂ : HasConstantInput M₁₂) (hIn₂₁ : HasConstantInput M₂₁)
    (d : Time) (h₁₂ : HasConstantTimeIndex M₁₂ d)
    (h₂₁ : HasConstantTimeIndex M₂₁ d) :
    HasConstantInput (mutual_constantMode_self_d_sq M₁₂ M₂₁ hIn₁₂ hIn₂₁ d h₁₂ h₂₁) ∧
      HasConstantTimeIndex
        (mutual_constantMode_self_d_sq M₁₂ M₂₁ hIn₁₂ hIn₂₁ d h₁₂ h₂₁) (d * d) :=
  constantMode_compose_indices M₁₂ M₂₁ hIn₁₂ d h₁₂ hIn₂₁ d h₂₁

/-! ## Exercise 5.152 -/

open Homomorphism

/--
  [textbook/exercise5.152/source/exercise]
  [textbook/exercise5.152/plan/mutual_primary_modes_isomorphic]

Charitable reading of “Z₁ = Z₂”: mutual primary modes whose embeddings are
mutual inverses, on systems that stutter autonomously, yield an isomorphism.
Literal identification of distinct Lean types is not claimed.
-/
noncomputable def mutual_primary_modes_isomorphism
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₁ : SystemMode Z₂ Z₁)
    (_h₁₂ : IsPrimaryMode M₁₂) (h₂₁ : IsPrimaryMode M₂₁)
    (hS : Function.LeftInverse M₂₁.stateMap M₁₂.stateMap ∧
      Function.RightInverse M₂₁.stateMap M₁₂.stateMap)
    (hI : Function.LeftInverse M₂₁.inputMap M₁₂.inputMap ∧
      Function.RightInverse M₂₁.inputMap M₁₂.inputMap)
    (hO : Function.LeftInverse M₂₁.outputMap M₁₂.outputMap ∧
      Function.RightInverse M₂₁.outputMap M₁₂.outputMap)
    (hAuto₁ : ∀ x, Z₁.NZ x none = x) (hAuto₂ : ∀ x, Z₂.NZ x none = x) :
    IsomorphismWitness Z₁ Z₂ where
  toHomomorphicImageWitness :=
    { HS := M₂₁.stateMap
      HI := M₂₁.inputMap
      HO := M₂₁.outputMap
      HS_surjective := hS.1.surjective
      HI_surjective := hI.1.surjective
      HO_surjective := hO.1.surjective
      preserves_transition := by
        intro x oi
        cases oi with
        | none =>
            simp [hAuto₁, hAuto₂]
        | some p =>
            exact primary_preserves_transition M₂₁ h₂₁ x p
      preserves_readout := M₂₁.readout }
  HS_injective := Function.RightInverse.injective hS.2
  HI_injective := Function.RightInverse.injective hI.2
  HO_injective := Function.RightInverse.injective hO.2

theorem mutual_primary_modes_isomorphic
    (M₁₂ : SystemMode Z₁ Z₂) (M₂₁ : SystemMode Z₂ Z₁)
    (h₁₂ : IsPrimaryMode M₁₂) (h₂₁ : IsPrimaryMode M₂₁)
    (hS : Function.LeftInverse M₂₁.stateMap M₁₂.stateMap ∧
      Function.RightInverse M₂₁.stateMap M₁₂.stateMap)
    (hI : Function.LeftInverse M₂₁.inputMap M₁₂.inputMap ∧
      Function.RightInverse M₂₁.inputMap M₁₂.inputMap)
    (hO : Function.LeftInverse M₂₁.outputMap M₁₂.outputMap ∧
      Function.RightInverse M₂₁.outputMap M₁₂.outputMap)
    (hAuto₁ : ∀ x, Z₁.NZ x none = x) (hAuto₂ : ∀ x, Z₂.NZ x none = x) :
    IsIsomorphicTo Z₁ Z₂ :=
  ⟨mutual_primary_modes_isomorphism M₁₂ M₂₁ h₁₂ h₂₁ hS hI hO hAuto₁ hAuto₂⟩

/-! ## Exercise 5.153 -/

/--
Exhibitor as a duration-2 mode of the sampled system: `+1` is two `+2` steps
on `Fin 3`.
-/
def cycleExhibitor_as_mode_of_sampled : SystemMode cycleExhibitor cycleSampledMode where
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

/--
  [textbook/exercise5.153/source/exercise]
  [textbook/exercise5.153/plan/mutual_modes_not_equal_counterexample]

Counterexample: `cycleSampledMode` and `cycleExhibitor` are mutual system modes
(duration 2 each way) but are unequal as systems (`+2` vs `+1`).
-/
theorem mutual_modes_not_equal_counterexample :
    IsSystemMode cycleSampledMode cycleExhibitor ∧
      IsSystemMode cycleExhibitor cycleSampledMode ∧
      cycleSampledMode.NZ 0 (some ()) ≠ cycleExhibitor.NZ 0 (some ()) :=
  ⟨⟨cycleSampledModeWitness⟩, ⟨cycleExhibitor_as_mode_of_sampled⟩, by decide⟩

/-! ## Exercise 5.156 -/

/--
  [textbook/exercise5.156/source/exercise]
  [textbook/exercise5.156/plan/not_manifest_zero_not_inMode]

If the mode is not manifest at time 0, the exhibitor is not in the mode at 0.
-/
theorem not_manifest_zero_not_inMode
    (M : SystemMode Z₁ Z₂) (f : ITZW I₂) (x : S₂) (t : Time)
    (h : ¬ ManifestAt M f x t 0) : ¬ InModeAt M f x t 0 :=
  not_inMode_of_not_manifest_zero M f x t h

/-! ## Exercise 5.157 -/

/--
  [textbook/exercise5.157/source/exercise]
  [textbook/exercise5.157/plan/primary_has_CNS_SMBF]

A primary mode admits the canonical constant-input duration-one SMBF.
-/
theorem primary_has_CNS_SMBF (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M) :
    IsPrimaryMode (primaryConstantInputMode M h) ∧
      HasConstantInput (primaryConstantInputMode M h) ∧
      HasConstantTimeIndex (primaryConstantInputMode M h) 1 :=
  ⟨⟨Nat.zero_lt_one, fun _ _ => rfl⟩,
    primaryConstantInputMode_constantInput M h,
    primaryConstantInputMode_time M h⟩

/-! ## Exercise 5.158 -/

/--
  [textbook/exercise5.158/source/exercise]
  [textbook/exercise5.158/plan/primary_NZ_RZ_restriction]

Typed reading of `NZ₁ = RSN(NZ₂, SZ₁ × IZ₁)` and `RZ₁ = RSN(RZ₂, SZ₁)`.
-/
theorem primary_NZ_RZ_restriction (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M) :
    (∀ x p, M.stateMap (Z₁.NZ x (some p)) =
      Z₂.NZ (M.stateMap x) (some (M.inputMap p))) ∧
      (∀ x, (Z₁.RZ x).map M.outputMap = Z₂.RZ (M.stateMap x)) :=
  ⟨primary_preserves_transition M h, M.readout⟩

/-! ## Exercise 5.159 -/

/--
  [textbook/exercise5.159/source/exercise]
  [textbook/exercise5.159/plan/primary_manifest_persists]

A primary mode remains manifest while exhibitor inputs stay in the image of the
mode input embedding.
-/
theorem primary_manifest_persists
    (M : SystemMode Z₁ Z₂) (h : IsPrimaryMode M)
    (f : ITZW I₂) (x : S₂) (t s : Time)
    (hmanifest : ManifestAt M f x t s)
    (r : Time) (hr : s + r ≤ t)
    (hseg : ∀ u, u < r → ∃ p : I₁, f (s + u) = some (M.inputMap p)) :
    ManifestAt M f x t (s + r) := by
  induction r generalizing s with
  | zero =>
      simpa using hmanifest
  | succ r ih =>
      rcases hmanifest with ⟨_, x₁, hx₁⟩
      obtain ⟨p, hp⟩ := hseg 0 (Nat.zero_lt_succ r)
      have hfs : f s = some (M.inputMap p) := by
        simpa only [Nat.add_zero] using hp
      have hstep :
          generateStateTrajectory Z₂ x f (s + 1) =
            M.stateMap (Z₁.NZ x₁ (some p)) := by
        rw [generateStateTrajectory_succ, hx₁, hfs]
        exact (primary_preserves_transition M h x₁ p).symm
      have hle' : s + 1 ≤ t := by
        have h1 : s + 1 ≤ s + (r + 1) := Nat.succ_le_succ (Nat.le_add_right s r)
        have h2 : s + (r + 1) ≤ t := hr
        exact Nat.le_trans h1 h2
      have hmanifest1 : ManifestAt M f x t (s + 1) := ⟨hle', _, hstep⟩
      have hseg' : ∀ u, u < r → ∃ p : I₁, f ((s + 1) + u) = some (M.inputMap p) := by
        intro u hu
        obtain ⟨p', hp'⟩ := hseg (u + 1) (Nat.succ_lt_succ hu)
        refine ⟨p', ?_⟩
        have : (s + 1) + u = s + (u + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 u]
        rwa [this]
      have hr' : (s + 1) + r ≤ t := by
        have : (s + 1) + r = s + (r + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 r]
        rwa [this]
      have ihout := ih (s + 1) hmanifest1 hr' hseg'
      have : s + (r + 1) = (s + 1) + r := by
        rw [Nat.add_assoc, Nat.add_comm 1 r]
      rw [this]
      exact ihout

/-! ## Exercise 5.160 — `RSYSMO` is a system parameterization -/

/--
  [textbook/exercise5.160/source/exercise]
  [textbook/exercise5.160/plan/rsysmo_isSystemParameterization]
  Exercise 5.160: `RSYSMO` is a `DiscreteSystemParameterization`.
-/
theorem rsysmo_isSystemParameterization (p : ReachableModeParam) :
    rsysmo p = reachableModeSystem p.Z p.A p.hA :=
  rsysmo_eq p

/-! ## Exercise 5.161 — reachable mode is primary -/

/--
  [textbook/exercise5.161/source/exercise]
  [textbook/exercise5.161/plan/reachableMode_isPrimary_exercise]
  Exercise 5.161: the reachable system mode is primary.
-/
theorem reachableMode_isPrimary_exercise (Z : DiscreteSystem S₂ I₂ O₂)
    (A : Set S₂) (hA : A.Nonempty) :
    IsPrimaryMode (reachableMode Z A hA) :=
  reachableMode_isPrimary Z A hA

/-! ## Exercise 5.162 — complement of an isolated mode is isolated -/

/--
  [textbook/exercise5.162/source/exercise]
  [textbook/exercise5.162/plan/complement_isolated_isIsolated]
  Exercise 5.162: the complement of an isolated mode's state set carries another
  isolated mode.
-/
theorem complement_isolated_isIsolated (M : SystemMode Z₁ Z₂)
    (h : IsIsolatedMode M) (hproper : IsProperMode M) :
    IsIsolatedMode (complementMode M h hproper) :=
  complementMode_isIsolated M h hproper

/-! ## Exercise 5.163 — stay in an isolated mode throughout an experiment -/

/--
  [textbook/exercise5.163/source/exercise]
  [textbook/exercise5.163/plan/isolated_throughout_iff_start]
  Exercise 5.163: under total exhibitor inputs, an isolated mode is occupied
  throughout an experiment iff the start state lies in the mode.
-/
theorem isolated_throughout_iff_start (M : SystemMode Z₁ Z₂)
    (h : IsIsolatedMode M) (f : ITZ I₂) (x : S₂) (t : Time) :
    (∀ s ≤ t, InModeAt M (liftInput f) x t s) ↔ ∃ x₁, x = M.stateMap x₁ :=
  isolated_throughout_iff M h f x t

/-! ## Exercise 5.164 — transient vs isolated differences -/

/--
  [textbook/exercise5.164/source/exercise]
  [textbook/exercise5.164/plan/transient_vs_isolated_exercise]
  Exercise 5.164: typed input and closure differences between transient and
  isolated modes (exhibitor autonomous stutter assumed).
-/
theorem transient_vs_isolated_exercise (M : SystemMode Z₁ Z₂)
    (haut : ∀ y : S₂, Z₂.NZ y none = y) :
    (IsTransientMode M →
      ¬ Function.Surjective M.inputMap ∧
        ∃ (x : S₁) (p : I₂), ∀ x' : S₁, Z₂.NZ (M.stateMap x) (some p) ≠ M.stateMap x') ∧
    (IsIsolatedMode M →
      Function.Surjective M.inputMap ∧
        ∀ (x : S₁) (p : I₂), ∃ x' : S₁, Z₂.NZ (M.stateMap x) (some p) = M.stateMap x') :=
  transient_vs_isolated_differences M haut

/-! ## Exercise 5.165 — transient state generates a transient mode -/

/--
  [textbook/exercise5.165/source/exercise]
  [textbook/exercise5.165/plan/transientState_generates_transientMode_exercise]
  Exercise 5.165: a transient state with nonempty stay-input set generates a
  transient singleton mode.
-/
theorem transientState_generates_transientMode_exercise
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (htrans : IsTransientState Z x')
    (hne : Nonempty (StayInput Z x'))
    (hproper : ∃ y : S₂, y ≠ x') :
    IsTransientMode (transientStateMode Z x' hne) :=
  transientState_generates_transientMode Z x' htrans hne hproper

/-! ## Exercise 5.166 — absorbing state generates absorbing trivial `RSYSMO` -/

/--
  [textbook/exercise5.166/source/exercise]
  [textbook/exercise5.166/plan/absorbingState_generates_absorbing_rsysmo]
  Exercise 5.166: an absorbing state generates an absorbing trivial reachable
  mode `RSYSMO(Z, {x'})`, and the explicit singleton mode is likewise absorbing
  and trivial.
-/
theorem absorbingState_generates_absorbing_rsysmo
    (Z : DiscreteSystem S₂ I₂ O₂) (x' : S₂)
    (habs : IsAbsorbingState Z x') (haut : Z.NZ x' none = x')
    (hproper : ∃ y : S₂, y ≠ x') :
    IsAbsorbingMode (reachableMode Z ({x'} : Set S₂) ⟨x', rfl⟩) ∧
      IsTrivialMode (reachableMode Z ({x'} : Set S₂) ⟨x', rfl⟩) ∧
      IsAbsorbingMode (absorbingStateMode Z x' habs) ∧
      IsTrivialMode (absorbingStateMode Z x' habs) ∧
      (∀ y, ReachableFromSet Z {x'} y ↔ y = x') := by
  have hR := absorbing_reachableMode_properties Z x' habs haut hproper
  exact ⟨hR.1, hR.2, absorbingStateMode_isAbsorbing Z x' habs hproper,
    absorbingStateMode_isTrivial Z x' habs,
    fun y => reachableFromSet_of_absorbing Z x' habs haut y⟩

/-! ## Exercise 5.167 — proper reachable mode is absorbing -/

/--
  [textbook/exercise5.167/source/exercise]
  [textbook/exercise5.167/plan/proper_reachableMode_absorbing_exercise]
  Exercise 5.167: export of Theorem 5.37.
-/
theorem proper_reachableMode_absorbing_exercise (Z : DiscreteSystem S₂ I₂ O₂)
    (A : Set S₂) (hA : A.Nonempty) (hproper : IsProperMode (reachableMode Z A hA)) :
    IsAbsorbingMode (reachableMode Z A hA) :=
  proper_reachableMode_absorbing Z A hA hproper

/-! ## Exercise 5.168 — isolated mode is absorbing -/

/--
  [textbook/exercise5.168/source/exercise]
  [textbook/exercise5.168/plan/isolated_isAbsorbing_exercise]
  Exercise 5.168: an isolated mode is absorbing.
-/
theorem isolated_isAbsorbing_exercise (M : SystemMode Z₁ Z₂)
    (h : IsIsolatedMode M) : IsAbsorbingMode M :=
  isolated_isAbsorbing M h

/-! ## Exercise 5.169 — counterexample: constant input + non-primary ↛ constant time > 1 -/

lemma twoStateMode_constantInput : HasConstantInput twoStateModeWitness :=
  fun _ _ _ => rfl

lemma twoStateMode_not_primary : ¬ IsPrimaryMode twoStateModeWitness := by
  intro h
  have hdur := h.2 (1 : Fin 2) ()
  -- duration is `x.val + 1`, so at state 1 it equals 2, not 1
  change (1 : Fin 2).val + 1 = 1 at hdur
  simp at hdur

lemma twoStateMode_variableTime : HasVariableTimeIndex twoStateModeWitness := by
  intro ⟨d, hd⟩
  have h0 := hd.2 (0 : Fin 2) ()
  have h1 := hd.2 (1 : Fin 2) ()
  change (0 : Fin 2).val + 1 = d at h0
  change (1 : Fin 2).val + 1 = d at h1
  simp at h0 h1
  omega

/--
  [textbook/exercise5.169/source/exercise]
  [textbook/exercise5.169/plan/constantInput_nonprimary_not_implies_constantTime]
  Exercise 5.169 counterexample: constant input and non-primary need not imply
  constant time index greater than 1 (`twoStateModeWitness` has variable time).
-/
theorem constantInput_nonprimary_not_implies_constantTime :
    HasConstantInput twoStateModeWitness ∧
      ¬ IsPrimaryMode twoStateModeWitness ∧
      HasVariableTimeIndex twoStateModeWitness :=
  ⟨twoStateMode_constantInput, twoStateMode_not_primary, twoStateMode_variableTime⟩

open WymoreImplementation
open Homomorphism

/-! ## Exercise 5.170 — fixed-time sampled mode -/

/--
  [textbook/exercise5.170/source/exercise]
  [textbook/exercise5.170/plan/fixedTimeMode_constant_indices]
  Exercise 5.170: fixed-time `STZ(CNS_p,x)(s)` image is a constant-input mode of time `s`.
-/
theorem fixedTimeMode_constant_indices (Z : DiscreteSystem S₂ I₂ O₂)
    (S : Set S₂) (P : Set I₂) (s : Time) (hs : 0 < s)
    (hS : S.Nonempty) (hP : P.Nonempty)
    (hImageSubsetS : ∀ y, FixedTimeReachable Z S P s y → y ∈ S) :
    HasConstantInput (fixedTimeMode Z S P s hs hS hP hImageSubsetS) ∧
      HasConstantTimeIndex (fixedTimeMode Z S P s hs hS hP hImageSubsetS) s :=
  ⟨fixedTimeMode_constantInput Z S P s hs hS hP hImageSubsetS,
    fixedTimeMode_constantTime Z S P s hs hS hP hImageSubsetS⟩

/-! ## Exercise 5.171 — transient complement is absorbing -/

/--
  [textbook/exercise5.171/source/exercise]
  [textbook/exercise5.171/plan/transientComplement_isAbsorbing_exercise]
  Exercise 5.171: complement of a transient mode is absorbing.
-/
theorem transientComplement_isAbsorbing_exercise (M : SystemMode Z₁ Z₂)
    (h : IsTransientMode M) (hproper : IsProperMode M) :
    IsAbsorbingMode (transientComplementMode M h hproper) :=
  transientComplement_isAbsorbing M h hproper

/-! ## Exercise 5.172 — inevitable transitions admit alternate SMBFs -/

/--
  [textbook/exercise5.172/source/exercise]
  [textbook/exercise5.172/plan/inevitable_admits_alternate_SMBF_exercise]
  Exercise 5.172: under inevitable transitions, every alternate SMBF with the
  same durations and initial inputs still yields a system mode.
-/
theorem inevitable_admits_alternate_SMBF_exercise (M : SystemMode Z₁ Z₂)
    (hInev : HasInevitableTransitions M)
    (input' : S₁ → I₁ → ITZ I₂)
    (hinit : ∀ x p, input' x p 0 = M.inputMap p) :
    ∃ M' : SystemMode Z₁ Z₂,
      (∀ x p, M'.timeIndex x p = M.timeIndex x p) ∧
        (∀ x p, M'.inputIndex x p 0 = M.inputMap p) ∧
        M'.stateMap = M.stateMap :=
  inevitable_admits_alternate_SMBF M hInev input' hinit

/-! ## Exercise 5.173 — primary ⇒ constant output and inevitable -/

/--
  [textbook/exercise5.173/source/exercise]
  [textbook/exercise5.173/plan/primary_constOutput_inevitable_exercise]
  Exercise 5.173: primary modes have constant output and inevitable transitions.
-/
theorem primary_constOutput_inevitable_exercise (M : SystemMode Z₁ Z₂)
    (h : IsPrimaryMode M) :
    HasConstantOutput (primaryConstantInputMode M h) ∧
      HasInevitableTransitions M :=
  primary_hasConstantOutput_and_inevitable M h

/-! ## Exercise 5.174 — time elaboration implements -/

/--
  [textbook/exercise5.174/source/exercise]
  [textbook/exercise5.174/plan/timeElaborate_implements_exercise]
  Exercise 5.174: time elaboration yields a constant-input/time/output mode
  (CNS-inevitable) that implements the original system.
-/
theorem timeElaborate_implements_exercise (Z : DiscreteSystem S I O)
    (n : Nat) (hn : 1 < n) :
    HasConstantInput (timeElaborateMode Z n hn) ∧
      HasConstantTimeIndex (timeElaborateMode Z n hn) n ∧
      HasConstantOutput (timeElaborateMode Z n hn) ∧
      Nonempty (Implements Z (timeElaborate Z n hn)) :=
  ⟨timeElaborateMode_constantInput Z n hn,
    timeElaborateMode_constantTime Z n hn,
    timeElaborateMode_constantOutput Z n hn,
    ⟨timeElaborateImplements Z n hn⟩⟩

/-! ## Exercise 5.175 — primary mode reflexive -/

/--
  [textbook/exercise5.175/source/exercise]
  [textbook/exercise5.175/plan/primaryMode_reflexive_exercise]
  Exercise 5.175: the primary system-mode relation is reflexive.
-/
theorem primaryMode_reflexive_exercise (Z : DiscreteSystem S I O) :
    IsPrimaryMode (primarySelfMode Z) :=
  primaryMode_reflexive Z

/-! ## Exercise 5.176 — primary mode transitive -/

/--
  [textbook/exercise5.176/source/exercise]
  [textbook/exercise5.176/plan/primaryMode_transitive_exercise]
  Exercise 5.176: the primary system-mode relation is transitive.
-/
theorem primaryMode_transitive_exercise (M₁₂ : SystemMode Z₁ Z₂)
    (M₂₃ : SystemMode Z₂ Z₃) (h₁₂ : IsPrimaryMode M₁₂) (h₂₃ : IsPrimaryMode M₂₃) :
    IsPrimaryMode (M₁₂.trans M₂₃) :=
  primaryMode_transitive M₁₂ M₂₃ h₁₂ h₂₃

/-! ## Exercise 5.177 — Implements from mode / HIMSY / iso -/

/--
  [textbook/exercise5.177/source/exercise]
  [textbook/exercise5.177/plan/implements_of_mode_hom_iso_exercise]
  Exercise 5.177: mode, homomorphic image, or isomorphism each yields `Implements`.
-/
theorem implements_of_mode_hom_iso_exercise :
    (Nonempty (SystemMode Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) ∧
    (Nonempty (HomomorphicImageWitness Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) ∧
    (Nonempty (IsomorphismWitness Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) :=
  implements_of_mode_hom_iso_copy

/-! ## Exercise 5.178 — IIMPSY parameterization -/

/--
  [textbook/exercise5.178/source/exercise]
  [textbook/exercise5.178/plan/iimpsys_isSystemParameterization]
  Exercise 5.178: `IIMPSY` is a system parameterization.
-/
theorem iimpsys_isSystemParameterization {S I O : Type} (p : IimpsysParam S I O) :
    iimpsys S I O p = p.implemented :=
  iimpsys_eq p

/-! ## Exercise 5.179 — EIMPSY parameterization -/

/--
  [textbook/exercise5.179/source/exercise]
  [textbook/exercise5.179/plan/eimpsys_isSystemParameterization]
  Exercise 5.179: `EIMPSY` is a system parameterization (exact implementation;
  textbook once says “isomorphically”).
-/
theorem eimpsys_isSystemParameterization {S : Type} {Port OutPort : Type}
    {PV : Port → Type} {OV : OutPort → Type}
    (p : EimpsysParam S Port OutPort PV OV) :
    eimpsys S Port OutPort PV OV p = p.implemented :=
  eimpsys_eq p

end Mbse.TextbookExercises.Ch05
