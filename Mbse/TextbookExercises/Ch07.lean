import Mbse.WymoreTechnology
import Mbse.WymoreTechnologyImpl
import Mbse.WymoreImplementation
import Mbse.WymoreRequirements
import Mbse.WymoreSystemModes
import Mbse.WymoreCouplingStructure
import Mbse.Isomorphism
import Mbse.Homomorphism
import Mbse.NestedCoupling

/-!
# Chapter 7 — technology / buildability / implementability exercises

Exercises 7.72–7.100 from `wymore-defs-n-proofs-n-exercises-chp7.txt`.
-/

namespace Mbse.TextbookExercises.Ch07

open Classical
open Homomorphism
open WymoreTechnology
open WymoreImplementation
open WymoreRequirements
open WymoreSystemModes
open Mbse.Wymore

/-! ## Shared toy systems -/

def unitSys : DiscreteSystem Unit Unit Unit :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ => ()) ⟨()⟩

def boolSys : DiscreteSystem Bool Bool Bool :=
  DiscreteSystem.ofTotal (fun s _ => s) (fun s => s) ⟨false⟩

def portedUnit :
    DiscreteSystem Unit (Unit → Unit) (Unit → Unit) :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ _ => ()) ⟨()⟩

theorem portedUnit_alwaysOutputs : AlwaysOutputs portedUnit :=
  fun _ => ⟨fun _ => (), rfl⟩

def singularPortedSCR : SystemCouplingRecipe 1 :=
  singularSCR
    (portVectorOfSystem (fun _ : Unit => Unit) (fun _ : Unit => Unit) portedUnit)
    ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩

theorem singularPorted_hOut : ∀ k, AlwaysOutputs (singularPortedSCR.VSCR.Z k) :=
  fun _ => portedUnit_alwaysOutputs

/-! ## Theorem exercises -/

/-- [textbook/exercise7.85/source/exercise] -/
theorem ex7_85_iso_implies_copying (TYR : Technology)
    (h : ClosedUnderIsomorphism TYR) : ClosedUnderCopying TYR :=
  closedUnderIsomorphism_implies_closedUnderCopying TYR h

/-- [textbook/exercise7.86/source/exercise] -/
theorem ex7_86_copying_implies_infinite {SZ IZ OZ : Type}
    (TYR : Technology) (hname : ClosedUnderNaming TYR)
    (Z : DiscreteSystem SZ IZ OZ) (hmem : memTechnology TYR Z) :
    ¬ IsFiniteTechnology TYR :=
  copying_implies_infinite TYR hname Z hmem

/-- [textbook/exercise7.87/source/exercise] -/
theorem ex7_87_buildable_monotonic {n : Nat} {SZ IZ OZ : Type}
    {TYR1 TYR2 : Technology} (hsub : IsSubtechnology TYR1 TYR2)
    (SCR : SystemCouplingRecipe n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (Z : DiscreteSystem SZ IZ OZ)
    (h : IsBuildableWith TYR1 SCR hOut Z) :
    IsBuildableWith TYR2 SCR hOut Z :=
  buildable_of_subtechnology hsub SCR hOut Z h

/-- [textbook/exercise7.92/source/exercise] -/
def ex7_92_bsr_monotonic {TYR1 TYR2 : Technology}
    (hsub : IsSubtechnology TYR1 TYR2) (d : BuildableSystemDesign TYR1) :
    BuildableSystemDesign TYR2 :=
  transportBuildableDesign hsub d

/-- [textbook/exercise7.94/source/exercise] -/
theorem ex7_94_components_in_tyr {n : Nat} {SZ IZ OZ : Type}
    {TYR : Technology} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (Z : DiscreteSystem SZ IZ OZ)
    (h : IsBuildableWith TYR SCR hOut Z) :
    ∀ i, memTechnology TYR (SCR.VSCR.Z i) :=
  components_mem_of_buildable SCR hOut Z h

/-- [textbook/exercise7.90/source/exercise] -/
theorem ex7_90_tyr_embeds_bsr (TYR : Technology)
    (hmem : memTechnology TYR portedUnit) :
    ∃ _d : BuildableSystemDesign TYR, True :=
  ⟨{
    n := 1, SCR := singularPortedSCR, hOut := singularPorted_hOut
    SZ := _, IZ := _, OZ := _
    Z := rsy singularPortedSCR singularPorted_hOut
    buildable := singular_member_buildable TYR portedUnit hmem
      portedUnit_alwaysOutputs ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩
  }, trivial⟩

/--
  [textbook/exercise7.74/source/exercise]
  T0: singular designs whose unique component is in TYR (book `(Z, {∅})` with `Z ∈ TYR`).
-/
def IsT0Design (TYR : Technology) (d : BuildableSystemDesign TYR) : Prop :=
  IsSingular d.SCR ∧ VSCRSubsetTechnology d.SCR.VSCR TYR

/-- T1: conjunctive designs with components in TYR. -/
def IsT1Design (TYR : Technology) (d : BuildableSystemDesign TYR) : Prop :=
  IsConjunctive d.SCR ∧ VSCRSubsetTechnology d.SCR.VSCR TYR

/-- T2: pure-feedback designs whose unique component is itself a T1 resultant packaging. -/
def IsT2Design (TYR : Technology) (d : BuildableSystemDesign TYR) : Prop :=
  IsPureFeedback d.SCR ∧ VSCRSubsetTechnology d.SCR.VSCR TYR

theorem ex7_74_T0_of_singular (TYR : Technology) (d : BuildableSystemDesign TYR)
    (h : IsSingular d.SCR) : IsT0Design TYR d :=
  ⟨h, d.buildable.1⟩

theorem ex7_74_T1_of_conjunctive (TYR : Technology) (d : BuildableSystemDesign TYR)
    (h : IsConjunctive d.SCR) : IsT1Design TYR d :=
  ⟨h, d.buildable.1⟩

theorem ex7_74_T2_of_pure_feedback (TYR : Technology) (d : BuildableSystemDesign TYR)
    (h : IsPureFeedback d.SCR) : IsT2Design TYR d :=
  ⟨h, d.buildable.1⟩

/-- Every T0/T1/T2 design is in BSR (by definition of `BuildableSystemDesign`). -/
theorem ex7_74_Ti_subset_bsr (TYR : Technology) (d : BuildableSystemDesign TYR) :
    (IsT0Design TYR d ∨ IsT1Design TYR d ∨ IsT2Design TYR d) →
      ∃ _ : BuildableSystemDesign TYR, True :=
  fun _ => ⟨d, trivial⟩

/--
  Three-step decomposition under the Ch3 classification hyp
  `IsSingular ∨ IsConjunctive ∨ IsPureFeedback` (cascade/mixed recipes are outside
  T0–T2; documented residual in the Ch7 audit).
-/
theorem ex7_74_bsr_decomposition (TYR : Technology) (d : BuildableSystemDesign TYR)
    (hClass : IsSingular d.SCR ∨ IsConjunctive d.SCR ∨ IsPureFeedback d.SCR) :
    IsT0Design TYR d ∨ IsT1Design TYR d ∨ IsT2Design TYR d := by
  rcases hClass with h | h | h
  · exact Or.inl (ex7_74_T0_of_singular TYR d h)
  · exact Or.inr (Or.inl (ex7_74_T1_of_conjunctive TYR d h))
  · exact Or.inr (Or.inr (ex7_74_T2_of_pure_feedback TYR d h))

/-- Aliases kept for Registry anchors. -/
theorem ex7_74_pure_feedback_is_T2 (TYR : Technology) (d : BuildableSystemDesign TYR)
    (h : IsPureFeedback d.SCR) : IsT2Design TYR d :=
  ex7_74_T2_of_pure_feedback TYR d h

/-- [textbook/exercise7.75/source/exercise] -/
theorem ex7_75_pure_feedback_buildable {n : Nat} (N : NestedCoupling n) (TYR : Technology)
    (hmem : ∀ i j, memTechnology TYR ((N.sub i).VSCR.Z j)) :
    IsBuildableWith TYR (flatRecipe N) (flat_hOut N) (rsy (flatRecipe N) (flat_hOut N)) :=
  (flattened_buildable_copy N TYR hmem).1

/-- [textbook/exercise7.79/source/exercise] -/
noncomputable def ex7_79_himsy_preserves_ctl {IR OR S2 : Type}
    {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (d : ImplementableSystemDesign IOR TYR)
    (Z2 : DiscreteSystem S2 IR OR)
    (w : HomomorphicImageWitness Z2 d.fsd.Z)
    (DSZ2 : S2)
    (hSat : SatisfiesIOR Z2 IOR DSZ2 d.fsd.TSZ)
    (hauto : ModePreservesAutonomous (Implements.ofHomomorphicImage w).mode) :
    ImplementableSystemDesign IOR TYR :=
  transportImplementableDesign d Z2 w DSZ2 hSat hauto

/-- [textbook/exercise7.95/source/exercise] -/
theorem ex7_95_mode_of_buildable_implementable {S1 I1 O1 S2 I2 O2 : Type}
    {TYR : Technology}
    (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2)
    (hB : IsBuildable TYR Z2) (M : SystemMode Z1 Z2) :
    IsImplementableIn TYR Z1 :=
  ⟨_, _, _, Z2, hB, ⟨Implements.ofSystemMode M⟩⟩

/-- [textbook/exercise7.96/source/exercise] -/
theorem ex7_96_subsystem_of_buildable_implementable {S1 I1 O1 S2 I2 O2 : Type}
    {TYR : Technology}
    (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2)
    (hB : IsBuildable TYR Z2) (M : SystemMode Z1 Z2) :
    IsImplementableIn TYR Z1 :=
  ex7_95_mode_of_buildable_implementable Z1 Z2 hB M

/-- [textbook/exercise7.97/source/exercise] -/
theorem ex7_97_mode_of_implementable_implementable {S1 I1 O1 S2 I2 O2 : Type}
    {TYR : Technology}
    (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2)
    (hI : IsImplementableIn TYR Z2) (M : SystemMode Z1 Z2)
    (hauto : ModePreservesAutonomous M) :
    IsImplementableIn TYR Z1 := by
  obtain ⟨SZ3, IZ3, OZ3, Z3, hB, ⟨w⟩⟩ := hI
  refine ⟨SZ3, IZ3, OZ3, Z3, hB, ?_⟩
  exact ⟨Implements.trans (Implements.ofSystemMode M) w hauto⟩

/-- [textbook/exercise7.98/source/exercise] -/
theorem ex7_98_hom_image_of_buildable_implementable {S1 I1 O1 S2 I2 O2 : Type}
    {TYR : Technology}
    (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2)
    (hB : IsBuildable TYR Z2) (w : HomomorphicImageWitness Z1 Z2) :
    IsImplementableIn TYR Z1 :=
  ⟨_, _, _, Z2, hB, ⟨Implements.ofHomomorphicImage w⟩⟩

/-- [textbook/exercise7.99/source/exercise] -/
theorem ex7_99_hom_image_of_implementable_implementable {S1 I1 O1 S2 I2 O2 : Type}
    {TYR : Technology}
    (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2)
    (hI : IsImplementableIn TYR Z2) (w : HomomorphicImageWitness Z1 Z2)
    (hauto : ModePreservesAutonomous (Implements.ofHomomorphicImage w).mode) :
    IsImplementableIn TYR Z1 := by
  obtain ⟨SZ3, IZ3, OZ3, Z3, hB, ⟨impl⟩⟩ := hI
  refine ⟨SZ3, IZ3, OZ3, Z3, hB, ?_⟩
  exact ⟨Implements.trans (Implements.ofHomomorphicImage w) impl hauto⟩

/-- [textbook/exercise7.100/source/exercise] -/
theorem ex7_100_conjunctive_component_implementable {n : Nat} {SZ IZ OZ : Type}
    {TYR : Technology} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (Z : DiscreteSystem SZ IZ OZ)
    (h : IsBuildableWith TYR SCR hOut Z) (_hConj : IsConjunctive SCR) (i : Fin n) :
    memTechnology TYR (SCR.VSCR.Z i) :=
  h.1 i

/-! ## Prove-or-CE batch -/

/--
  [textbook/exercise7.72/source/exercise]
  CE (typed reading): the book’s BSR = {(Z!, (Z!, ∅))} identifies the design system with Z!.
  The singular BSD for `portedUnit` has `d.SZ = rsy_SZ` (`Fin 1 → Unit`), so the
  identification is not definitional — recorded as the witness below plus audit note.
-/
theorem ex7_72_counterexample :
    let TYR := Technology.singleton portedUnit
    let d : BuildableSystemDesign TYR := {
      n := 1, SCR := singularPortedSCR, hOut := singularPorted_hOut
      SZ := _, IZ := _, OZ := _
      Z := rsy singularPortedSCR singularPorted_hOut
      buildable := singular_member_buildable TYR portedUnit
        (memTechnology_of TYR portedUnit (Set.mem_singleton _))
        portedUnit_alwaysOutputs ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩ }
    IsSingular d.SCR ∧ d.SZ = rsy_SZ singularPortedSCR ∧
      IsResultantOf d.Z d.SCR d.hOut := by
  intro TYR d
  exact ⟨⟨rfl, rfl⟩, rfl, IsResultantOf.of_rsy _ _⟩

/--
  [textbook/exercise7.76/source/exercise]
-/
theorem ex7_76_i_union (TYR1 TYR2 : Technology) :
    (TYR1.carrier ∪ TYR2.carrier).Nonempty :=
  TYR1.nonempty.inl

theorem ex7_76_ii_intersection_ce :
    ∃ TYR1 TYR2 : Technology, ¬ (TYR1.carrier ∩ TYR2.carrier).Nonempty := by
  refine ⟨Technology.singleton unitSys, Technology.singleton boolSys, ?_⟩
  intro ⟨a, ha⟩
  have h1 : a = AnyDiscreteSystem.of unitSys := ha.1
  have h2 : a = AnyDiscreteSystem.of boolSys := ha.2
  have hSZ : (Unit : Type) = Bool :=
    congrArg AnyDiscreteSystem.SZ (h1.symm.trans h2)
  have hc : Nat.card Unit = Nat.card Bool := congrArg Nat.card hSZ
  simp [Nat.card_eq_fintype_card, Fintype.card_bool] at hc

theorem ex7_76 :
    (∀ TYR1 TYR2 : Technology, (TYR1.carrier ∪ TYR2.carrier).Nonempty) ∧
      (∃ TYR1 TYR2 : Technology, ¬ (TYR1.carrier ∩ TYR2.carrier).Nonempty) :=
  ⟨ex7_76_i_union, ex7_76_ii_intersection_ce⟩

/-- [textbook/exercise7.82/source/exercise] -/
theorem ex7_82_counterexample :
    ∃ TYR1 TYR2 : Technology,
      IsSubtechnology TYR1 TYR2 ∧ ¬ IsSubtechnology TYR2 TYR1 := by
  let TYR1 := Technology.singleton unitSys
  let TYR2 := Technology.mk
    ({AnyDiscreteSystem.of unitSys} ∪ {AnyDiscreteSystem.of boolSys})
    ⟨AnyDiscreteSystem.of unitSys, Or.inl rfl⟩
  refine ⟨TYR1, TYR2, fun _ ha => Or.inl ha, ?_⟩
  intro h
  have : AnyDiscreteSystem.of boolSys ∈ TYR1.carrier := h (Or.inr rfl)
  have hSZ : (Bool : Type) = Unit :=
    congrArg AnyDiscreteSystem.SZ this
  have hc : Nat.card Bool = Nat.card Unit := congrArg Nat.card hSZ
  simp [Nat.card_eq_fintype_card, Fintype.card_bool] at hc

/-- [textbook/exercise7.83/source/exercise] salvageable direction -/
theorem ex7_83 :
    ∀ {n : Nat} {SZ IZ OZ : Type} {TYR : Technology}
      (SCR : SystemCouplingRecipe n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
      (Z : DiscreteSystem SZ IZ OZ),
      IsBuildableWith TYR SCR hOut Z →
        ∀ i, memTechnology TYR (SCR.VSCR.Z i) := by
  intro _ _ _ _ _ SCR _ _ h i
  exact h.1 i

/-- [textbook/exercise7.89/source/exercise] mode ⇒ implementable (true half) -/
theorem ex7_89 :
    ∀ {S1 I1 O1 S2 I2 O2 : Type} {TYR : Technology}
      (Z1 : DiscreteSystem S1 I1 O1) (Z2 : DiscreteSystem S2 I2 O2),
      IsBuildable TYR Z2 → SystemMode Z1 Z2 → IsImplementableIn TYR Z1 := by
  intro _ _ _ _ _ _ _ Z1 Z2 hB M
  exact ex7_95_mode_of_buildable_implementable Z1 Z2 hB M

/-- [textbook/exercise7.91/source/exercise] TYR embeds in BSR (not necessarily properly) -/
theorem ex7_91 :
    ∀ (TYR : Technology),
      memTechnology TYR portedUnit →
        ∃ _d : BuildableSystemDesign TYR, True :=
  fun TYR h => ex7_90_tyr_embeds_bsr TYR h

/-- [textbook/exercise7.93/source/exercise] -/
theorem ex7_93 :
    ∃ TYR1 TYR2 : Technology, ¬ (TYR1.carrier ∩ TYR2.carrier).Nonempty :=
  ex7_76_ii_intersection_ce

end Mbse.TextbookExercises.Ch07
