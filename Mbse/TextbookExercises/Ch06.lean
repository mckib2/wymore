import Mbse.WymoreRequirements
import Mbse.WymoreSystemModes

/-!
# Chapter 6 — input/output requirement exercises

Exercises 6.82, 6.86–6.91, 6.93–6.95, 6.97, 6.99, 6.101–6.103.
-/

namespace Mbse.TextbookExercises.Ch06

open WymoreRequirements
open WymoreSystemModes
open Homomorphism

/--
  [textbook/exercise6.82/source/exercise]
  [textbook/exercise6.82/plan/rsysmo_fsr_iff]
-/
theorem rsysmo_fsr_iff_exercise {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (IOR : InputOutputRequirement IR OR)
    (DSZ : S) (T : Set Time) :
    SatisfiesIOR Z IOR DSZ T ↔
      SatisfiesIOR (reachableModeSystem Z {DSZ} ⟨DSZ, Set.mem_singleton DSZ⟩)
        IOR ⟨DSZ, ⟨DSZ, Set.mem_singleton DSZ, reachable_self Z DSZ⟩⟩ T :=
  rsysmo_fsr_iff Z IOR DSZ T

/--
  [textbook/exercise6.86/source/exercise]
  [textbook/exercise6.86/plan/eligible_output_restriction_claim]
  Literal book claim (vacuous via `g1 = g2`); see also `extensions_agree_on_output`.
-/
theorem eligible_output_restriction_claim_exercise {S IR OR : Type}
    {Z : DiscreteSystem S IR OR} {IOR : InputOutputRequirement IR OR}
    {DSZ : S} {TSZ : Set Time}
    (h : SatisfiesIOR Z IOR DSZ TSZ) (f : ITZ IR) (hf : f ∈ IOR.itr)
    (h1 h2 : ITZ IR) (ha1 : agreesOn h1 f (TSR IOR)) (ha2 : agreesOn h2 f (TSR IOR)) :
    ∃ g1 ∈ IOR.er f, ∃ g2 ∈ IOR.er f, agreesOn g1 g2 TSZ :=
  eligible_output_restriction_claim h f hf h1 h2 ha1 ha2

/--
  [textbook/exercise6.87/source/exercise]
  [textbook/exercise6.87/plan/himio_himsy_reverse_claim]
-/
theorem himio_himsy_reverse_claim_exercise {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (hHIinj : Function.Injective w.HI) (hHOinj : Function.Injective w.HO)
    (DSZ2 : S2) (TSZ : Set Time)
    (hSat : SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ) :
    SatisfiesIOR Z2 IOR2 DSZ2 TSZ :=
  himio_himsy_reverse_claim IOR2 w hHIinj hHOinj DSZ2 TSZ hSat

/--
  [textbook/exercise6.88/source/exercise]
  [textbook/exercise6.88/plan/himsy_satisfies_himio]
-/
theorem himsy_satisfies_himio_exercise {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (DSZ2 : S2) (TSZ : Set Time)
    (hSat : SatisfiesIOR Z2 IOR2 DSZ2 TSZ) :
    SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ :=
  himsy_satisfies_himio IOR2 w DSZ2 TSZ hSat

/--
  [textbook/exercise6.89/source/exercise]
  [textbook/exercise6.89/plan/ior_iso_himsy_iff_claim]
-/
theorem ior_iso_himsy_iff_claim_exercise {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (hHIinj : Function.Injective w.HI) (hHOinj : Function.Injective w.HO)
    (DSZ2 : S2) (TSZ : Set Time) :
    SatisfiesIOR Z2 IOR2 DSZ2 TSZ ↔
      SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ :=
  ior_iso_himsy_iff_claim IOR2 w hHIinj hHOinj DSZ2 TSZ

/--
  [textbook/exercise6.90/source/exercise]
  [textbook/exercise6.90/plan/subreq_equal_itr_lifts_claim]
-/
theorem subreq_equal_itr_lifts_claim_exercise {S : Type}
    {Z : DiscreteSystem S Unit Bool} {DSZ : S} {TSZ : Set Time}
    (h : SatisfiesIOR Z tightIOR DSZ TSZ) :
    SatisfiesIOR Z looseIOR DSZ TSZ :=
  subreq_equal_itr_lifts_claim h

/--
  [textbook/exercise6.91/source/exercise]
  [textbook/exercise6.91/plan/canonical_subreq_claim]
-/
theorem canonical_subreq_claim_exercise {S IR OR : Type}
    {IOR1 IOR2 : InputOutputRequirement IR OR}
    {Z : DiscreteSystem S IR OR} {DSZ : S} {TSZ : Set Time}
    (hSub : IsIOSubrequirement IOR1 IOR2)
    (hTSR : TSR IOR1 = Set.univ) (hITR : IOR1.itr = IOR2.itr)
    (hEq : TSR IOR2 = Set.univ)
    (h : SatisfiesIOR Z IOR1 DSZ TSZ) :
    SatisfiesIOR Z IOR2 DSZ TSZ :=
  canonical_subreq_claim hSub hTSR hITR hEq h

/--
  [textbook/exercise6.93/source/exercise]
  [textbook/exercise6.93/plan/full_itr_fsr_nonempty_claim]
-/
theorem full_itr_fsr_nonempty_claim_exercise :
    (echoIOR.olr = .infinite ∧ echoIOR.itr = Set.univ) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S) (T : Set Time),
        SatisfiesIOR Z echoIOR x T :=
  full_itr_fsr_nonempty_claim

/--
  [textbook/exercise6.94/source/exercise]
  [textbook/exercise6.94/plan/full_itr_complete_or_empty_claim]
-/
theorem full_itr_complete_or_empty_claim_exercise :
    (delayedEchoIOR.olr = .infinite ∧ delayedEchoIOR.itr = Set.univ) ∧
      Nonempty (FSR delayedEchoIOR) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S),
        SatisfiesIORCompletely Z delayedEchoIOR x :=
  full_itr_complete_or_empty_claim

/--
  [textbook/exercise6.95/source/exercise]
  [textbook/exercise6.95/plan/incomplete_only_fsr_exists]
-/
theorem incomplete_only_fsr_exists_exercise :
    Nonempty (FSR delayedEchoIOR) ∧
      (∀ fsd : FSR delayedEchoIOR, fsd.TSZ ⊂ TSR delayedEchoIOR) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S),
        SatisfiesIORCompletely Z delayedEchoIOR x :=
  incomplete_only_fsr_exists

/--
  [textbook/exercise6.97/source/exercise]
  [textbook/exercise6.97/plan/tsy_family_eq_normio]
-/
theorem tsy_family_eq_normio_exercise {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hOut : AlwaysOutputs (tsy p)) :
    SatisfiesIORCompletely (tsy p)
      (normIO {
        Z := tsy p
        x := tsyInitial
        olr := p.IOR.olr
        F := p.IOR.itr
        F_nonempty := p.IOR.itr_nonempty
        hOut := hOut
      }) tsyInitial :=
  tsy_family_eq_normio p hOut

/--
  [textbook/exercise6.99/source/exercise]
  [textbook/exercise6.99/plan/normIO_satisfies_completely]
-/
theorem normIO_satisfies_completely_exercise (p : NormIOParam) :
    SatisfiesIORCompletely p.Z (normIO p) p.x :=
  normIO_satisfies_completely p

/--
  [textbook/exercise6.101/source/exercise]
  [textbook/exercise6.101/plan/fsr_closed_under_ts_subset]
-/
def fsr_closed_under_ts_subset_exercise {IR OR : Type} {IOR : InputOutputRequirement IR OR}
    (fsd : FSR IOR) {T : Set Time} (hT : T.Nonempty) (hsub : T ⊆ fsd.TSZ) :
    FSR IOR :=
  fsr_closed_under_ts_subset fsd hT hsub

/--
  [textbook/exercise6.102/source/exercise]
  [textbook/exercise6.102/plan/tsy_isSystemParameterization]
-/
theorem tsy_isSystemParameterization_exercise {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) :
    tsyParameterization IR OR p = tsy p :=
  tsy_isSystemParameterization p

/--
  [textbook/exercise6.103/source/exercise]
  [textbook/exercise6.103/plan/tsy_trajectory_characterization]
-/
theorem tsy_trajectory_characterization_exercise {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hInf : TSR p.IOR = Set.univ) (f : ITZ IR) (hf : f ∈ p.IOR.itr) :
    (∀ t, generateStateTrajectory (tsy p) tsyInitial (liftInput f) t = tsyPrefix f t) ∧
    (∀ t, generateOutputTrajectory (tsy p) tsyInitial (liftInput f) t =
      some ((p.cho.pick (p.IOR.er (p.chi.pick
        (if t = 0 then p.IOR.itr else compatibleInputs p.IOR.itr (tsyPrefix f t))))) t)) :=
  tsy_trajectory_characterization p hInf f hf

end Mbse.TextbookExercises.Ch06
