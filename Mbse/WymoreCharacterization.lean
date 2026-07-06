import Mbse.WymorePropertyFragment
import Mbse.WymorePathologyExamples
import Mbse.LTSWymore
import Mbse.HomSoundness
import Mbse.PropertyFragmentSpec
import Mbse.SystemToFormula
import Mbse.GeneralProperties
import Mbse.GeneralPropertyFragment

/-!
# General Wymore property characterization (Tracks A–D)

Consolidates FO assertional soundness, impossibility results, partial fragment,
LTS refinement, and predicate-indexed alternatives.
-/

namespace WymoreCharacterization

open WymorePropertyFragment WymorePathologyExamples PropertyFragmentSpec
  PropertySemantics HomSoundness LTS LTS.Examples GeneralProperties
  SystemToFormula PropertyFragment.General

/-! ## Track B: FO assertional -/

theorem stageWymore_fo_compile {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    compileObservablesFO Z s0 = compileSystemFO Z s0 :=
  compileObservablesFO_definable Z s0

theorem stageWymore_fo_satisfies_iff_execution {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesFO Z s0 f ↔
      IsWymoreExecution Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) :=
  systemSatisfiesFO_iff_execution Z s0 f

theorem stageWymore_fo_assertional_compile {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    compileObservablesAssertionalFO Z s0 = compileAssertionalFO Z s0 := rfl

theorem stageWymore_fo_verification {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    SystemSatisfiesFOAt Z_spec (w.HS s0) (projectedInput w.HI f) :=
  hom_implies_satisfies_specFO w s0 f hExec

theorem stageWymore_counterSystem_fo :
    SystemSatisfiesFO counterSystem 0 (fun _ => some true) :=
  counterSystem_satisfies_own_FO

/-! ## Track B/D: infinite state impossibility -/

theorem stageWymore_infinite_no_finite_enum :
    ¬ RequiresFiniteStateEnumeration Nat :=
  counterSystem_no_finite_dynamicsTable

theorem stageWymore_predicate_schema {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesPred Z = compileObservablesPred Z :=
  compileObservablesPred_wellformed Z

/-! ## Track A: partial open -/

theorem stageWymore_partial_adequate {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z :=
  partial_adequate_trivial Z

theorem stageWymore_partial_readout_pathology :
    wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) ∧
      wymoreStay.RZ 0 = wymoreJump.RZ 0 := by
  refine ⟨wymoreStay_jump_different_step, ?_⟩
  simp [wymoreStay, wymoreJump, DiscreteSystem.ofTotal]

theorem stageWymore_partial_identity_hom {Z_spec Z_impl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hDyn : SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  partial_identity_hom_via_pinned hSpec hImpl hDyn

theorem stageWymore_closed_excluded :
    ¬ AlwaysOutputs closedSystem :=
  closedSystem_not_alwaysOutputs

theorem stageWymore_partial_fragment :
    partialOpenFragment.dynamicsComplete = true :=
  partialOpen_dynamicsComplete

/-! ## Track C: LTS refinement -/

theorem stageWymore_lts_refinement_sound {S Act SZ IZ OZ : Type}
    (L : LabeledTransitionSystem S Act) (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (R : WymoreRefinement S Act L SZ IZ OZ Z s0) :
    TraceRefines L Z s0 R.interp :=
  wymoreRefinement_traceRefines L Z s0 R

theorem stageWymore_lts_trivial_refines {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (hOut : AlwaysOutputs Z) :
    TraceRefines (trivialSpec IZ OZ) Z s0 (@identityInterp IZ OZ) :=
  trivial_refinement Z s0 hOut

theorem stageWymore_lts_nondet_obstruction (s0 : Bool) :
    ¬ TraceRefines forbidSpec toggleSystem s0 unitInterp :=
  toggle_not_refines_forbid s0

theorem stageWymore_lts_fragment :
    ltsRefinementFragment.finiteClauseEnumeration = false :=
  foAssertional_no_finite_enum

/-! ## Fragment tier alignment -/

theorem stageWymore_pinnedFinite_tier :
    pinnedFiniteFragment = pinnedFragment :=
  pinnedFinite_eq_pinned

theorem stageWymore_fo_tier :
    foAssertionalFragment.finiteClauseEnumeration = false :=
  foAssertional_no_finite_enum

end WymoreCharacterization
