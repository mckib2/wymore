import Mbse.WymorePropertyFragment
import Mbse.WymorePathologyExamples
import Mbse.FragmentPathologyRegistry
import Mbse.HomSoundness
import Mbse.PropertyFragmentSpec
import Mbse.SystemToFormula
import Mbse.GeneralProperties
import Mbse.GeneralPropertyFragment
import Mbse.TemporalLogic

/-!
# General Wymore property characterization (Tracks A, B, D)

Consolidates FO assertional soundness, impossibility results, partial-open fragment,
and predicate-indexed alternatives. Track C (LTS) lives in [`LTSCharacterization`](LTSCharacterization.lean).
-/

namespace WymoreCharacterization

open WymorePropertyFragment WymorePathologyExamples FragmentPathologyRegistry
  PropertyFragmentSpec PropertySemantics HomSoundness GeneralProperties
  SystemToFormula PropertyFragment.General PropertyFragment.FSM FSMProperties PathologyExamples
  TemporalLogic

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

theorem stageWymore_fo_soundness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (_hSide : FoAssertionalSideConditions Z_spec (w.HS s0) (projectedInput w.HI f))
    (hExec : IsWymoreExecution Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f)) :
    SystemSatisfiesFOAt Z_spec (w.HS s0) (projectedInput w.HI f) :=
  hom_implies_satisfies_specFO w s0 f hExec

theorem stageWymore_fo_execution_link {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesFO Z s0 f ↔
      IsWymoreExecution Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) :=
  stageWymore_fo_satisfies_iff_execution Z s0 f

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
  partial_adequate Z

theorem stageWymore_partial_readout_pathology :
    wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) ∧
      wymoreStay.RZ 0 = wymoreJump.RZ 0 := by
  refine ⟨wymoreStay_jump_different_step, ?_⟩
  simp [wymoreStay, wymoreJump, DiscreteSystem.ofTotal]

theorem stageWymore_partial_readout_only_blocked :
    SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
      SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
        wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) :=
  partial_readout_only_not_complete

theorem stageWymore_partial_identity_hom {Z_spec Z_impl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hDyn : SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  partial_identity_hom_via_pinned hSpec hImpl hDyn

theorem stageWymore_partial_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z_spec) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  partial_property_iff_hom hOut

theorem stageWymore_partial_verification {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hOut : AlwaysOutputs Z)
    (_hAdeq : PhiAdequatePartialOpen Z) :
    SystemSatisfiesPartialDynamics Z Z_impl ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl :=
  partial_synthesized_property_iff_hom hOut

theorem stageWymore_partial_soundness {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (_hOut : AlwaysOutputs Z_spec)
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamics Z_spec Z_impl :=
  partial_hom_implies_satisfies h

theorem stageWymore_partial_fragment_sideConditions {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    (Z : DiscreteSystem SZ IZ OZ) (h : PartialOpenSideConditions SZ IZ OZ Z) :
    partialOpenFragment.dynamicsComplete = true :=
  h.dynamicsComplete

theorem stageWymore_closed_excluded :
    ¬ AlwaysOutputs closedSystem :=
  closedSystem_not_alwaysOutputs

theorem stageWymore_partial_fragment :
    partialOpenFragment.dynamicsComplete = true :=
  partialOpen_dynamicsComplete

/-! ## BLOCKED registry exports -/

theorem stageWymore_blocked_infiniteSZ : ¬ RequiresFiniteStateEnumeration Nat :=
  blocked_infiniteSZ

theorem stageWymore_blocked_partialRZ :
    pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem :=
  blocked_partialRZ

theorem stageWymore_blocked_readoutOnly :
    readoutOnlyFragment.dynamicsComplete = false ∧
      (FSMSatisfiesOutputTable fsmJump fsmStay ∧
        FSMSatisfiesOutputTable fsmStay fsmJump ∧
          ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump) :=
  blocked_readoutOnly

theorem stageWymore_blocked_eventuallyF :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      (∀ t, traceNoQ.holds t StutterAtom.p) ∧
        (∀ t, traceWithQ.holds t StutterAtom.p) ∧
          traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
            ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) :=
  blocked_eventuallyF

theorem stageWymore_blocked_rawBranchingNZ :
    partialOpenFragment.dynamicsComplete = true ∧
      SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
        SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
          wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  refine ⟨partialOpen_dynamicsComplete, ?_⟩
  exact partial_readout_only_not_complete

/-! ## Fragment tier alignment -/

theorem stageWymore_pinnedFinite_tier :
    pinnedFiniteFragment = pinnedFragment :=
  pinnedFinite_eq_pinned

theorem stageWymore_fo_tier :
    foAssertionalFragment.finiteClauseEnumeration = false :=
  foAssertional_no_finite_enum

end WymoreCharacterization
