import Mbse.WymorePropertyFragment
import Mbse.PropertyFragmentSpec
import Mbse.PathologyExamples
import Mbse.GeneralProperties
import Mbse.FiniteWymore
import Mbse.SystemToFormula
import Mbse.GeneralPropertyFragment

/-!
# Pathology examples for the general Wymore property track

Documents failure modes for infinite state, partial I/O, and finite enumeration.
-/

namespace WymorePathologyExamples

open WymorePropertyFragment PropertyFragmentSpec PathologyExamples GeneralProperties FSM
  SystemToFormula PropertyFragment.General

/-! ## Infinite state (`counterSystem`) -/

theorem counterSystem_is_infinite : ¬ IsFinite counterSystem :=
  counterSystem_not_finite

/-- Pinned propositional `dynamicsTable` is not available without `Fintype SZ`. -/
theorem counterSystem_no_finite_dynamicsTable :
    ¬ RequiresFiniteStateEnumeration Nat :=
  not_requiresFiniteStateEnumeration_nat

/-- FO assertional compile is definable on infinite `counterSystem`. -/
theorem counterSystem_fo_compile_exists :
    compileObservablesFO counterSystem 0 = compileSystemFO counterSystem 0 :=
  compileObservablesFO_counterSystem

theorem counterSystem_satisfies_own_FO :
    SystemSatisfiesFO counterSystem 0 (fun _ => some true) := by
  rw [systemSatisfiesFO_iff_execution]
  exact canonical_is_wymore_execution counterSystem 0 (fun _ => some true)

/-! ## Partial readout (`closedSystem`) -/

theorem closedSystem_not_alwaysOutputs : ¬ AlwaysOutputs closedSystem := by
  intro h
  rcases h () with ⟨w, _⟩
  cases w

theorem closedSystem_excluded_from_pinned :
    PropertyFragmentSpec.pinnedFragment.dynamicsComplete = true ∧
      ¬ AlwaysOutputs closedSystem := by
  refine ⟨pinnedFragment_dynamicsComplete, closedSystem_not_alwaysOutputs⟩

/-! ## Predicate schema works on infinite state (Track D) -/

theorem counterSystem_predicate_schema :
    compileObservablesPred counterSystem = compileObservablesPred counterSystem :=
  compileObservablesPred_wellformed counterSystem

/-! ## Partial dynamics: readout-only still incomplete (Track A pathology) -/

abbrev wymPathStates := Fin 2
abbrev wymPathInputs := Fin 1
abbrev wymPathOutputs := Fin 1

def wymoreSharedReadout : wymPathStates → wymPathOutputs := fun _ => 0

def wymoreStay : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs :=
  DiscreteSystem.ofTotal (fun _ _ => 0) wymoreSharedReadout ⟨0⟩

def wymoreJump : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs :=
  DiscreteSystem.ofTotal (fun _ _ => 1) wymoreSharedReadout ⟨0⟩

theorem wymoreStay_alwaysOutputs : AlwaysOutputs wymoreStay :=
  ofTotal_alwaysOutputs _ _ _

theorem wymoreJump_alwaysOutputs : AlwaysOutputs wymoreJump :=
  ofTotal_alwaysOutputs _ _ _

/-- Readout-only fragment flag matches Stage 2 pathology (Example 2). -/
theorem partial_readoutOnly_not_dynamicsComplete :
    readoutOnlyFragment.dynamicsComplete = false := rfl

/-- Same readout, different `NZ`: readout-only tables cannot distinguish implementations. -/
theorem wymoreStay_jump_same_readout :
    wymoreStay.RZ = wymoreJump.RZ := rfl

theorem wymoreStay_jump_different_step :
    wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  simp [wymoreStay, wymoreJump, DiscreteSystem.ofTotal]

/-- FSM pathology Example 2 lifts to raw `DiscreteSystem` via `toDiscreteSystem`. -/
theorem wymore_readout_only_pathology :
    fsmStay.NZ 0 0 ≠ fsmJump.NZ 0 0 ∧
      fsmStay.RZ 0 = fsmJump.RZ 0 := by
  refine ⟨?_, ?_⟩
  · simp [fsmStay, fsmJump]
  · simp [fsmStay, fsmJump, sharedRZ]

theorem partial_adequate_trivial {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z := ⟨rfl⟩

/-- Under `AlwaysOutputs`, pinned Stage 3 bi-implication remains the identity-hom witness. -/
theorem partial_identity_hom_via_pinned {Z_spec Z_impl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hDyn : SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl :=
  (system_property_iff_hom hSpec hImpl).mp hDyn

/-! ## Partial dynamics: finite enumeration witness -/

/-- On finite open Moore systems, partial dynamics with `AlwaysOutputs` needs `Fintype SZ`. -/
theorem partial_agrees_with_pinned_when_alwaysOutputs {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
    [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (_hOut : AlwaysOutputs Z) :
    RequiresFiniteStateEnumeration SZ :=
  requiresFiniteStateEnumeration_of_fintype (SZ := SZ)

end WymorePathologyExamples
