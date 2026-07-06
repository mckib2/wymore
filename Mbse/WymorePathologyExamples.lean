import Mbse.WymorePropertyFragment
import Mbse.PropertyFragmentSpec
import Mbse.PathologyExamples
import Mbse.GeneralProperties
import Mbse.FSMProperties
import Mbse.FiniteWymore
import Mbse.SystemToFormula
import Mbse.GeneralPropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.Homomorphism
import Mbse.SpecFromProperties
import Mbse.HimsySynthesis

/-!
# Pathology examples for the general Wymore property track

Documents failure modes for infinite state, partial I/O, and finite enumeration.
-/

namespace WymorePathologyExamples

open WymorePropertyFragment PropertyFragmentSpec PathologyExamples GeneralProperties FSM
  SystemToFormula FOLTL PropertyFragment.General PropertyFragment.FSM
  ExtensionalDynamicsFragment Homomorphism SpecFromProperties HimsySynthesis GeneralFSMBridge
  FSMProperties

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

/-- Extensional Φ is reflexively satisfied on infinite `counterSystem`. -/
theorem counterSystem_satisfies_own_extensional :
    SystemSatisfiesExtensional counterSystem counterSystem counterSystem_alwaysOutputs
      counterSystem_alwaysOutputs :=
  extensional_satisfies_reflexive counterSystem counterSystem_alwaysOutputs

theorem counterSystem_satisfies_assertionalFO :
    SystemSatisfiesSpecAssertionalFOAt counterSystem counterSystem 0 (fun _ => some true) :=
  (assertionalFO_at_iff_extensional counterSystem_alwaysOutputs counterSystem_alwaysOutputs 0
    (fun _ => some true)).2 counterSystem_satisfies_own_extensional

/-- Extensional Φ ↔ identity hom on infinite `counterSystem` (same-type witness). -/
theorem counterSystem_extensional_iff_hom :
    SystemSatisfiesExtensional counterSystem counterSystem counterSystem_alwaysOutputs
      counterSystem_alwaysOutputs ↔
      SystemIsIdentityHomomorphicImageOpen counterSystem counterSystem
        counterSystem_alwaysOutputs counterSystem_alwaysOutputs :=
  extensional_property_iff_hom counterSystem_alwaysOutputs counterSystem_alwaysOutputs

/-! ## Cross-type extensional (`counterElab` → `counterSystem`) -/

/-- Elaboration with redundant `Bool` state component; `fst` projects to `counterSystem`. -/
def counterElab : DiscreteSystem (Nat × Bool) Bool Nat :=
  DiscreteSystem.ofTotal (fun (n, b) (_ : Bool) => (n + 1, b)) (fun (n, _) => n) ⟨(0, true)⟩

theorem counterElab_alwaysOutputs : AlwaysOutputs counterElab :=
  ofTotal_alwaysOutputs _ _ _

def counterElab_witness : HomomorphicImageWitness counterSystem counterElab where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun n => ⟨⟨n, true⟩, rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun ⟨n, b⟩ oi => by
    cases oi with
    | none => simp [counterElab, counterSystem, DiscreteSystem.ofTotal]
    | some i => simp [counterElab, counterSystem, DiscreteSystem.ofTotal]
  preserves_readout := fun ⟨n, b⟩ => by
    simp [counterElab, counterSystem, DiscreteSystem.ofTotal, Option.map_some]

theorem counterElab_hom_to_counterSystem :
    IsHomomorphicImage counterSystem counterElab :=
  ⟨counterElab_witness⟩

theorem counterElab_satisfies_extensional_cross :
    SystemSatisfiesExtensionalCross counterSystem counterElab :=
  extensional_cross_of_hom counterElab_hom_to_counterSystem

theorem counterElab_cross_iff_hom :
    SystemSatisfiesExtensionalCross counterSystem counterElab ↔
      IsHomomorphicImage counterSystem counterElab :=
  extensional_cross_property_iff_hom

/-! ## Extensional synthesis + PhiAdequate witnesses -/

theorem counterSystem_phi_adequate_cross :
    PhiAdequateExtensionalCross counterSystem :=
  extensional_phi_adequate_cross counterSystem

theorem counterSystem_phi_adequate_open :
    PhiAdequateExtensionalOpen counterSystem counterSystem_alwaysOutputs :=
  extensional_phi_adequate_open counterSystem counterSystem_alwaysOutputs

theorem counterSystem_synthesized_cross_iff_hom :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ↔
      IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab :=
  extensional_synthesized_cross_iff_hom

theorem counterElab_synthesized_hom :
    IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab :=
  (extensional_synthesized_cross_iff_hom (Z := counterSystem) (Z_impl := counterElab)).mp
    counterElab_satisfies_extensional_cross

theorem counterSystem_self_synthesizable :
    IsSynthesizableExtensional counterSystem counterSystem_alwaysOutputs :=
  extensional_self_synthesizable counterSystem counterSystem_alwaysOutputs

/-! ## HIMSY synthesis witness -/

theorem counterSystem_eq_himsy_counterElab :
    HimsySpecEqual counterSystem (synthesizeHimsySpec counterElab_witness) :=
  synthesizeHimsySpec_eq_spec counterElab_witness

theorem counterSystem_himsy_phi_adequate :
    PhiAdequateHimsy counterElab_witness :=
  himsy_phi_adequate_of_witness counterElab_witness

/-! ## Inverse table recovery witness (finite pinned) -/

theorem fsmStay_recoverable_table :
    IsRecoverableExtensionalTable
      (dynamicsTable fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay))
      fsmStay.toDiscreteSystem (fsm_alwaysOutputs fsmStay) :=
  isRecoverableExtensionalTable_of _ _ _ (fsm_table_synthesizable fsmStay)

/-! ## Partial readout (`closedSystem`) -/

theorem closedSystem_not_alwaysOutputs : ¬ AlwaysOutputs closedSystem := by
  intro h
  rcases h () with ⟨w, _⟩
  cases w

theorem closedSystem_excluded_from_pinned :
    PropertyFragmentSpec.pinnedFragment.dynamicsComplete = true ∧
      ¬ AlwaysOutputs closedSystem := by
  refine ⟨pinnedFragment_dynamicsComplete, closedSystem_not_alwaysOutputs⟩

/-! ## Predicate schema works on infinite state -/

theorem counterSystem_predicate_schema :
    compileObservablesPred counterSystem = compileObservablesPartialOpen counterSystem :=
  compileObservablesPred_eq_partialOpen counterSystem

/-! ## Partial dynamics: readout-only still incomplete -/

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

theorem partial_adequate {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    PartialDynamicsAdequate Z :=
  partialDynamicsAdequate_of Z

theorem partial_readout_only_not_complete :
    SystemSatisfiesPartialReadoutOnly wymoreJump wymoreStay ∧
      SystemSatisfiesPartialReadoutOnly wymoreStay wymoreJump ∧
      wymoreStay.NZ 0 (some 0) ≠ wymoreJump.NZ 0 (some 0) := by
  have hcross := partial_readoutOnly_satisfies_cross (Z_spec := wymoreJump) (Z_impl := wymoreStay)
    wymoreStay_jump_same_readout
  refine ⟨hcross.1, hcross.2, wymoreStay_jump_different_step⟩

/-! ## Incomplete readout table (pathology) -/

/-- Spec with silent readout (`RZ = none`); incomplete table emits no readout clause at that state. -/
def silentReadoutSpec : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs where
  sz_nonempty := ⟨0⟩
  NZ := wymoreStay.NZ
  RZ := fun _ => none

/-- Same dynamics, spurious output at silent spec states. -/
def spuriousOutputImpl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs where
  sz_nonempty := ⟨0⟩
  NZ := wymoreStay.NZ
  RZ := fun _ => some 0

theorem spuriousOutputImpl_not_extEqual :
    ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl := by
  intro h
  simpa [silentReadoutSpec, spuriousOutputImpl] using h.1 0

theorem partial_satisfies_incompleteReadout_not_implies_extEqual :
    SystemSatisfiesPartialDynamicsIncompleteReadout silentReadoutSpec spuriousOutputImpl ∧
      ¬ PartialExtEqual silentReadoutSpec spuriousOutputImpl := by
  refine ⟨?_, spuriousOutputImpl_not_extEqual⟩
  intro s0 f φ hmem
  dsimp [partialDynamicsTableIncompleteReadout] at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · dsimp [partialReadoutClausesIncomplete] at hmem
      rw [List.mem_flatMap] at hmem
      rcases hmem with ⟨s, _, hmatch⟩
      simp [silentReadoutSpec] at hmatch
    · dsimp [partialAutonomousClauses] at hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨s, _, heq⟩
      rw [← heq]
      simpa [partialAutonomousClause, silentReadoutSpec, spuriousOutputImpl, wymoreStay] using
        wymoreTrace_models_partialAutonomous spuriousOutputImpl s0 f s
  · dsimp [partialTransitionClauses] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨s, _, hmap⟩
    rw [List.mem_map] at hmap
    rcases hmap with ⟨i, _, heq⟩
    rw [← heq]
    simpa [partialTransitionClause, silentReadoutSpec, spuriousOutputImpl, wymoreStay] using
      wymoreTrace_models_partialTransition spuriousOutputImpl s0 f s i

/-! ## Autonomous input incomplete in pinned dynamics (pathology) -/

def autoNoneSharedRz : wymPathStates → wymPathOutputs := fun _ => 0

def autoNoneSpec : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs where
  sz_nonempty := ⟨0⟩
  NZ := fun s oi =>
    match oi with
    | some _ => if s = 0 then 0 else 0
    | none => if s = 0 then 0 else 0
  RZ := fun s => some (autoNoneSharedRz s)

def autoNoneImpl : DiscreteSystem wymPathStates wymPathInputs wymPathOutputs where
  sz_nonempty := ⟨0⟩
  NZ := fun s oi =>
    match oi with
    | some _ => if s = 0 then 0 else 0
    | none => if s = 0 then 0 else 1
  RZ := fun s => some (autoNoneSharedRz s)

theorem autoNoneSpec_alwaysOutputs : AlwaysOutputs autoNoneSpec :=
  fun s => ⟨autoNoneSharedRz s, rfl⟩

theorem autoNoneImpl_alwaysOutputs : AlwaysOutputs autoNoneImpl :=
  fun s => ⟨autoNoneSharedRz s, rfl⟩

theorem autoNone_differ_at_none :
    autoNoneSpec.NZ 1 none = 0 ∧ autoNoneImpl.NZ 1 none = 1 ∧
      autoNoneSpec.NZ 1 none ≠ autoNoneImpl.NZ 1 none := by
  native_decide

theorem autoNone_not_extEqual : ¬ PartialExtEqual autoNoneSpec autoNoneImpl := by
  intro h
  rcases autoNone_differ_at_none with ⟨_, _, hne⟩
  exact hne (h.2 1 none).symm

theorem autoNone_fsm_extEqual :
    FSMExtEqual (ofDiscreteSystem autoNoneSpec autoNoneSpec_alwaysOutputs)
      (ofDiscreteSystem autoNoneImpl autoNoneImpl_alwaysOutputs) := by
  constructor
  · intro s; rfl
  · intro s i; simp [ofDiscreteSystem, autoNoneSpec, autoNoneImpl]

theorem autoNone_pinned_dynamics :
    FSMSatisfiesDynamics (ofDiscreteSystem autoNoneSpec autoNoneSpec_alwaysOutputs)
      (ofDiscreteSystem autoNoneImpl autoNoneImpl_alwaysOutputs) :=
  fsm_extEqual_implies_satisfies_dynamics autoNone_fsm_extEqual

theorem pinnedDynamics_not_implies_extEqual_at_none :
    SystemSatisfiesDynamics autoNoneSpec autoNoneImpl
      autoNoneSpec_alwaysOutputs autoNoneImpl_alwaysOutputs ∧
      ¬ PartialExtEqual autoNoneSpec autoNoneImpl := by
  refine ⟨(SystemSatisfiesDynamics_iff_fsm _ _).1 autoNone_pinned_dynamics, autoNone_not_extEqual⟩

theorem pinnedDynamics_not_implies_partialDynamics :
    SystemSatisfiesDynamics autoNoneSpec autoNoneImpl
      autoNoneSpec_alwaysOutputs autoNoneImpl_alwaysOutputs ∧
      ¬ SystemSatisfiesPartialDynamics autoNoneSpec autoNoneImpl := by
  rcases pinnedDynamics_not_implies_extEqual_at_none with ⟨hPinned, hNe⟩
  refine ⟨hPinned, ?_⟩
  intro hPart
  exact hNe (partial_satisfies_implies_extEqual_readoutComplete (readoutSpecComplete_of autoNoneSpec) hPart)

/-! ## Closed system partial witness -/

def closedSystemImpl : DiscreteSystem Unit Empty Empty :=
  closedSystem

theorem closedSystem_readoutComplete : ReadoutSpecComplete closedSystem :=
  readoutSpecComplete_of closedSystem

theorem closedSystem_partial_iff_hom :
    SystemSatisfiesPartialDynamics closedSystem closedSystemImpl ↔
      PartialIsIdentityHomomorphicImage closedSystem closedSystemImpl :=
  partial_property_iff_hom_readoutComplete closedSystem_readoutComplete

theorem closedSystem_resolved :
    ReadoutSpecComplete closedSystem ∧
      (SystemSatisfiesPartialDynamics closedSystem closedSystemImpl ↔
        PartialIsIdentityHomomorphicImage closedSystem closedSystemImpl) :=
  ⟨closedSystem_readoutComplete, closedSystem_partial_iff_hom⟩

/-! ## Infinite closed readout witness -/

def counterClosedReadout : DiscreteSystem Nat Bool (Option Nat) where
  sz_nonempty := ⟨0⟩
  NZ := counterSystem.NZ
  RZ := fun n => if n = 0 then none else some n

theorem counterClosedReadout_not_alwaysOutputs : ¬ AlwaysOutputs counterClosedReadout := by
  intro h
  have hz : counterClosedReadout.RZ 0 = none := rfl
  rcases h 0 with ⟨w, hw⟩
  rw [hz] at hw
  cases hw

theorem counterClosedReadout_extensional_partial_refl :
    SystemSatisfiesExtensionalPartial counterClosedReadout counterClosedReadout :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem counterClosedReadout_satisfiesOpen_refl :
    SystemSatisfiesPartialDynamicsOpen counterClosedReadout counterClosedReadout :=
  partialDynamicsOpen_satisfies_reflexive counterClosedReadout

theorem counterClosedReadout_satisfiesCompiled_refl :
    SystemSatisfiesPartialDynamicsCompiled counterClosedReadout counterClosedReadout
      (compileObservablesPartialOpen counterClosedReadout) :=
  partialDynamicsCompiled_satisfies_reflexive counterClosedReadout

def counterClosedReadoutInput : ITZW Bool := fun _ => none

theorem counterClosedReadout_satisfiesPartialAssertionalFO_refl :
    SystemSatisfiesSpecPartialAssertionalFOAt counterClosedReadout counterClosedReadout 0
      counterClosedReadoutInput :=
  (partialAssertionalFO_at_iff_partialDynamicsOpen
    (readoutSpecCompleteOpen_of counterClosedReadout) 0 counterClosedReadoutInput).2
    counterClosedReadout_satisfiesOpen_refl

theorem counterClosedReadout_resolved :
    ¬ AlwaysOutputs counterClosedReadout ∧
      SystemSatisfiesPartialDynamicsOpen counterClosedReadout counterClosedReadout ∧
        SystemSatisfiesExtensionalPartial counterClosedReadout counterClosedReadout ∧
          PartialIsIdentityHomomorphicImage counterClosedReadout counterClosedReadout :=
  ⟨counterClosedReadout_not_alwaysOutputs, counterClosedReadout_satisfiesOpen_refl,
    counterClosedReadout_extensional_partial_refl,
    (extensional_partial_iff_hom).1 counterClosedReadout_extensional_partial_refl⟩

theorem closedSystem_satisfiesOpen :
    SystemSatisfiesPartialDynamicsOpen closedSystem closedSystemImpl :=
  partialDynamicsOpen_satisfies_reflexive closedSystem

/-! ## Partial dynamics: finite enumeration witness -/

/-- On finite open Moore systems, partial dynamics with `AlwaysOutputs` needs `Fintype SZ`. -/
theorem partial_agrees_with_pinned_when_alwaysOutputs {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
    [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (_hOut : AlwaysOutputs Z) :
    RequiresFiniteStateEnumeration SZ :=
  requiresFiniteStateEnumeration_of_fintype (SZ := SZ)

/-! ## Same-type surjective non-identity hom (separation witness) -/

abbrev swapHomStates := Fin 2

def swapHS : swapHomStates → swapHomStates
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩

theorem swapHS_surjective : Function.Surjective swapHS := by
  intro s
  match s with
  | ⟨0, _⟩ => exact ⟨⟨1, by decide⟩, rfl⟩
  | ⟨1, _⟩ => exact ⟨⟨0, by decide⟩, rfl⟩

theorem swapHS_ne_id : swapHS ≠ id := by
  intro h
  have := congrFun h ⟨0, by decide⟩
  simp [swapHS] at this

def swapSpecNZ : swapHomStates → Unit → swapHomStates := fun s _ => s
def swapImplNZ : swapHomStates → Unit → swapHomStates := fun s _ => s

def swapSpecRZ : swapHomStates → Bool := fun s => s != 0
def swapImplRZ : swapHomStates → Bool := fun s => s = 0

def swapSpecSys : DiscreteSystem swapHomStates Unit Bool :=
  DiscreteSystem.ofTotal swapSpecNZ swapSpecRZ ⟨0⟩

def swapImplSys : DiscreteSystem swapHomStates Unit Bool :=
  DiscreteSystem.ofTotal swapImplNZ swapImplRZ ⟨0⟩

def swapHomWitness : HomomorphicImageWitness swapSpecSys swapImplSys where
  HS := swapHS
  HI := id
  HO := id
  HS_surjective := swapHS_surjective
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro x oi
    cases x <;> cases oi <;> simp [swapHS, swapSpecSys, swapImplSys, DiscreteSystem.ofTotal,
      swapSpecNZ, swapImplNZ]
  preserves_readout := by
    intro x
    match x with
    | ⟨0, _⟩ => simp [swapHS, swapSpecSys, swapImplSys, DiscreteSystem.ofTotal, swapSpecRZ, swapImplRZ]
    | ⟨1, _⟩ => simp [swapHS, swapSpecSys, swapImplSys, DiscreteSystem.ofTotal, swapSpecRZ, swapImplRZ]

theorem swapSpecSys_alwaysOutputs : AlwaysOutputs swapSpecSys :=
  ofTotal_alwaysOutputs _ _ _

theorem swapImplSys_alwaysOutputs : AlwaysOutputs swapImplSys :=
  ofTotal_alwaysOutputs _ _ _

theorem swapHom_isNonIdentity : IsNonIdentityWitness swapHomWitness :=
  Or.inl swapHS_ne_id

theorem swapHom_sameType_image : SameTypeHomomorphicImage swapSpecSys swapImplSys :=
  ⟨swapHomWitness⟩

theorem swapHom_satisfies_cross :
    SystemSatisfiesExtensionalCross swapSpecSys swapImplSys :=
  extensional_cross_of_hom ⟨swapHomWitness⟩

theorem swapHom_not_extensional :
    ¬ SystemSatisfiesExtensional swapSpecSys swapImplSys
      swapSpecSys_alwaysOutputs swapImplSys_alwaysOutputs := by
  intro h
  have hR := h.1
  simp only [totalRz, swapSpecSys, swapImplSys, DiscreteSystem.ofTotal, swapSpecRZ, swapImplRZ,
    Option.get_some] at hR
  have := hR ⟨0, by decide⟩
  simp at this

theorem sameType_surjectiveHom_separation :
    SameTypeHomomorphicImage swapSpecSys swapImplSys ∧
      SystemSatisfiesExtensionalCross swapSpecSys swapImplSys ∧
        IsNonIdentityWitness swapHomWitness ∧
          ¬ SystemSatisfiesExtensional swapSpecSys swapImplSys
            swapSpecSys_alwaysOutputs swapImplSys_alwaysOutputs :=
  ⟨swapHom_sameType_image, swapHom_satisfies_cross, swapHom_isNonIdentity, swapHom_not_extensional⟩

/-! ## FO execution without extensional/hom -/

abbrev foPathStates := Fin 2
abbrev foPathInputs := Fin 1
abbrev foPathOutputs := Fin 1

def foUnreachableSharedRz : foPathStates → foPathOutputs := fun _ => 0

def foUnreachableSpec : DiscreteSystem foPathStates foPathInputs foPathOutputs :=
  DiscreteSystem.ofTotal (fun s _ => if s = 0 then 0 else 0) foUnreachableSharedRz ⟨0⟩

def foUnreachableImpl : DiscreteSystem foPathStates foPathInputs foPathOutputs :=
  DiscreteSystem.ofTotal (fun s _ => if s = 0 then 0 else 1) foUnreachableSharedRz ⟨0⟩

def foUnreachableInput : ITZW foPathInputs := fun _ => some 0

theorem foUnreachable_stay_at_zero (t : Time) :
    _root_.generateStateTrajectory foUnreachableImpl 0 foUnreachableInput t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    calc _root_.generateStateTrajectory foUnreachableImpl 0 foUnreachableInput (t + 1)
        = foUnreachableImpl.NZ (_root_.generateStateTrajectory foUnreachableImpl 0 foUnreachableInput t)
            (foUnreachableInput t) := rfl
      _ = 0 := by rw [ih, foUnreachableInput]; simp [foUnreachableImpl, DiscreteSystem.ofTotal]

theorem foUnreachableSpec_alwaysOutputs : AlwaysOutputs foUnreachableSpec :=
  ofTotal_alwaysOutputs _ _ _

theorem foUnreachableImpl_alwaysOutputs : AlwaysOutputs foUnreachableImpl :=
  ofTotal_alwaysOutputs _ _ _

theorem foUnreachable_differ_at_unreachable :
    foUnreachableSpec.NZ 1 (some 0) = 0 ∧
      foUnreachableImpl.NZ 1 (some 0) = 1 ∧
        foUnreachableSpec.NZ 1 (some 0) ≠ foUnreachableImpl.NZ 1 (some 0) := by
  native_decide

theorem foUnreachable_impl_satisfies_specFO :
    SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput := by
  dsimp [SystemSatisfiesSpecFOAt, compileSystemFO]
  simp only [SatisfiesFO]
  refine ⟨rfl, ?_, ?_⟩
  · intro t
    rw [foUnreachable_stay_at_zero t, foUnreachable_stay_at_zero (t + 1), foUnreachableInput]
    simp [foUnreachableSpec, DiscreteSystem.ofTotal]
  · intro t
    rw [_root_.generateOutputTrajectory_val, foUnreachable_stay_at_zero t]
    simp [foUnreachableSpec, foUnreachableSharedRz, foUnreachableImpl, DiscreteSystem.ofTotal]

theorem foUnreachable_not_extensional :
    ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
      foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs := by
  intro h
  rcases foUnreachable_differ_at_unreachable with ⟨_, _, hne⟩
  exact hne (h.2 1 (some 0)).symm

theorem foUnreachable_not_assertionalFO :
    ¬ SystemSatisfiesSpecAssertionalFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput := by
  intro h
  have := (assertionalFO_at_iff_extensional foUnreachableSpec_alwaysOutputs
    foUnreachableImpl_alwaysOutputs 0 foUnreachableInput).1 h
  exact foUnreachable_not_extensional this

theorem fo_execution_not_complete_for_hom :
    SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
      ¬ SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs ∧
        ¬ SystemIsIdentityHomomorphicImageOpen foUnreachableSpec foUnreachableImpl
          foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs := by
  refine ⟨foUnreachable_impl_satisfies_specFO, ?_, ?_⟩
  · exact foUnreachable_not_extensional
  · intro hHom
    exact foUnreachable_not_extensional
      ((extensional_property_iff_hom foUnreachableSpec_alwaysOutputs
        foUnreachableImpl_alwaysOutputs).mpr hHom)

end WymorePathologyExamples
