import Mbse.BlockerAudit
import Mbse.BiImplicationFailures
import Mbse.TracePropertyLayer
import Mbse.PathologyExamples
import Mbse.WymorePathologyExamples
import Mbse.FSMProperties
import Mbse.PhiDecode
import Mbse.WymorePropertyFragment
import Mbse.ExtensionalDynamicsFragment
import Mbse.ClassicalAssertionalBridge
import Mbse.WymoreExercises
import Mbse.ComposedCaseStudy
import Mbse.MinskyKit
import Mbse.FibCaseStudy
import Mbse.PartialDynamicsHomFragment
import Mbse.Homomorphism
import Mbse.TuringCoupling
import Mbse.TuringZoneVariants
import Mbse.TickGranularity
import Mbse.FragmentInvariance
import Mbse.SolverWitness
import Mbse.AssertionalCotyledonBridge

/-!
# Paper claim linkage

Derived `paperClaimStatus` theorems and audits that reference `BiImplicationFailures`
and `TracePropertyLayer` (kept separate from `BlockerAudit` to avoid import cycles).
-/

namespace BlockerAudit

open BiImplicationFailures PathologyExamples WymorePathologyExamples
  PropertyFragment.FSM FSMProperties PhiDecode ExtensionalDynamicsFragment
  ClassicalAssertionalBridge WymoreExercises ComposedCaseStudy MinskyKit FibCaseStudy
  PartialDynamicsHomFragment Homomorphism TuringCoupling Mbse.Wymore

/--
Every Wymore IOR—finite or infinite, deterministic or relational—has an exact
characteristic boundary fragment.
-/
theorem audit_iorBoundaryFragment :
    ∀ {S IR OR : Type} (Z : DiscreteSystem S IR OR)
      (R : WymoreRequirements.InputOutputRequirement IR OR) (s0 : S) (T : Set Time),
      IORTemporalFragment.Satisfies Z (IORTemporalFragment.ofIOR R) s0 T ↔
        WymoreRequirements.SatisfiesIOR Z R s0 T :=
  fun Z R s0 T => IORTemporalFragment.satisfies_ofIOR_iff Z R s0 T

def audit_iorBoundaryCotyledon
    (R : WymoreRequirements.InputOutputRequirement IR OR) :
    IORTemporalFragment.AFSR (IORTemporalFragment.ofIOR R) ≃
      WymoreRequirements.FSR R :=
  IORTemporalFragment.afsrEquivFSR R

theorem paperClaim_outputTableOnly_blocked
    (_h : SatisfactionWithoutHom (FSMSatisfiesOutputTable fsmStay fsmJump)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump)) :
    paperClaimStatus .outputTableOnlyPhi = .blocked :=
  rfl

theorem paperClaim_traceProperty_qualified :
    TracePropertyLayer.tracePropertySeparateProp →
      paperClaimStatus .fInTracePropertyLayer = .qualified :=
  fun _ => rfl

theorem audit_tracePropertySeparate :
    TracePropertyLayer.tracePropertySeparateProp ∧
      paperClaimStatus .fInTracePropertyLayer = .qualified := by
  constructor
  · exact TracePropertyLayer.traceProperty_separate_from_hom
  · rfl

theorem paperClaim_barePhi_blocked_derived
    (_h : fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump) :
    paperClaimStatus .barePhiUniqueSpec = .blocked :=
  rfl

theorem paperClaim_executionFO_blocked_derived
    (_h : SatisfactionWithoutHom
      (SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput)
      (SystemSatisfiesExtensional foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs)) :
    paperClaimStatus .executionFOSubstitutesHom = .blocked :=
  rfl

/-- Fragment-qualified hom projection equivalence is proved (headline dynamics-encoding bridge). -/
theorem audit_homProjection_equivalence :
    paperClaimStatus .homProjectionEquivalence = .safe ∧
      (∀ {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
        (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2),
        ClassicalFCMembership Z_spec Z_impl ↔
          AssertionalFCHomMembership Z_spec Z_impl) := by
  refine ⟨paperClaim_homProjection_safe, ?_⟩
  intro _ _ _ _ _ _ Z_spec Z_impl
  exact qualified_equivalence_homProjection Z_spec Z_impl

/-- Paper case-study kit: Part 1 directs + Part 2 alternates satisfy the headline bi-implication. -/
theorem audit_caseStudyPlaybook :
    paperClaimStatus .caseStudyPlaybook = .safe ∧
      (SystemSatisfiesPartialDynamicsHom counterInc counterIncShift ↔
        IsHomomorphicImage counterInc counterIncShift) ∧
      (SystemSatisfiesPartialDynamicsHom counterDec counterDecElab ↔
        IsHomomorphicImage counterDec counterDecElab) ∧
      (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestElab ↔
        IsHomomorphicImage zeroTest zeroTestElab) ∧
      (SystemSatisfiesPartialDynamicsHom zeroTest zeroTestDual ↔
        IsHomomorphicImage zeroTest zeroTestDual) :=
  ⟨paperClaim_caseStudyPlaybook_safe, counterIncShift_iff_hom, counterDecElab_iff_hom,
    zeroTestElab_iff_hom, zeroTestDual_iff_hom⟩

/-- Fibonacci composition: Φ↔hom, shelf NZ/RZ wiring, and `Nat.fib` functional correctness. -/
theorem audit_fibCaseStudy :
    (SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl ↔
      IsHomomorphicImage fibSpec fibAwkwardImpl) ∧
    (∀ n, fibSpecOut (fibSpecNext (fibRun n) .step) = Nat.fib n) ∧
    (∀ s n, (fibAwkwardNext s (.load n)).a = kitAssign 0) :=
  ⟨fibAwkward_iff_hom, fibSpec_computes_fib, fun s n =>
    (fibAwkward_uses_shelf_components).1 s n⟩

/-- Gallery cascade (not the paper spine): composed shift→counter buildable implements $Z_{12}$. -/
theorem audit_cascadeCaseStudy :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl ↔
      IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  cascadeAwkward_iff_hom

/-- Dual-port pattern select remains mechanized in the gallery. -/
theorem audit_dualPortMechanized :
    paperClaimStatus .dualPortMechanized = .safe ∧
      (SystemSatisfiesPartialDynamicsHom dualPatternSpec dualPatternElab ↔
        IsHomomorphicImage dualPatternSpec dualPatternElab) :=
  ⟨paperClaim_dualPort_safe, dualPatternElab_iff_hom⟩

/-- Restricted `F`/`U` inside dynamics-encoding Φ remains an open exploration. -/
theorem audit_restrictedFU_open :
    paperClaimStatus .restrictedFUInDynamicsEncoding = .openQuestion :=
  paperClaim_restrictedFU_open

/-! ## Turing-machine case study

The paper's spine: a machine presented as a genuine coupling recipe, the reference it realises, the
alternative zone buildables, and the compositional lift.  These audits are what the case-study
prose is allowed to claim.
-/

/--
Case-study spine: the coupling of a tape zone and a control zone realises the monolithic reference,
in fact isomorphically, and therefore satisfies the fragment compiled from it.
-/
theorem audit_turingCoupling :
    (SystemSatisfiesPartialDynamicsHom (TuringCoupling.tmReference Bool Bool bitFlipTable)
        (TuringCoupling.tmResultant Bool Bool bitFlipTable) ↔
      IsHomomorphicImage (TuringCoupling.tmReference Bool Bool bitFlipTable)
        (TuringCoupling.tmResultant Bool Bool bitFlipTable)) ∧
    IsIsomorphicTo (TuringCoupling.tmReference Bool Bool bitFlipTable)
      (TuringCoupling.tmResultant Bool Bool bitFlipTable) :=
  ⟨TuringCoupling.tmResultant_satisfies_iff_hom Bool Bool bitFlipTable,
    TuringCoupling.tmResultant_isomorphic_reference Bool Bool bitFlipTable⟩

/--
Not the case study.  The case study is the four-component run-length machine
(`audit_runLength`); these two-zone rebuilds describe a recipe the paper no longer uses.
The theorems stay because they are still true of that older recipe.
-/
theorem audit_turingZoneVariants :
    IsHomomorphicImage (TuringCoupling.tapeZone Bool) (TuringCoupling.instrTapeZone Bool) ∧
    IsIsomorphicTo (TuringCoupling.ctlZone Bool Bool bitFlipTable)
      (TuringCoupling.altCtlZone Bool Bool bitFlipTable) ∧
    ¬ IsHomomorphicImage (TuringCoupling.tapeZone Bool) (TuringCoupling.frozenTapeZone Bool) ∧
    ¬ IsHomomorphicImage (TuringCoupling.tapeZone Bool) (TuringCoupling.blindTapeZone Bool) ∧
    ¬ IsHomomorphicImage (TuringCoupling.quietTapeZone Bool) (TuringCoupling.tapeZone Bool) ∧
    SystemSatisfiesPartialDynamicsHom (TuringCoupling.tmReference Bool Bool bitFlipTable)
      (TuringCoupling.tmElaboratedResultant Bool Bool bitFlipTable) :=
  ⟨⟨TuringCoupling.instrTapeHom Bool⟩,
    ⟨TuringCoupling.altCtlIso Bool Bool bitFlipTable⟩,
    TuringCoupling.no_hom_frozenTape Bool false true (by decide),
    TuringCoupling.no_hom_blindTape Bool false true (by decide),
    TuringCoupling.no_hom_quietTape_from_tape Bool,
    TuringCoupling.tmElaboratedResultant_satisfies_reference_fragment Bool Bool bitFlipTable⟩

/--
Tick granularity: the same build fails a one-tick reference and satisfies the same reference
restated at two ticks per logical step.  Conformance is a statement about a reference *and* a clock.
-/
theorem audit_tickGranularity :
    ¬ SystemSatisfiesPartialDynamicsHom TickGranularity.flipRef TickGranularity.flipImpl ∧
      SystemSatisfiesPartialDynamicsHom TickGranularity.stretchedRef TickGranularity.flipImpl :=
  TickGranularity.tick_granularity_matters

/--
Fragment invariance: the compiled property set depends on neither side's encoding, survives port
relabelling, composes across a coupling recipe, and on finite systems determines its reference up to
isomorphism.  This is the defensible form of the paper's "you need not maintain `h`" claim.
-/
theorem audit_fragmentInvariance :
    (∀ {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
      {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
      {Z_impl' : DiscreteSystem SZ3 IZ3 OZ3}, IsIsomorphicTo Z_impl Z_impl' →
        (SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
          SystemSatisfiesPartialDynamicsHom Z_spec Z_impl')) ∧
    (∀ {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
      {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2},
        IsFinite Z1 → IsFinite Z2 →
        SystemSatisfiesPartialDynamicsHom Z1 Z2 → SystemSatisfiesPartialDynamicsHom Z2 Z1 →
        IsIsomorphicTo Z1 Z2) :=
  ⟨fun h => FragmentInvariance.satisfies_iff_of_impl_iso h,
    fun h1 h2 s1 s2 => FragmentInvariance.mutual_satisfaction_isomorphic h1 h2 s1 s2⟩

/--
Solver linkage: the conformance map the SAT solver returned for the tape/instrumented-tape instance,
re-checked by the kernel.  The solver proposes, Lean verifies.
-/
theorem audit_solverWitness :
    SystemSatisfiesPartialDynamicsHom SolverWitness.specSys SolverWitness.implSys :=
  SolverWitness.solver_verdict_confirmed

/--
Cotyledon bridge.  `Φ` yields `Implements`.  Identity-boundary `IOR` transfer extracts the
homomorphism from `Φ` and then applies Theorem 6.58; the identity equations are extra.
Non-identity port maps use `satisfies_ior_transported`, not Theorem 6.58.
-/
theorem audit_cotyledonBridge :
    (∀ {S1 S2 IR OR : Type} {Z_spec : DiscreteSystem S1 IR OR} {Z_impl : DiscreteSystem S2 IR OR}
      (hPhi : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl)
      (_hHI : (AssertionalCotyledonBridge.witnessOfPhi hPhi).HI = id)
      (_hHO : (AssertionalCotyledonBridge.witnessOfPhi hPhi).HO = id)
      (IOR : WymoreRequirements.InputOutputRequirement IR OR) (DSZ_impl : S2) (T : Set Time),
      WymoreRequirements.SatisfiesIOR Z_spec IOR
          ((AssertionalCotyledonBridge.witnessOfPhi hPhi).HS DSZ_impl) T →
        WymoreRequirements.SatisfiesIOR Z_impl IOR DSZ_impl T) ∧
    (∀ {S1 I1 O1 S2 I2 O2 : Type} {Z_spec : DiscreteSystem S1 I1 O1} {Z_impl : DiscreteSystem S2 I2 O2},
      SystemSatisfiesPartialDynamicsHom Z_spec Z_impl →
        Nonempty (WymoreImplementation.Implements Z_spec Z_impl)) :=
  ⟨fun hPhi hHI hHO IOR DSZ_impl T hSpec =>
    AssertionalCotyledonBridge.satisfies_ior_of_phi_idIO hPhi hHI hHO IOR DSZ_impl T hSpec,
   fun hPhi => AssertionalCotyledonBridge.implements_of_partialDynamicsHom hPhi⟩

/--
Case study.  The two-zone variant catalog is not this audit: the machine is tape, head, state
register, and instruction table, and that catalog describes a different recipe.  What is checked
here is streaming run-length encoding of an infinite bit trajectory.  The wired resultant
realises its pipeline reference exactly when it satisfies the fragment; the table-level phase
re-encoding does not change the verdict; a stuck head is rejected; and the same four-component
resultant is both buildable and paired with the pipeline IOR as an implementable design.
The trace `0,0,1` and the count cap are finite readings of the same step, not second algorithms.
-/
theorem audit_runLength :
    (SystemSatisfiesPartialDynamicsHom RunLengthMachine.pipelineRef
      RunLengthMachine.rleResultant ↔
      IsHomomorphicImage RunLengthMachine.pipelineRef RunLengthMachine.rleResultant) ∧
    (SystemSatisfiesPartialDynamicsHom RunLengthMachine.rleRef RunLengthMachine.instrTable ↔
      SystemSatisfiesPartialDynamicsHom RunLengthMachine.rleRef RunLengthMachine.tableFlip) ∧
    ¬ IsHomomorphicImage RunLengthMachine.head RunLengthMachine.stuckHead ∧
    Nonempty (WymoreTechnology.BuildableSystemDesign RunLengthMachine.rleTechnology) ∧
    Nonempty (WymoreTechnology.ImplementableSystemDesign RunLengthMachine.pipelineIOR
      RunLengthMachine.rleTechnology) ∧
    (RunLengthMachine.pipelineOut RunLengthMachine.trace001 3 = (false, 1) ∧
      RunLengthMachine.pipelineOut RunLengthMachine.trace001 5 = (false, 2) ∧
      RunLengthMachine.pipelineOut RunLengthMachine.trace001 7 = (true, 1)) ∧
    RunLengthMachine.rleStepCap 4 RunLengthMachine.rleInit false =
      RunLengthMachine.rleStep RunLengthMachine.rleInit false :=
  ⟨RunLengthMachine.rleResultant_pipeline_fragment_iff_hom,
    RunLengthMachine.table_fragment_invariant,
    RunLengthMachine.no_hom_stuckHead,
    ⟨RunLengthMachine.rle_resultant_in_bsr⟩,
    ⟨AssertionalCotyledonBridge.rle_in_isr⟩,
    RunLengthMachine.pipeline_trace_001,
    RunLengthMachine.rleStep_cap_eq (by decide : RunLengthMachine.rleInit.count < 4)⟩

end BlockerAudit
