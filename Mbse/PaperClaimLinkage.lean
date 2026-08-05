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

/-!
# Paper claim linkage

Derived `paperClaimStatus` theorems and audits that reference `BiImplicationFailures`
and `TracePropertyLayer` (kept separate from `BlockerAudit` to avoid import cycles).
-/

namespace BlockerAudit

open BiImplicationFailures PathologyExamples WymorePathologyExamples
  PropertyFragment.FSM FSMProperties PhiDecode ExtensionalDynamicsFragment
  ClassicalAssertionalBridge WymoreExercises ComposedCaseStudy MinskyKit FibCaseStudy
  PartialDynamicsHomFragment Homomorphism TuringCoupling

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
Alternative buildables: two zones accepted (extra internal state, re-encoded state), three rejected
with impossibility proofs, and the rebuilt machine still realises the reference through Theorem
4.56 without re-verifying the machine.
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

end BlockerAudit
