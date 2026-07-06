import Mbse.PathologyExamples
import Mbse.LivenessFragment
import Mbse.PropertySemantics
import Mbse.GeneralProperties
import Mbse.BiImplicationFailures
import Mbse.SpecFromProperties
import Mbse.ExtensionalDynamicsFragment

/-!
# Trace property layer vs dynamics encoding

**Dynamics encoding** (`compileObservables`, `fsmDynamicsTable`): G-shaped assertional
properties in the hom↔Φ bi-implication ladder.

**Trace properties** (`F`, etc.): checked on execution traces outside that ladder.
Do not conflate trace satisfaction with dynamics-encoding verification.
-/

namespace TracePropertyLayer

open PropertySemantics HomSoundness GeneralProperties LivenessFragment BiImplicationFailures
  SpecFromProperties ExtensionalDynamicsFragment PropertyFragment.General
  PropertyFragment.FSM FSMProperties TemporalLogic SystemToLTL HomomorphismProperties
  WymorePropertyFragment

variable {SZ IZ OZ : Type}

/-! ## Trace property types -/

/-- LTL properties checked on traces; not part of dynamics-encoding hom↔Φ ladder. -/
structure TracePropertySet (AP : Type) where
  formulas : List (LTL AP)

def SystemSatisfiesTraceProperty {SZ IZ OZ AP : Type}
    (_Z : DiscreteSystem SZ IZ OZ) (props : TracePropertySet AP)
    (traceOf : SZ → ITZW IZ → Trace AP)
    (Adm : ITZW IZ → Prop := AllInputs) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ), Adm f → ∀ φ, φ ∈ props.formulas → (traceOf s0 f).models φ

/-- Dynamics-encoding property set (existing compileObservables / fsmDynamicsTable). -/
abbrev DynamicsEncodingPhi (SZ IZ OZ : Type) := PropertySet (LTL (Atom SZ IZ OZ))

/-! ## Positive dynamics-encoding theorems (re-exports) -/

theorem dynamicsEncoding_iff_hom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateSpec (SystemSatisfiesDynamics Z Z hZ hZ) (synthesizeSpec Z hZ = Z)) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  (stage3_verification_equivalence hZ hImpl) _hAdeq

theorem dynamicsEncoding_extensional_iff_hom {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  extensional_synthesized_verification_open hZ hImpl _hAdeq

/-! ## Layer boundary (explicit non-claim) -/

/-- G-only output-table agreement + `F` trace property does not determine hom. -/
theorem traceProperty_separate_from_hom :
    FSMSatisfiesOutputTable PathologyExamples.fsmStay PathologyExamples.fsmStay ∧
      FSMSatisfiesOutputTable PathologyExamples.fsmStay PathologyExamples.fsmJump ∧
        (SystemToLTL.fsmTrace PathologyExamples.fsmJump 0 (fun _ => 0)).models
            (LTL.atom (.state 1)).F ∧
          ¬ (SystemToLTL.fsmTrace PathologyExamples.fsmStay 0 (fun _ => 0)).models
              (LTL.atom (.state 1)).F ∧
            ¬ FSMIsIdentityHomomorphicImage PathologyExamples.fsmStay PathologyExamples.fsmJump :=
  LivenessFragment.liveness_no_hom_with_F_mission

theorem traceProperty_conflation_fails_biImp :
    ¬ VerificationEquivalence
      (FSMSatisfiesOutputTable PathologyExamples.fsmStay PathologyExamples.fsmJump)
      (FSMIsIdentityHomomorphicImage PathologyExamples.fsmStay PathologyExamples.fsmJump)
      True :=
  biImpFails_readoutOnly_verificationEquivalence

/-! ## Composed verification obligation -/

structure VerificationObligation where
  dynamicsEncodingAdequate : Prop
  tracePropertiesSatisfied : Prop
  homVerified : Prop

end TracePropertyLayer
