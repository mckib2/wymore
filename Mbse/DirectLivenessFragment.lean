import Mbse.DynamicsLivenessExplore
import Mbse.TracePropertyLayer
import Mbse.LivenessFragment
import Mbse.PropertyFragmentSpec
import Mbse.TemporalLogic
import Mbse.BiImplicationFailures
import Mbse.PathologyExamples
import Mbse.FSMProperties
import Mbse.SpecFromProperties
import Mbse.PropertySemantics

/-!
# Direct-assertional liveness fragment

Engineer-authored liveness (`F` / `U`) checked on traces, **outside** the
dynamics-encoding hom↔Φ ladder. Informed by [`DynamicsLivenessExplore`](DynamicsLivenessExplore.lean):
restricted entailed-`F` may optionally sit on the dynamics ladder; unrestricted
mission liveness stays here.
-/

namespace DirectLivenessFragment

open TemporalLogic PropertyFragmentSpec TracePropertyLayer LivenessFragment
  BiImplicationFailures PathologyExamples FSMProperties DynamicsLivenessExplore
  SpecFromProperties PropertySemantics PropertyFragment.FSM

/-- Direct assertional fragment: allows `F` as a trace property, not dynamics-complete. -/
def directLivenessFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .excluded
  eventuallyPolicy := .restrictedBounded
  finiteClauseEnumeration := false
  dynamicsComplete := false
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem direct_not_dynamics_complete :
    directLivenessFragment.dynamicsComplete = false := rfl

/-- Satisfaction of a list of LTL formulas on all admissible traces. -/
abbrev SatisfiesDirectLiveness {SZ IZ OZ AP : Type}
    (Z : DiscreteSystem SZ IZ OZ) (props : TracePropertySet AP)
    (traceOf : SZ → ITZW IZ → Trace AP) :=
  SystemSatisfiesTraceProperty Z props traceOf

/-- Unrestricted direct `F` does not determine Def.~4.3 identity hom. -/
theorem directF_not_iff_hom :
    TracePropertyLayer.tracePropertySeparateProp :=
  TracePropertyLayer.traceProperty_separate_from_hom

/-- Conflating output-table dynamics with direct `F` fails gated verification. -/
theorem directF_conflation_fails_hom :
    ¬ VerificationEquivalence
      (FSMSatisfiesOutputTableAndFState fsmStay fsmJump 1)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump)
      (PhiAdequateSpec (FSMSatisfiesDynamics fsmStay fsmStay)
        (synthesizeFsmSpec fsmStay = synthesizeFsmSpec fsmStay)) :=
  freeMissionF_conflation_fails

/-- Separation: dynamics-encoding iff remains available; direct liveness is separate. -/
theorem layers_separated :
    (candidateVerdict .entailedF = .safeRedundant) ∧
      (candidateVerdict .freeMissionF = .blocked) ∧
      (directLivenessFragment.dynamicsComplete = false) ∧
      TracePropertyLayer.tracePropertySeparateProp :=
  ⟨rfl, rfl, rfl, directF_not_iff_hom⟩

end DirectLivenessFragment
