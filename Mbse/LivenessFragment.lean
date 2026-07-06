import Mbse.PropertyFragmentSpec
import Mbse.FSMProperties
import Mbse.PathologyExamples
import Mbse.FragmentPathologyRegistry
import Mbse.HomomorphismProperties

/-!
# Liveness / `F` fragment investigation

The dynamics-encoding assertional fragment excludes `F` (`EventuallyPolicy.excluded`).
Mission-level `F` formulas are expressible in [`TemporalLogic`](TemporalLogic.lean) but are
**not** part of the hom↔Φ bi-implication ladder.

* Trace-level: `blocked_eventuallyF` (semantic limit on synthetic traces)
* Wymore FSM-level: `blocked_eventuallyF_wymore` (G-only output table + `F` trace property)
* Trace-property layer API: [`TracePropertyLayer`](TracePropertyLayer.lean) (`traceProperty_separate_from_hom`)
* Full hom↔Φ with `F` in dynamics Φ: **not established** in this library
-/

namespace LivenessFragment

open PropertyFragmentSpec PropertyFragment.FSM FSMProperties TemporalLogic SystemToLTL
  PathologyExamples FragmentPathologyRegistry HomomorphismProperties

/-- Dynamics-complete fragment shape; `EventuallyPolicy` remains excluded from encoding tiers. -/
def safetyLivenessFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem safetyLivenessFragment_no_F_in_policy :
    safetyLivenessFragment.eventuallyPolicy = .excluded := rfl

theorem liveness_trace_obstruction :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      (∀ t, traceNoQ.holds t StutterAtom.p) ∧
        (∀ t, traceWithQ.holds t StutterAtom.p) ∧
          traceWithQ.models (LTL.F (LTL.atom StutterAtom.q)) ∧
            ¬ traceNoQ.models (LTL.F (LTL.atom StutterAtom.q)) :=
  blocked_eventuallyF

theorem liveness_wymore_obstruction :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) :=
  PathologyExamples.blocked_eventuallyF_wymore

/-- G-only output-table agreement does not imply hom when `F` mission distinguishes traces. -/
theorem liveness_no_hom_with_F_mission :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.F (LTL.atom (.state 1))) ∧
            ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump := by
  rcases PathologyExamples.blocked_eventuallyF_wymore with ⟨hSelf, hJump, hFJ, hFS⟩
  exact ⟨hSelf, hJump, hFJ, hFS, fsmStay_jump_not_identityHom⟩

/-- Identity extensional equality preserves state trajectories. -/
theorem fsm_extEqual_stateTraj {SZ IZ OZ : Type} {F G : FSMSystem SZ IZ OZ}
    (h : FSMExtEqual F G) (s0 : SZ) (f : ITZ IZ) (t : Time) :
    FSM.generateStateTrajectory F s0 f t = FSM.generateStateTrajectory G s0 f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [FSM.generateStateTrajectory_succ, ih, h.2 _ (f t)]

/-- Identity extensional equality preserves `F` state-mission on canonical traces. -/
theorem fsm_extEqual_preserves_F_state_mission {SZ IZ OZ : Type}
    {F G : FSMSystem SZ IZ OZ} (h : FSMExtEqual F G) (s0 : SZ) (f : ITZ IZ) (s : SZ)
    (hF : (SystemToLTL.fsmTrace F s0 f).models (LTL.F (LTL.atom (.state s)))) :
    (SystemToLTL.fsmTrace G s0 f).models (LTL.F (LTL.atom (.state s))) := by
  rcases hF with ⟨t, ht, ht'⟩
  refine ⟨t, ht, ?_⟩
  simp only [satisfiesAt, SystemToLTL.fsmTrace] at ht' ⊢
  rw [fsm_extEqual_stateTraj h s0 f t] at ht'
  exact ht'

/-- Alias: trace properties checked outside dynamics-encoding ladder. -/
theorem traceProperty_separate_from_hom :
    FSMSatisfiesOutputTable fsmStay fsmStay ∧
      FSMSatisfiesOutputTable fsmStay fsmJump ∧
        (SystemToLTL.fsmTrace fsmJump 0 (fun _ => 0)).models (LTL.atom (.state 1)).F ∧
          ¬ (SystemToLTL.fsmTrace fsmStay 0 (fun _ => 0)).models (LTL.atom (.state 1)).F ∧
            ¬ FSMIsIdentityHomomorphicImage fsmStay fsmJump :=
  liveness_no_hom_with_F_mission

end LivenessFragment
