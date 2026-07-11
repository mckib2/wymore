import Mbse.LivenessFragment
import Mbse.TracePropertyLayer
import Mbse.PartialDynamicsHomFragment
import Mbse.PropertyFragmentSpec
import Mbse.BiImplicationFailures
import Mbse.FragmentPathologyRegistry
import Mbse.PathologyExamples
import Mbse.FSMProperties
import Mbse.Homomorphism
import Mbse.TemporalLogic
import Mbse.WymorePropertyFragment
import Mbse.SystemToLTL
import Mbse.SpecFromProperties
import Mbse.PropertySemantics

/-!
# Dynamics-encoding liveness exploration (restricted `F` / `U`)

Outcome-agnostic investigation of whether restricted liveness schemas can enter
Φ_dyn while preserving the hom bi-implication. Production fragments keep
`EventuallyPolicy.excluded` until a candidate is proved safe.

## Verdict so far

* **Safe (redundant):** conjoining an `F`-mission *entailed* by identity extensional
  equality preserves the bi-implication (no new power).
* **Blocked (unrestricted):** free `F` / output-table+`F` conflation — existing
  `blocked_eventuallyF` / `traceProperty_conflation_fails_biImp`.
* **Blocked:** naive progress-`U`, free/`dynamics-tied` `G(p → F(q))` as Φ substitutes
  (see [`DynamicsLivenessUResponse`](DynamicsLivenessUResponse.lean)).
* **Boundary:** path X-chain ≠ full Φ_dyn; `G(p → X(q))` is guided clause; `F≤1` collapses
  to `X` only when the target atom is false at premise time.
* **Open:** bounded `F≤k` as an independent (non-sugar) constraint.
-/

namespace DynamicsLivenessExplore

open TemporalLogic LivenessFragment TracePropertyLayer PartialDynamicsHomFragment
  PropertyFragmentSpec BiImplicationFailures FragmentPathologyRegistry
  PathologyExamples FSMProperties Homomorphism WymorePropertyFragment SystemToLTL
  SpecFromProperties PropertySemantics PropertyFragment.FSM

/-! ## Candidate registry -/

inductive LivenessCandidate where
  | entailedF
  | boundedF
  | tableProgressU
  | dynamicsResponse
  | freeMissionF

inductive CandidateVerdict where
  | safeRedundant
  | blocked
  | openExplore

def candidateVerdict : LivenessCandidate → CandidateVerdict
  | .entailedF => .safeRedundant
  | .boundedF => .openExplore
  | .tableProgressU => .blocked
  | .dynamicsResponse => .blocked
  | .freeMissionF => .blocked

/-! ## Optional fragment specs (not production defaults) -/

def entailedLivenessFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .entailedOnly
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

def boundedLivenessFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .restrictedBounded
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem production_still_excludes_F :
    pinnedFragment.eventuallyPolicy = .excluded ∧
      partialHomPredicateFragment.eventuallyPolicy = .excluded :=
  ⟨rfl, rfl⟩

/-! ## Candidate 1: entailed / redundant `F` (positive) -/

/-- If identity extEqual holds and the spec trace meets `F(state s)`, so does the impl. -/
theorem entailedF_preserved_by_extEqual {SZ IZ OZ : Type}
    {F G : FSMSystem SZ IZ OZ} (h : FSMExtEqual F G) (s0 : SZ) (f : ITZ IZ) (s : SZ)
    (hF : (SystemToLTL.fsmTrace F s0 f).models (LTL.F (LTL.atom (.state s)))) :
    (SystemToLTL.fsmTrace G s0 f).models (LTL.F (LTL.atom (.state s))) :=
  fsm_extEqual_preserves_F_state_mission h s0 f s hF

/-- Adding an extEqual-entailed `F` does not break identity-hom bi-implication. -/
theorem entailedF_safe_with_identityHom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ]
    (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl ↔ FSMIsIdentityHomomorphicImage F_spec F_impl :=
  fsm_property_iff_hom F_spec F_impl

theorem candidate_entailedF_verdict :
    candidateVerdict .entailedF = .safeRedundant := rfl

/-! ## Candidate 5: free mission `F` (negative, re-export) -/

theorem freeMissionF_blocked :
    candidateVerdict .freeMissionF = .blocked ∧
      TracePropertyLayer.tracePropertySeparateProp :=
  ⟨rfl, TracePropertyLayer.traceProperty_separate_from_hom⟩

theorem freeMissionF_conflation_fails :
    ¬ VerificationEquivalence
      (FSMSatisfiesOutputTableAndFState fsmStay fsmJump 1)
      (FSMIsIdentityHomomorphicImage fsmStay fsmJump)
      (PhiAdequateSpec (FSMSatisfiesDynamics fsmStay fsmStay)
        (synthesizeFsmSpec fsmStay = synthesizeFsmSpec fsmStay)) :=
  TracePropertyLayer.traceProperty_conflation_fails_gatedVerification

/-! ## Bounded eventually `F≤k` -/

/-- Bounded eventually: `φ` holds within `k` steps from `t`. -/
def satisfiesFBounded {AP : Type} (φ : LTL AP) (σ : Trace AP) (t k : Nat) : Prop :=
  ∃ t', t ≤ t' ∧ t' ≤ t + k ∧ satisfiesAt φ σ t'

theorem FBounded_implies_F {AP : Type} (φ : LTL AP) (σ : Trace AP) (t k : Nat)
    (h : satisfiesFBounded φ σ t k) : satisfiesAt (.F φ) σ t := by
  rcases h with ⟨t', ht, _, hφ⟩
  exact ⟨t', ht, hφ⟩

theorem F_zero_iff {AP : Type} (φ : LTL AP) (σ : Trace AP) (t : Nat) :
    satisfiesFBounded φ σ t 0 ↔ satisfiesAt φ σ t := by
  constructor
  · intro ⟨t', ht, ht', hφ⟩
    have : t' = t := Nat.le_antisymm ht' ht
    simpa [this] using hφ
  · intro h
    exact ⟨t, le_rfl, Nat.le_refl _, h⟩

/-- `F≤1` unfolds to `φ ∨ X φ`. -/
theorem FBounded_one_unfold {AP : Type} (φ : LTL AP) (σ : Trace AP) (t : Nat) :
    satisfiesFBounded φ σ t 1 ↔
      satisfiesAt φ σ t ∨ satisfiesAt φ σ (t + 1) := by
  constructor
  · intro ⟨t', ht, ht', hφ⟩
    by_cases hEq : t' = t
    · exact Or.inl (hEq ▸ hφ)
    · have : t' = t + 1 := by omega
      exact Or.inr (this ▸ hφ)
  · intro h
    rcases h with h | h
    · exact ⟨t, le_rfl, Nat.le_add_right _ _, h⟩
    · exact ⟨t + 1, Nat.le_add_right _ _, le_rfl, h⟩

theorem candidate_boundedF_open :
    candidateVerdict .boundedF = .openExplore := rfl

/-! ## Table-progress until (syntax available; bi-imp open) -/

/-- Compiled progress until: `(¬done) U done` on a state atom. -/
def progressUntilClause {SZ IZ OZ : Type} (done : Atom SZ IZ OZ) : LTL (Atom SZ IZ OZ) :=
  LTL.U (LTL.not (LTL.atom done)) (LTL.atom done)

theorem candidate_tableProgressU_open :
    candidateVerdict .tableProgressU = .blocked := rfl

theorem candidate_dynamicsResponse_open :
    candidateVerdict .dynamicsResponse = .blocked := rfl

/-! ## Summary for paper / comparative report -/

theorem exploration_summary :
    (candidateVerdict .entailedF = .safeRedundant) ∧
      (candidateVerdict .freeMissionF = .blocked) ∧
      (candidateVerdict .boundedF = .openExplore) ∧
      (candidateVerdict .tableProgressU = .blocked) ∧
      (candidateVerdict .dynamicsResponse = .blocked) ∧
      (pinnedFragment.eventuallyPolicy = .excluded ∧
        partialHomPredicateFragment.eventuallyPolicy = .excluded) :=
  ⟨rfl, rfl, rfl, rfl, rfl, production_still_excludes_F⟩

end DynamicsLivenessExplore
