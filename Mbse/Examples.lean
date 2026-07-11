import Mbse.WymoreExercises
import Mbse.SwarmExamples
import Mbse.AssertionalFC
import Mbse.DynamicsLivenessExplore
import Mbse.DynamicsLivenessUResponse
import Mbse.PartialDynamicsHomFragment
import Mbse.Homomorphism

/-!
# Example gallery

Documented, importable demos for papers and CI smoke tests:

* [`WymoreExercises`](WymoreExercises.lean) — ones-counter, `01110`, dual-port, real accumulator
* [`SwarmExamples`](SwarmExamples.lean) — UAV swarm mask case study
* [`AssertionalFC`](AssertionalFC.lean) — public verification API
* [`DynamicsLivenessExplore`](DynamicsLivenessExplore.lean) / [`DynamicsLivenessUResponse`](DynamicsLivenessUResponse.lean)
-/

namespace MbseExamples

open WymoreExercises DynamicsLivenessExplore DynamicsLivenessUResponse
  PartialDynamicsHomFragment Homomorphism

export WymoreExercises (caseStudy_playbook onesCounter pattern01110 realAccumulator
  dualPatternSpec pattern01110Shift pattern01110V1 pattern01110V2 pattern01110V3)

export DynamicsLivenessExplore (exploration_summary candidateVerdict)

theorem gallery_caseStudy_ok :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterRich ↔
      IsHomomorphicImage onesCounter onesCounterRich :=
  onesCounterRich_iff_hom

theorem gallery_fu_verdict :
    candidateVerdict .entailedF = .safeRedundant ∧
      candidateVerdict .freeMissionF = .blocked ∧
      candidateVerdict .tableProgressU = .blocked ∧
      candidateVerdict .dynamicsResponse = .blocked :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Re-export of the U/response exploration package. -/
def gallery_u_response_summary :=
  DynamicsLivenessUResponse.u_response_exploration_summary

end MbseExamples
