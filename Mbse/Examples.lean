import Mbse.WymoreExercises
import Mbse.ComposedCaseStudy
import Mbse.MinskyKit
import Mbse.FibCaseStudy
import Mbse.SwarmExamples
import Mbse.AssertionalFC
import Mbse.DynamicsLivenessExplore
import Mbse.DynamicsLivenessUResponse
import Mbse.PartialDynamicsHomFragment
import Mbse.Homomorphism

/-!
# Example gallery

Documented, importable demos for papers and CI smoke tests:

* [`MinskyKit`](MinskyKit.lean) / [`FibCaseStudy`](FibCaseStudy.lean) — paper case-study spine
* [`WymoreExercises`](WymoreExercises.lean) — gallery: ones-counter, `01110`, dual-port, real accumulator
* [`ComposedCaseStudy`](ComposedCaseStudy.lean) — gallery: cascade double-`01110` + Plus3
* [`SwarmExamples`](SwarmExamples.lean) — UAV swarm mask case study
* [`AssertionalFC`](AssertionalFC.lean) — public verification API
-/

namespace MbseExamples

open WymoreExercises ComposedCaseStudy MinskyKit FibCaseStudy
  DynamicsLivenessExplore DynamicsLivenessUResponse
  PartialDynamicsHomFragment Homomorphism

export MinskyKit (minskyKit_playbook counterInc counterDec natAdder zeroTest
  counterIncShift)

export FibCaseStudy (fibSpec fibAwkwardImpl fibAwkward_iff_hom fibSpec_computes_fib
  fibAwkward_uses_shelf_components fib_caseStudy_playbook)

export WymoreExercises (caseStudy_playbook onesCounter pattern01110 realAccumulator
  dualPatternSpec pattern01110Shift pattern01110V1 pattern01110V2 pattern01110V3)

export ComposedCaseStudy (cascadeSpec cascadeAwkwardImpl cascadeAwkward_iff_hom
  cascade_caseStudy_playbook plus3FromOnes)

export DynamicsLivenessExplore (exploration_summary candidateVerdict)

theorem gallery_minskyKit_ok :
    SystemSatisfiesPartialDynamicsHom counterInc counterIncShift ↔
      IsHomomorphicImage counterInc counterIncShift :=
  counterIncShift_iff_hom

theorem gallery_fib_ok :
    SystemSatisfiesPartialDynamicsHom fibSpec fibAwkwardImpl ↔
      IsHomomorphicImage fibSpec fibAwkwardImpl :=
  fibAwkward_iff_hom

theorem gallery_caseStudy_ok :
    SystemSatisfiesPartialDynamicsHom onesCounter onesCounterRich ↔
      IsHomomorphicImage onesCounter onesCounterRich :=
  onesCounterRich_iff_hom

theorem gallery_cascade_ok :
    SystemSatisfiesPartialDynamicsHom cascadeSpec cascadeAwkwardImpl ↔
      IsHomomorphicImage cascadeSpec cascadeAwkwardImpl :=
  cascadeAwkward_iff_hom

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
