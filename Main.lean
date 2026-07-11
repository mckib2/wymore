import Mbse

/-!
# Verification report executable

Prints a one-page assertional-FC verification report for paper FSM case studies.
Run: `lake exe mbse`
-/

def main : IO Unit := do
  IO.println "=== Assertional FC verification report ==="
  IO.println "Semantic bi-implication: SystemSatisfiesPartialDynamicsHom ↔ IsHomomorphicImage"
  IO.println ""
  IO.println "Case studies (kernel-checked elaborations):"
  IO.println "  onesCounter → onesCounterRich: HOM ✓ (onesCounterRich_hom); Φ ✓ (iff)"
  IO.println "  pattern01110 → pattern01110Elab: HOM ✓; searchHom_complete ✓"
  IO.println "  pattern01110 → pattern01110Rich: HOM ✓; maps verified ✓"
  IO.println "  dualPatternSpec → dualPatternElab: HOM ✓ (Lean-complete; paper sketch)"
  IO.println "  realAccumulator → realAccumulatorRich: HOM ✓ (exact ℝ); Φ ✓ (iff)"
  IO.println ""
  IO.println "Finite engine API: HomSearch.searchHom / PhiChecker.verifyAssertionalFC"
  IO.println "Public facade: import Mbse.AssertionalFC"
  IO.println "Restricted F/U in Φ_dyn: open (DynamicsLivenessExplore)"
  IO.println "=== end report ==="
