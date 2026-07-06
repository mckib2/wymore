import Mbse.CombinationalProperties
import Mbse.PropertyFragment
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

/-!
# Pathology sketch verification (optional Stage 4)

Paper Appendix Example 1 (fault-handling disjunction) suggests a cardinality obstruction
to homomorphic images when a branching reference has more inputs than the implementation.

Under identity-map combinational semantics, the obstruction is real: no surjective
input map exists when `#IZ_spec > #IZ_impl`. Under canonical synthesized references
(single committed resolution), homomorphism **does** exist — the sketch is not a
counterexample to Stage-1 bi-implication.
-/

namespace PathologyExamples

open PropertyFragment Combinational CombinationalProperties HomomorphismProperties SpecFromProperties

/-- Two-input implementation (committed to engine A). -/
abbrev implInputs := Fin 2

abbrev implOutputs := Fin 1

def implSystem : CombinationalSystem implInputs implOutputs where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := fun _ => 0

/-- Function table: always output `0` (engine A). -/
def implTable : implInputs → implOutputs := fun _ => 0

theorem impl_satisfies_table : CombSatisfiesFunction implSystem implTable := by
  rw [combSatisfiesFunction_iff]
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- Four-input branching reference (paper's naive spec). -/
abbrev specInputs := Fin 4

def specSystem : CombinationalSystem specInputs implOutputs where
  iz_finite := inferInstance
  oz_finite := inferInstance
  RZ := fun _ => 0

/-- No surjection `implInputs → specInputs` (cardinality obstruction). -/
theorem no_surjective_input_map : ¬ ∃ f : implInputs → specInputs, Function.Surjective f := by
  rintro ⟨f, hf⟩
  have hcard : Fintype.card specInputs ≤ Fintype.card implInputs :=
    Fintype.card_le_of_surjective (α := implInputs) (β := specInputs) f hf
  simp [Fintype.card_fin] at hcard

/-- Canonical synthesized spec for the implementation table uses two inputs, not four. -/
theorem canonical_spec_hom_exists :
    CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  comb_satisfies_implies_hom implTable implSystem impl_satisfies_table

/-- The pathology sketch does not refute Stage-1 bi-implication with canonical `synthesizeSpec`. -/
theorem example1_refuted_for_canonical_spec :
    CombSatisfiesFunction implSystem implTable ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec implTable) implSystem :=
  comb_property_iff_hom implTable implSystem

-- Example 2 (stuttering / future `F`) deferred until the property fragment adds `F`.

end PathologyExamples
