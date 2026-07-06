import Mbse.SpecFromProperties
import Mbse.HomomorphismProperties
import Mbse.ObservablesFromSpec

/-!
# Combinational bi-implication: property satisfaction ↔ homomorphic image

Stage 1 of the FC ↔ temporal-logic proof program. Uses identical input/output types
and the canonical synthesized reference `synthesizeCombSpec F`.
-/

namespace CombinationalProperties

open PropertyFragment Combinational SpecFromProperties HomomorphismProperties ObservablesFromSpec PropertySemantics

/-- Identity homomorphic-image witness when implementation readout matches spec table. -/
def identityCombWitness {IZ OZ : Type} (F : IZ → OZ) [Fintype IZ] [Fintype OZ]
    (C_impl : CombinationalSystem IZ OZ)
    (hF : ∀ i, C_impl.RZ i = F i) :
    CombIdentityHomomorphicImageWitness (synthesizeCombSpec F) C_impl where
  preserves_readout := fun i => by simpa [synthesizeCombSpec_readout] using hF i

theorem comb_satisfies_implies_hom {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ)
    (h : CombSatisfiesFunction C_impl F) :
    CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl :=
  ⟨identityCombWitness F C_impl ((combSatisfiesFunction_iff C_impl F).mp h)⟩

theorem comb_hom_implies_satisfies {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ)
    (h : CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl) :
    CombSatisfiesFunction C_impl F := by
  rcases h with ⟨w⟩
  exact comb_identity_hom_impl_satisfies F w (synthesizeCombSpec_satisfies F)

/-- Stage-1 bi-implication for combinational function-table properties. -/
theorem comb_property_iff_hom {IZ OZ : Type} [Fintype IZ] [Fintype OZ]
    (F : IZ → OZ) (C_impl : CombinationalSystem IZ OZ) :
    CombSatisfiesFunction C_impl F ↔
      CombIsIdentityHomomorphicImage (synthesizeCombSpec F) C_impl :=
  ⟨comb_satisfies_implies_hom F C_impl, comb_hom_implies_satisfies F C_impl⟩

/-- Φ-adequacy: synthesized spec satisfies compiled observables and is canonical. -/
theorem comb_phi_adequate {IZ OZ : Type} [Fintype IZ] [Fintype OZ] (F : IZ → OZ) :
    PhiAdequateSpec
      (CombSatisfiesFunction (synthesizeCombSpec F) F)
      (synthesizeCombSpec F = synthesizeCombSpec F) := by
  constructor
  · exact synthesizeCombSpec_satisfies F
  · rfl

/-- Compiled observables from synthesized spec match the function-table property set. -/
theorem comb_synthesized_observables {IZ OZ : Type} [Fintype IZ] [Fintype OZ] (F : IZ → OZ) :
    compileCombObservables (synthesizeCombSpec F) = combFunctionTable (synthesizeCombSpec F) F := by
  simp [compileCombObservables, combFunctionTable, synthesizeCombSpec_readout]

end CombinationalProperties
