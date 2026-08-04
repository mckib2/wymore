import Mbse.Isomorphism
import Mbse.IsomorphismConstructions
import Mbse.CouplingIsomorphism

/-!
# Chapter 4 — homomorphism algebra, isomorphisms and copies

Exercise/theorem aliases for the Chapter 4 results proved in
[`Mbse.Isomorphism`](../Isomorphism.lean) (Theorems 4.31, 4.38, 4.45 and Exercises 4.80, 4.81,
4.82, 4.84), [`Mbse.IsomorphismConstructions`](../IsomorphismConstructions.lean) (Theorem 4.58 and
Exercises 4.69, 4.71, 4.72, 4.74, 4.83) and
[`Mbse.CouplingIsomorphism`](../CouplingIsomorphism.lean) (Theorem 4.56, Corollary 4.59 and
Exercise 4.85).

Port encoding: textbook `#IPZ₂ = #IPZ₁` is modeled by an explicit bijection `σ : Port₂ ≃ Port₁`
between port index types, so a port-preserving map may *permute* ports; Def 4.27 clause (ii)
becomes "the homomorphism acts portwise through surjections `HIᵢ : IᵢZ₂ → I_{σ i}Z₁`".
-/

namespace Mbse.TextbookExercises.Ch04

open Homomorphism

/-! ## Theorem 4.31: homomorphism is reflexive and transitive -/

/--
  [textbook/theorem4.31/theorem/homomorphism_reflexive_transitive]
  `Z = HIMSY(Z, ID(SZ), ID(IZ), ID(OZ))`.
-/
abbrev thm4_31_reflexive {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :=
  isHomomorphicImage_refl Z

/--
  [textbook/theorem4.31/theorem/homomorphism_reflexive_transitive]
  `Z1 = HIMSY(Z3, HS1 ∘ HS2, HI1 ∘ HI2, HO1 ∘ HO2)`.
-/
abbrev thm4_31_transitive {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : IsHomomorphicImage Z1 Z2) (h23 : IsHomomorphicImage Z2 Z3) :=
  isHomomorphicImage_trans h12 h23

/-! ## Theorem 4.38: isomorphism is symmetric -/

/--
  [textbook/theorem4.38/theorem/isomorphism_symmetric]
  `Z1 = ISY(Z2, HS, HI, HO)` iff `Z2 = ISY(Z1, HS⁻¹, HI⁻¹, HO⁻¹)`.
-/
abbrev thm4_38_isomorphism_symmetric {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2) :=
  isIsomorphicTo_comm (Z1 := Z1) (Z2 := Z2)

/-! ## Theorem 4.45: port maps of a port-preserving isomorphism are bijections -/

/--
  [textbook/theorem4.45/theorem/port_maps_bijective]
  In a port-preserving isomorphism each `HIᵢ` is `1TO1` and `ONTO`, so corresponding ports are
  equivalent sets.
-/
abbrev thm4_45_port_maps_bijective {Port1 Port2 : Type}
    {Val1 : Port1 → Type} {Val2 : Port2 → Type} [∀ p, Nonempty (Val2 p)] {σ : Port2 ≃ Port1}
    {H : ((p : Port2) → Val2 p) → ((p : Port1) → Val1 p)}
    (hp : PreservesPorts σ H) (hinj : Function.Injective H) (p : Port2) :=
  hp.port_bijective hinj p

/-! ## Exercise 4.80 / 4.81: `HIMPPSY` -/

/--
  [textbook/exercise4.80/theorem/himppsy_is_parameterization]
  `HIMPPSY` is a system parameterization refining `HIMSY`, and it preserves input and output ports
  by construction.
-/
abbrev ex4_80_himppsy_is_parameterization {SZ1 SZ2 : Type}
    {Port1 Port2 OutPort1 OutPort2 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    (h : IsPortPreservingHomImage Z1 Z2) :=
  h.isHomomorphicImage

/--
  [textbook/exercise4.80/theorem/preserves_input_ports]
  `HIMPPSY` actually preserves input ports.
-/
abbrev ex4_80_preserves_input_ports {SZ1 SZ2 : Type} {Port1 Port2 OutPort1 OutPort2 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    (h : PortPreservingHomWitness Z1 Z2) :=
  IsPortPreservingHomImage.inPorts_spec h

/--
  [textbook/exercise4.80/theorem/preserves_output_ports]
  `HIMPPSY` actually preserves output ports.
-/
abbrev ex4_80_preserves_output_ports {SZ1 SZ2 : Type} {Port1 Port2 OutPort1 OutPort2 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    (h : PortPreservingHomWitness Z1 Z2) :=
  IsPortPreservingHomImage.outPorts_spec h

/--
  [textbook/exercise4.81/theorem/himppsy_reflexive_transitive]
  `HIMPPSY` is reflexive.
-/
abbrev ex4_81_reflexive {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :=
  isPortPreservingHomImage_refl Z

/--
  [textbook/exercise4.81/theorem/himppsy_reflexive_transitive]
  `HIMPPSY` is transitive.
-/
abbrev ex4_81_transitive {SZ1 SZ2 SZ3 : Type}
    {Port1 Port2 Port3 OutPort1 OutPort2 OutPort3 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type} {PortVal3 : Port3 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    {OutPortVal3 : OutPort3 → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port3) → PortVal3 p) ((q : OutPort3) → OutPortVal3 q)}
    (h12 : IsPortPreservingHomImage Z1 Z2) (h23 : IsPortPreservingHomImage Z2 Z3) :=
  isPortPreservingHomImage_trans h12 h23

/-! ## Exercise 4.82: isomorphism is reflexive, transitive and symmetric -/

/--
  [textbook/exercise4.82/theorem/isomorphism_reflexive]
  Exercise 4.82 (i).
-/
abbrev ex4_82_reflexive {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :=
  isIsomorphicTo_refl Z

/--
  [textbook/exercise4.82/theorem/isomorphism_transitive]
  Exercise 4.82 (ii).
-/
abbrev ex4_82_transitive {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : IsIsomorphicTo Z1 Z2) (h23 : IsIsomorphicTo Z2 Z3) :=
  isIsomorphicTo_trans h12 h23

/--
  [textbook/exercise4.82/theorem/isomorphism_symmetric]
  Exercise 4.82 (iii).
-/
abbrev ex4_82_symmetric {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsIsomorphicTo Z1 Z2) :=
  isIsomorphicTo_symm h

/-! ## Exercise 4.84: the copy relation is an equivalence -/

/--
  [textbook/exercise4.84/theorem/copy_reflexive]
  Exercise 4.84: reflexivity.
-/
abbrev ex4_84_reflexive {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :=
  isCopyOf_refl Z

/--
  [textbook/exercise4.84/theorem/copy_transitive]
  Exercise 4.84: transitivity.
-/
abbrev ex4_84_transitive {SZ1 SZ2 SZ3 : Type}
    {Port1 Port2 Port3 OutPort1 OutPort2 OutPort3 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type} {PortVal3 : Port3 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    {OutPortVal3 : OutPort3 → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port3) → PortVal3 p) ((q : OutPort3) → OutPortVal3 q)}
    (h12 : IsCopyOf Z1 Z2) (h23 : IsCopyOf Z2 Z3) :=
  isCopyOf_trans h12 h23

/--
  [textbook/exercise4.84/theorem/copy_symmetric]
  Exercise 4.84: symmetry, in the strong form that allows the copy to permute ports.
-/
abbrev ex4_84_symmetric {SZ1 SZ2 : Type} {Port1 Port2 OutPort1 OutPort2 : Type}
    {PortVal1 : Port1 → Type} {PortVal2 : Port2 → Type}
    {OutPortVal1 : OutPort1 → Type} {OutPortVal2 : OutPort2 → Type}
    [∀ p, Nonempty (PortVal2 p)] [∀ q, Nonempty (OutPortVal2 q)]
    {Z1 : DiscreteSystem SZ1 ((p : Port1) → PortVal1 p) ((q : OutPort1) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port2) → PortVal2 p) ((q : OutPort2) → OutPortVal2 q)}
    (h : IsCopyOf Z1 Z2) :=
  isCopyOf_symm h

/-! ## A copy that genuinely permutes ports

The strengthened Def 4.27 allows the two systems to index their ports differently. This example
exhibits a copy whose input port bijection is the non-identity permutation of a two-element port
set: `Z₁` carries `ℕ` on port `false` and `Bool` on port `true`, while `Z₂` carries them the other
way round. No copy with the identity port bijection can exist here, since `ℕ` and `Bool` are not
in bijection.
-/

/-- Input port values of `Z₁`: port `true` carries `Bool`, port `false` carries `ℕ`. -/
def swapVal1 : Bool → Type := fun b => cond b Bool Nat

/-- Input port values of `Z₂`: the same two sets attached to the opposite ports. -/
def swapVal2 : Bool → Type := fun b => cond b Nat Bool

instance swapVal2_nonempty (p : Bool) : Nonempty (swapVal2 p) := by
  cases p
  · exact ⟨(false : Bool)⟩
  · exact ⟨(0 : Nat)⟩

/-- The single output port carries `Unit` in both systems. -/
def unitOut : Unit → Type := fun _ => Unit

instance unitOut_nonempty (q : Unit) : Nonempty (unitOut q) := ⟨()⟩

/-- [textbook/definition4.47/requirement/input_port_count] The port bijection exchanging the two
input ports. -/
def swapPorts : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- `HI`, which reads port `p` of `Z₂` off port `!p` of `Z₁`. -/
def swapHI (f : (p : Bool) → swapVal2 p) : (p : Bool) → swapVal1 p
  | true => f false
  | false => f true

/-- [textbook/definition4.27/component/port_family] `SHIS`: the identity on each port's value set,
but attached to the swapped port. -/
def swapPort : (p : Bool) → swapVal2 p → swapVal1 (swapPorts p)
  | true => _root_.id
  | false => _root_.id

def swapSystem1 : DiscreteSystem Unit ((p : Bool) → swapVal1 p) ((q : Unit) → unitOut q) where
  sz_nonempty := ⟨()⟩
  NZ := fun _ _ => ()
  RZ := fun _ => some (fun _ => ())

def swapSystem2 : DiscreteSystem Unit ((p : Bool) → swapVal2 p) ((q : Unit) → unitOut q) where
  sz_nonempty := ⟨()⟩
  NZ := fun _ _ => ()
  RZ := fun _ => some (fun _ => ())

theorem swapHI_bijective : Function.Bijective swapHI := by
  constructor
  · intro f g h
    funext p
    cases p
    · exact congr_fun h true
    · exact congr_fun h false
  · intro g
    refine ⟨fun p => match p with | true => g false | false => g true, ?_⟩
    funext p
    cases p <;> rfl

/-- A copy witness whose input port bijection is the swap. -/
def swapCopyWitness : CopyWitness swapSystem1 swapSystem2 where
  HS := _root_.id
  HI := swapHI
  HO := _root_.id
  HS_surjective := Function.surjective_id
  HI_surjective := swapHI_bijective.2
  HO_surjective := Function.surjective_id
  HS_injective := Function.injective_id
  HI_injective := swapHI_bijective.1
  HO_injective := Function.injective_id
  preserves_transition := by intro x oi; rfl
  preserves_readout := by intro x; rfl
  inIdx := swapPorts
  outIdx := Equiv.refl Unit
  inPorts :=
    { port := swapPort
      port_surjective := by intro p; cases p <;> exact Function.surjective_id
      proj := by intro f p; cases p <;> rfl }
  outPorts := PreservesPorts.id

/--
  [textbook/definition4.47/definition/copy]
  A copy whose port bijection is a genuine permutation: `swapPorts` moves both ports.
-/
theorem swap_isCopyOf_permuting :
    IsCopyOf swapSystem1 swapSystem2 ∧ ∀ p, swapCopyWitness.inIdx p ≠ p := by
  refine ⟨⟨swapCopyWitness⟩, ?_⟩
  intro p
  cases p <;> simp [swapCopyWitness, swapPorts]

/-- [textbook/exercise4.84/theorem/copy_symmetric] The port-permuting copy is symmetric too. -/
theorem swap_isCopyOf_symm : IsCopyOf swapSystem2 swapSystem1 :=
  isCopyOf_symm ⟨swapCopyWitness⟩

/-! ## Theorem 4.58: replacing an output port by an equivalent set -/

/--
  [textbook/theorem4.58/theorem/replacement_is_copy]
  `Z₂ ∈ DSYSTEMS`, `OnZ₂ = B` and `Z₂ = COPY(Z₁, ID(SZ₁), ID(IZ₁), HO, SHIS, SHOS)`.
-/
abbrev thm4_58_replacement_is_copy {SZ InPort OutPort : Type} [DecidableEq OutPort]
    {InVal : InPort → Type} {OutVal1 : OutPort → Type}
    (Z1 : DiscreteSystem SZ ((p : InPort) → InVal p) ((q : OutPort) → OutVal1 q))
    (n : OutPort) {B : Type} (F : OutVal1 n ≃ B) :=
  replaceOutPort_isCopy Z1 n F

/-! ## Exercise 4.69: the assertion is false -/

/--
  [textbook/exercise4.69/theorem/counterexample]
  A finite system that *is* a homomorphic image of a non-finite system.
-/
abbrev ex4_69_counterexample := Homomorphism.ex4_69_counterexample

/--
  [textbook/exercise4.69/theorem/assertion_refuted]
  Exercise 4.69: the stated assertion does not hold.
-/
abbrev ex4_69_assertion_false := Homomorphism.ex4_69_assertion_false

/-! ## Exercise 4.71 -/

/--
  [textbook/exercise4.71/theorem/construction]
  Exercise 4.71: `Z₁ = HIMSY(Z₂, PJN(SZ₂, 2), ID(IZ₂), ID(OZ₂))`.
-/
abbrev ex4_71_construction {SZ IZ OZ : Type} (Z1 : DiscreteSystem SZ IZ OZ) :=
  Homomorphism.ex4_71_construction Z1

/-! ## Exercises 4.72 and 4.74: consistent elaborations -/

/--
  [textbook/exercise4.72/theorem/consistent_elaboration_states]
  Exercise 4.72: consistent elaboration with respect to states.
-/
abbrev ex4_72_consistent_elaboration {SZ1 IZ OZ S : Type}
    (Z1 : DiscreteSystem SZ1 IZ OZ) (e : StatePartition SZ1 S) (ch : ChoiceFunction S) :=
  Homomorphism.ex4_72_consistent_elaboration Z1 e ch

/--
  [textbook/exercise4.74/theorem/consistent_elaboration]
  Exercise 4.74: consistent elaboration with respect to states, inputs and outputs.
-/
abbrev ex4_74_consistent_elaboration {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2)
    (chS : ChoiceFunction SZ2) (chO : ChoiceFunction OZ2) :=
  Homomorphism.ex4_74_consistent_elaboration d chS chO

/-! ## Exercise 4.83 -/

/--
  [textbook/exercise4.83/theorem/mutual_homomorphism_isomorphic]
  Exercise 4.83: mutually homomorphic finite systems are isomorphic.
-/
abbrev ex4_83_mutual_homomorphism_isomorphic {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (hfin1 : IsFinite Z1) (hfin2 : IsFinite Z2)
    (h1 : IsHomomorphicImage Z1 Z2) (h2 : IsHomomorphicImage Z2 Z1) :=
  Homomorphism.ex4_83_mutual_homomorphism_isomorphic hfin1 hfin2 h1 h2

/-! ## Theorem 4.56 / Corollary 4.59 / Exercise 4.85: coupling-level results -/

/--
  [textbook/theorem4.56/theorem/resultant_port_preserving_homomorphism]
  Theorem 4.56: componentwise port-preserving homomorphisms lift to the resultant.
-/
abbrev thm4_56_resultant_homomorphic_image {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k)) :=
  Homomorphism.thm4_56_resultant_homomorphic_image E hOut1 hOut2

/--
  [textbook/corollary4.59/theorem/resultant_copy]
  Corollary 4.59: componentwise copies lift to the resultant.
-/
abbrev cor4_59_resultant_copy {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (hS : ∀ i, Function.Injective (E.hom i).HS)
    (hI : ∀ (i : Fin n) (p : SCR.VSCR.Port i), Function.Injective ((E.inPorts i).port p))
    (hO : ∀ (i : Fin n) (q : SCR.VSCR.OutPort i), Function.Injective ((E.outPorts i).port q)) :=
  Homomorphism.cor4_59_resultant_copy E hOut1 hOut2 hS hI hO

/--
  [textbook/exercise4.85/theorem/rearrangement_isomorphic]
  Exercise 4.85: rearranging a connectable vector yields an isomorphic resultant.
-/
abbrev ex4_85_rearrangement_isomorphic {n : Nat} (SCR : SystemCouplingRecipe n)
    (F : Fin n ≃ Fin n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :=
  Homomorphism.ex4_85_rearrangement_isomorphic SCR F hOut

/--
  [textbook/exercise4.66/theorem/null_order_elimination]
  Exercise 4.66: eliminating the components of null order yields a homomorphic image.
-/
abbrev ex4_66_null_order_elimination {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :=
  Homomorphism.ex4_66_null_order_elimination E hOut

end Mbse.TextbookExercises.Ch04
