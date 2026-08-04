import Mbse.Isomorphism

/-!
# Chapter 4 — homomorphism algebra, isomorphisms and copies

Exercise/theorem aliases for the Chapter 4 algebraic results proved in
[`Mbse.Isomorphism`](../Isomorphism.lean): Theorem 4.31, Theorem 4.38, Theorem 4.45,
Exercises 4.80, 4.81, 4.82 and 4.84.

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

end Mbse.TextbookExercises.Ch04
