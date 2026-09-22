import Mbse.PartialDynamicsHomFragment
import Mbse.WymoreRequirements
import Mbse.WymoreImplementation
import Mbse.WymoreTechnology
import Mbse.WymoreTechnologyImpl
import Mbse.TuringCoupling
import Mbse.RunLengthMachine

/-!
# Assertional Cotyledon Bridge

Connects the paper's assertional dynamics-encoding fragment (`SystemSatisfiesPartialDynamicsHom`)
directly to Wayne Wymore's authentic Tricotyledon Theory of System Design (T3SD):
- Chapter 6: Functionality Cotyledon `CTL(IOR) = FSR(IOR)` and `SatisfiesIOR`.
- Chapter 5: Implementation of system designs (`Implements`, `IMPSY`).
- Chapter 7: Technology (`Technology`), Buildability Cotyledon `CTL(TYR) = BSR(TYR)`,
  and Implementability Cotyledon `CTL(IOR, TYR) = ISR(IOR, TYR)`.

## Theoretical Spine
1. An Input/Output Requirement `IOR` specifies pure boundary trajectory behavior.
2. An engineer may specify functional intent directly via temporal properties over I/O, or
   compile an architectural reference model `Z_spec` into `Φ_dyn(Z_spec)`.
3. Satisfaction of `Φ_dyn(Z_spec)` is equivalent to existence of a Wymore system homomorphism
   (`partialDynamicsHom_iff_hom`).
4. Theorem 6.58 (`himsy_idIO_satisfies_iff`) transfers `SatisfiesIOR` only when the witnessing
   homomorphism is the identity on both boundary alphabets. The homomorphism is extracted from
   `Φ`; the identity equations are extra hypotheses, not a consequence of `Φ` alone.
5. For non-identity port maps the same trajectory projection is the transported requirement
   `himio` (Definition 6.72), not Theorem 6.58.
6. `Φ` yields Chapter 5 `Implements`. Paired with a buildable design that is an element of
   `BSR(TYR)`, the result is an `ImplementableSystemDesign`: the formal implementability cotyledon.
   Informally that cotyledon is the overlap of functionality and buildability; the types differ,
   so the formal object is the pairing, not a set-theoretic intersection.
-/

namespace AssertionalCotyledonBridge

open PartialDynamicsHomFragment
open WymoreRequirements
open WymoreImplementation
open WymoreTechnology
open TuringCoupling
open Homomorphism
open Mbse.Wymore
open Classical

universe u

/-! ## 1. Bridge to Chapter 6: Functionality Cotyledon ($CTL(IOR) = FSR(IOR)$) -/

/--
If `Z_spec` satisfies `IOR`, and `Z_impl` satisfies the dynamics-encoding fragment of `Z_spec`
via a homomorphism with identity on input/output alphabets, then `Z_impl` satisfies `IOR`.

This formally connects assertional satisfaction of `Φ_dyn` to Wymore Theorem 6.58.
-/
theorem satisfies_ior_of_partialDynamicsHom_witness
    {S1 S2 IR OR : Type}
    {Z_spec : DiscreteSystem S1 IR OR} {Z_impl : DiscreteSystem S2 IR OR}
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (hHI : w.HI = id) (hHO : w.HO = id)
    (IOR : InputOutputRequirement IR OR) (DSZ_impl : S2) (T : Set Time)
    (hSpecSat : SatisfiesIOR Z_spec IOR (w.HS DSZ_impl) T) :
    SatisfiesIOR Z_impl IOR DSZ_impl T := by
  have hIff := himsy_idIO_satisfies_iff w hHI hHO DSZ_impl T IOR
  exact hIff.mpr hSpecSat

/--
Bi-implication form: on identical boundary I/O alphabets, satisfaction of `IOR` by `Z_impl`
is equivalent to satisfaction by `Z_spec` at the projected initial state.
-/
theorem satisfies_ior_iff_of_partialDynamicsHom_witness
    {S1 S2 IR OR : Type}
    {Z_spec : DiscreteSystem S1 IR OR} {Z_impl : DiscreteSystem S2 IR OR}
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (hHI : w.HI = id) (hHO : w.HO = id)
    (IOR : InputOutputRequirement IR OR) (DSZ_impl : S2) (T : Set Time) :
    SatisfiesIOR Z_impl IOR DSZ_impl T ↔
      SatisfiesIOR Z_spec IOR (w.HS DSZ_impl) T :=
  himsy_idIO_satisfies_iff w hHI hHO DSZ_impl T IOR

/-- The homomorphism whose existence is `Φ`. -/
noncomputable def witnessOfPhi
    {S1 I1 O1 S2 I2 O2 : Type}
    {Z_spec : DiscreteSystem S1 I1 O1} {Z_impl : DiscreteSystem S2 I2 O2}
    (hPhi : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl) :
    HomomorphicImageWitness Z_spec Z_impl :=
  Classical.choice (hom_of_partialDynamicsHom hPhi)

/--
Identity-boundary path. Extract the homomorphism from `Φ` and apply Theorem 6.58.
The identity equations are hypotheses on that extracted witness: `Φ` alone does not
force `HI = HO = id`.
-/
theorem satisfies_ior_of_phi_idIO
    {S1 S2 IR OR : Type}
    {Z_spec : DiscreteSystem S1 IR OR} {Z_impl : DiscreteSystem S2 IR OR}
    (hPhi : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl)
    (hHI : (witnessOfPhi hPhi).HI = id) (hHO : (witnessOfPhi hPhi).HO = id)
    (IOR : InputOutputRequirement IR OR) (DSZ_impl : S2) (T : Set Time)
    (hSpecSat : SatisfiesIOR Z_spec IOR ((witnessOfPhi hPhi).HS DSZ_impl) T) :
    SatisfiesIOR Z_impl IOR DSZ_impl T :=
  satisfies_ior_of_partialDynamicsHom_witness (witnessOfPhi hPhi) hHI hHO IOR DSZ_impl T hSpecSat

/--
Transported IOR. When the port maps are not identities, satisfaction of the pushed
requirement `himio IOR HI HO` on the reference transfers to `IOR` on the elaboration
(the same trajectory projection as Theorem 6.58, without requiring `HI = HO = id`).
-/
theorem satisfies_ior_transported
    {S1 I1 O1 S2 I2 O2 : Type}
    {Z_spec : DiscreteSystem S1 I1 O1} {Z_impl : DiscreteSystem S2 I2 O2}
    (w : HomomorphicImageWitness Z_spec Z_impl)
    (hHIinj : Function.Injective w.HI) (hHOinj : Function.Injective w.HO)
    (IOR : InputOutputRequirement I2 O2) (DSZ : S2) (T : Set Time)
    (hSat : SatisfiesIOR Z_spec (himio IOR w.HI w.HO) (w.HS DSZ) T) :
    SatisfiesIOR Z_impl IOR DSZ T :=
  himio_himsy_reverse_claim IOR w hHIinj hHOinj DSZ T hSat

/-! ## 2. Bridge to Chapter 5: Implementation of System Designs (`Implements`) -/

/--
Every system satisfying the dynamics-encoding fragment implements the reference system
in the sense of Wymore Definition 5.71.
-/
theorem implements_of_partialDynamicsHom
    {S1 I1 O1 S2 I2 O2 : Type}
    {Z_spec : DiscreteSystem S1 I1 O1} {Z_impl : DiscreteSystem S2 I2 O2}
    (hPhi : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl) :
    Nonempty (Implements Z_spec Z_impl) := by
  have hHom := hom_of_partialDynamicsHom hPhi
  obtain ⟨w⟩ := hHom
  exact ⟨Implements.ofHomomorphicImage w⟩

/-! ## 3. Bridge to Chapter 7: Implementability Cotyledon ($CTL(IOR, TYR) = ISR$) -/

/-- An implementable design projects to its functionality-cotyledon component. -/
def fsr_of_isr {IR OR : Type} {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (d : ImplementableSystemDesign IOR TYR) : FunctionalSystemDesign IOR :=
  d.fsd

/-- An implementable design projects to its buildability-cotyledon component. -/
def bsr_of_isr {IR OR : Type} {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (d : ImplementableSystemDesign IOR TYR) : BuildableSystemDesign TYR where
  n := d.n
  SCR := d.SCR
  hOut := d.hOut
  SZ := d.SZ2
  IZ := d.IZ2
  OZ := d.OZ2
  Z := d.Z2
  buildable := d.buildable

/--
Given a functional system design in `FSR(IOR)` and a buildable system design in `BSR(TYR)`,
if the buildable system satisfies the compiled dynamics fragment of the functional system,
then they together form an implementable system design in `CTL(IOR, TYR) = ISR(IOR, TYR)`.
-/
def implementableDesignOfPartialDynamicsHom
    {IR OR : Type} {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (fsd : FunctionalSystemDesign IOR)
    {n : Nat} (SCR : SystemCouplingRecipe n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    {SZ2 IZ2 OZ2 : Type} (Z2 : DiscreteSystem SZ2 IZ2 OZ2)
    (hBuild : IsBuildableWith TYR SCR hOut Z2)
    (w : HomomorphicImageWitness fsd.Z Z2) :
    ImplementableSystemDesign IOR TYR where
  fsd := fsd
  n := n
  SCR := SCR
  hOut := hOut
  SZ2 := SZ2
  IZ2 := IZ2
  OZ2 := OZ2
  Z2 := Z2
  buildable := hBuild
  impl := Implements.ofHomomorphicImage w

/--
Existence form: assertional satisfaction `SystemSatisfiesPartialDynamicsHom` between a
functional design and a buildable design establishes nonemptiness of `CTL(IOR, TYR)`.
-/
theorem ctl_ior_tyr_nonempty_of_partialDynamicsHom
    {IR OR : Type} {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (fsd : FunctionalSystemDesign IOR)
    {n : Nat} (SCR : SystemCouplingRecipe n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    {SZ2 IZ2 OZ2 : Type} (Z2 : DiscreteSystem SZ2 IZ2 OZ2)
    (hBuild : IsBuildableWith TYR SCR hOut Z2)
    (hPhi : SystemSatisfiesPartialDynamicsHom fsd.Z Z2) :
    Nonempty (ImplementableSystemDesign IOR TYR) := by
  have hHom := hom_of_partialDynamicsHom hPhi
  obtain ⟨w⟩ := hHom
  exact ⟨implementableDesignOfPartialDynamicsHom fsd SCR hOut Z2 hBuild w⟩

/-! ## 4. Case Study Technology: Turing Machine in $BSR(TYR)$ and $CTL(IOR, TYR)$ -/

/--
The discrete technology for the Turing machine case study: contains the tape zone and control zone.
-/
def tmTechnology (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ) : Technology :=
  Technology.mk
    { AnyDiscreteSystem.of ((tmSCR Γ Λ M).VSCR.Z 0),
      AnyDiscreteSystem.of ((tmSCR Γ Λ M).VSCR.Z 1) }
    ⟨AnyDiscreteSystem.of ((tmSCR Γ Λ M).VSCR.Z 0), by simp⟩

/--
Every component of the Turing machine coupling recipe belongs to `tmTechnology`.
-/
theorem tm_vscr_subset_technology (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) :
    VSCRSubsetTechnology (tmSCR Γ Λ M).VSCR (tmTechnology Γ Λ M) := by
  intro i
  fin_cases i
  · apply memTechnology_of
    exact Or.inl rfl
  · apply memTechnology_of
    exact Or.inr rfl

/--
The coupled Turing machine resultant is buildable in `tmTechnology`.
-/
theorem tm_resultant_is_buildable_with (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) :
    IsBuildableWith (tmTechnology Γ Λ M) (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)
      (tmResultant Γ Λ M) := by
  refine ⟨tm_vscr_subset_technology Γ Λ M, ?_⟩
  exact IsResultantOf.of_rsy (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)

/--
The coupled Turing machine resultant belongs to the Buildability Cotyledon `BSR(tmTechnology)`.
-/
noncomputable def tm_resultant_in_bsr (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) :
    BuildableSystemDesign (tmTechnology Γ Λ M) where
  n := 2
  SCR := tmSCR Γ Λ M
  hOut := tmSCR_alwaysOutputs Γ Λ M
  SZ := rsy_SZ (tmSCR Γ Λ M)
  IZ := rsy_IZ (tmSCR Γ Λ M)
  OZ := rsy_OZ (tmSCR Γ Λ M)
  Z := tmResultant Γ Λ M
  buildable := tm_resultant_is_buildable_with Γ Λ M

/--
NormIO parameter for the monolithic Turing machine reference system from an initial configuration.
-/
noncomputable def tmReferenceNormIOParam (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ)
    (x0 : TMConfig Γ Λ) (olr : OperationalLength) (F : Set (ITZ (Option Λ)))
    (hF : F.Nonempty) : NormIOParam where
  Z := tmReference Γ Λ M
  x := x0
  olr := olr
  F := F
  F_nonempty := hF
  hOut := tmReference_alwaysOutputs Γ Λ M

/--
The monolithic reference system is a Functional System Design in `FSR(normIO)`.
-/
noncomputable def tmReference_fsd (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ)
    (x0 : TMConfig Γ Λ) (olr : OperationalLength) (F : Set (ITZ (Option Λ)))
    (hF : F.Nonempty) :
    FunctionalSystemDesign (normIO (tmReferenceNormIOParam Γ Λ M x0 olr F hF)) where
  S := TMConfig Γ Λ
  Z := tmReference Γ Λ M
  DSZ := x0
  TSZ := timeScale olr
  satisfies := normIO_members_in_fsr (tmReferenceNormIOParam Γ Λ M x0 olr F hF)
    (timeScale_nonempty olr) (fun _ h => h)

/--
The coupled two-zone resultant, certified by `SystemSatisfiesPartialDynamicsHom` rather than by
passing the homomorphism in by hand, is an implementable system design.
-/
noncomputable def tm_coupled_in_isr (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) (x0 : TMConfig Γ Λ) (olr : OperationalLength)
    (F : Set (ITZ (Option Λ))) (hF : F.Nonempty) :
    ImplementableSystemDesign (normIO (tmReferenceNormIOParam Γ Λ M x0 olr F hF))
      (tmTechnology Γ Λ M) :=
  Classical.choice <|
    ctl_ior_tyr_nonempty_of_partialDynamicsHom
      (tmReference_fsd Γ Λ M x0 olr F hF)
      (tmSCR Γ Λ M)
      (tmSCR_alwaysOutputs Γ Λ M)
      (tmResultant Γ Λ M)
      (tm_resultant_is_buildable_with Γ Λ M)
      (tmResultant_satisfies_reference_fragment Γ Λ M)

/-! ## Run-length encoding in the implementability cotyledon -/

open RunLengthMachine

/--
The wired four-component resultant implements the pipeline-aware run-length requirement.
Membership is obtained from `SystemSatisfiesPartialDynamicsHom`, not from a hand-supplied
homomorphism. Theorem 6.58 is not used: the boundary maps are projections.
-/
noncomputable def rle_in_isr : ImplementableSystemDesign pipelineIOR rleTechnology :=
  Classical.choice <|
    ctl_ior_tyr_nonempty_of_partialDynamicsHom
      pipelineRef_fsd
      rleSCR
      rle_hOut
      rleResultant
      rle_resultant_is_buildable
      rleResultant_satisfies_pipeline_fragment

end AssertionalCotyledonBridge
