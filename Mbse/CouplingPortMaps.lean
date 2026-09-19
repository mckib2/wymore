import Mbse.Isomorphism
import Mbse.WymoreCouplingStructure

/-!
# Shared port-skeleton maps for coupling proofs

Common transport and intertwining lemmas used by Chapter 4 elaboration
([`Mbse.CouplingIsomorphism`](CouplingIsomorphism.lean)) and Chapter 5 induced
modes ([`Mbse.WymoreModeCoupling`](WymoreModeCoupling.lean)).  Both share the
same port indices and connectivity; only the component systems and the
portwise maps differ.
-/

namespace Homomorphism

open Homomorphism Mbse.Wymore

/-- Transport along two proofs of the same type equality agrees (definitional proof irrelevance). -/
lemma eq_rec_proof_irrel {A B : Type} {h1 h2 : A = B} (a : A) : h1 ▸ a = h2 ▸ a := by
  subst h1; rfl

/-- The connected output feeding an input port is unique, so `connectedOutput` is determined. -/
lemma connectedOutput_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR)
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) (hop : (op, ip) ∈ SCR.CSCR) :
    connectedOutput SCR ip hC = op :=
  SCR.connectivity.1.2 _ _ _ (connectedOutput_spec SCR ip hC) hop

/-- Transporting an application across a heterogeneous equality of functions. -/
lemma heq_fun_apply {A A' B B' : Type} (hA : A = A') (hB : B = B') {f : A → B} {g : A' → B'}
    (h : HEq f g) (v : A) : hB ▸ f v = g (hA ▸ v) := by
  subst hA; subst hB; cases h; rfl

/-- Transporting the readout of a *named* connected output port along its compatibility proof. -/
lemma conn_cast_congr {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR) (i : Fin n)
    (port : SCR.VSCR.Port i) (op1 op2 : Σ j, SCR.VSCR.OutPort j) (h : op1 = op2)
    (h1 : SCR.VSCR.OutPortVal op1.1 op1.2 = SCR.VSCR.PortVal i port)
    (h2 : SCR.VSCR.OutPortVal op2.1 op2.2 = SCR.VSCR.PortVal i port) :
    h1 ▸ rsyOutAt SCR hOut x op1 = h2 ▸ rsyOutAt SCR hOut x op2 := by
  subst h
  exact eq_rec_proof_irrel _

/-- Connected-port form of `rsy_component_input_fun` with the feeding output port named. -/
lemma rsy_component_input_of_conn {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : SCR.VSCR.Port i) (op : Σ j, SCR.VSCR.OutPort j)
    (hop : (op, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR)
    (hty : SCR.VSCR.OutPortVal op.1 op.2 = SCR.VSCR.PortVal i port) :
    rsy_component_input_fun SCR hOut i extIn x port = hty ▸ rsyOutAt SCR hOut x op := by
  classical
  have hC : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ CISCR SCR := ⟨op, hop⟩
  rw [rsy_component_input_ciscr _ _ _ _ _ _ hC]
  exact conn_cast_congr SCR hOut x i port _ op (connectedOutput_eq SCR _ hC op hop) _ hty

/--
Portwise readout intertwining for `AlwaysOutputs` systems: if whole-output maps
preserve readout and act portwise, each port projection intertwines.
-/
theorem alwaysOutputs_port_readout
    {SZ1 IZ1 OutPort : Type} {Val1 Val2 : OutPort → Type} {SZ2 IZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 ((q : OutPort) → Val1 q))
    (Z2 : DiscreteSystem SZ2 IZ2 ((q : OutPort) → Val2 q))
    (HS : SZ2 → SZ1)
    (HO : ((q : OutPort) → Val2 q) → ((q : OutPort) → Val1 q))
    (outPorts : PreservesPorts (Equiv.refl OutPort) HO)
    (hOut1 : AlwaysOutputs Z1) (hOut2 : AlwaysOutputs Z2)
    (hread : ∀ y, (Z2.RZ y).map HO = Z1.RZ (HS y))
    (y : SZ2) (q : OutPort) :
    outPorts.port q (componentReadoutAt Z2 hOut2 q y) =
      componentReadoutAt Z1 hOut1 q (HS y) := by
  classical
  have h2 : Z2.RZ y = some (Classical.choose (hOut2 y)) :=
    Classical.choose_spec (hOut2 y)
  have h1 : Z1.RZ (HS y) = some (Classical.choose (hOut1 (HS y))) :=
    Classical.choose_spec (hOut1 (HS y))
  have hmap := hread y
  rw [h2, h1] at hmap
  have hval : HO (Classical.choose (hOut2 y)) = Classical.choose (hOut1 (HS y)) :=
    Option.some_injective _ hmap
  have hproj : HO (Classical.choose (hOut2 y)) q =
      outPorts.port q (Classical.choose (hOut2 y) q) :=
    outPorts.proj _ q
  show outPorts.port q (Classical.choose (hOut2 y) q) = _
  rw [← hproj, hval]
  rfl

/--
Recipe with the same port indices and connectivity as `SCR`, but with
replacement component systems `Z'`.
-/
def sharedSkeletonRecipe {n : Nat} (SCR : SystemCouplingRecipe n)
    {SZ' : Fin n → Type}
    {PVal' : (i : Fin n) → SCR.VSCR.Port i → Type}
    {OVal' : (i : Fin n) → SCR.VSCR.OutPort i → Type}
    (Z' : (i : Fin n) → DiscreteSystem (SZ' i)
      ((p : SCR.VSCR.Port i) → PVal' i p)
      ((q : SCR.VSCR.OutPort i) → OVal' i q))
    (distinct' : ∀ i j, i ≠ j → ¬ HEq (Z' i) (Z' j))
    (compat' : ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR → OVal' op.1 op.2 = PVal' ip.1 ip.2) :
    SystemCouplingRecipe n where
  VSCR :=
    { SZ := SZ', Port := SCR.VSCR.Port, PortVal := PVal'
      OutPort := SCR.VSCR.OutPort, OutPortVal := OVal'
      Z := Z', distinct := distinct' }
  CSCR := SCR.CSCR
  connectivity :=
    ⟨SCR.connectivity.1, SCR.connectivity.2.1, SCR.connectivity.2.2.1, compat'⟩

/--
Resolved-input intertwining for two recipes that share `Port`, `OutPort`, and
`CSCR` literally.  Port maps act through `PreservesPorts` and matched connected
ports identify via `HEq`.
-/
theorem sharedSkeleton_component_input
    {n : Nat} {SCR : SystemCouplingRecipe n}
    {SZ' : Fin n → Type}
    {PVal' : (i : Fin n) → SCR.VSCR.Port i → Type}
    {OVal' : (i : Fin n) → SCR.VSCR.OutPort i → Type}
    (Z' : (i : Fin n) → DiscreteSystem (SZ' i)
      ((p : SCR.VSCR.Port i) → PVal' i p)
      ((q : SCR.VSCR.OutPort i) → OVal' i q))
    (distinct' : ∀ i j, i ≠ j → ¬ HEq (Z' i) (Z' j))
    (compat' : ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR → OVal' op.1 op.2 = PVal' ip.1 ip.2)
    (HS : ∀ i, SZ' i → SCR.VSCR.SZ i)
    (HI : ∀ i, ((p : SCR.VSCR.Port i) → PVal' i p) →
      ((p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p))
    (HO : ∀ i, ((q : SCR.VSCR.OutPort i) → OVal' i q) →
      ((q : SCR.VSCR.OutPort i) → SCR.VSCR.OutPortVal i q))
    (inPorts : ∀ i, PreservesPorts (Equiv.refl (SCR.VSCR.Port i)) (HI i))
    (outPorts : ∀ i, PreservesPorts (Equiv.refl (SCR.VSCR.OutPort i)) (HO i))
    (matched : ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR → HEq ((outPorts op.1).port op.2) ((inPorts ip.1).port ip.2))
    (hread : ∀ i y, ((Z' i).RZ y).map (HO i) = (SCR.VSCR.Z i).RZ (HS i y))
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut' : ∀ k, AlwaysOutputs (Z' k))
    (i : Fin n)
    (e : rsy_IZ (sharedSkeletonRecipe SCR Z' distinct' compat'))
    (y : rsy_SZ (sharedSkeletonRecipe SCR Z' distinct' compat')) :
    HI i (rsy_component_input_fun (sharedSkeletonRecipe SCR Z' distinct' compat')
        hOut' i e y) =
      rsy_component_input_fun SCR hOut i
        (fun ip => (inPorts ip.val.1).port ip.val.2 (e ip))
        (fun k => HS k (y k)) := by
  classical
  let SCR' := sharedSkeletonRecipe SCR Z' distinct' compat'
  funext port
  have hproj :
      HI i (rsy_component_input_fun SCR' hOut' i e y) port =
        (inPorts i).port port (rsy_component_input_fun SCR' hOut' i e y port) :=
    (inPorts i).proj _ port
  rw [hproj]
  rsy_port_cases SCR, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) with hU
  · rw [rsy_component_input_uiscr SCR' hOut' i e y port hU,
      rsy_component_input_uiscr SCR hOut i _ _ port hU]
    rfl
  · have hC : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ CISCR SCR :=
      (not_mem_uiscr_iff_mem_ciscr SCR _).mp hU
    set op := connectedOutput SCR ⟨i, port⟩ hC with hopdef
    have hspec : (op, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR :=
      connectedOutput_spec SCR ⟨i, port⟩ hC
    have hty' : SCR'.VSCR.OutPortVal op.1 op.2 = SCR'.VSCR.PortVal i port :=
      compat' op ⟨i, port⟩ hspec
    have htyS : SCR.VSCR.OutPortVal op.1 op.2 = SCR.VSCR.PortVal i port :=
      SCR.connectivity.2.2.2 op ⟨i, port⟩ hspec
    rw [rsy_component_input_of_conn SCR' hOut' i e y port op hspec hty',
      rsy_component_input_of_conn SCR hOut i _ _ port op hspec htyS]
    have hreadout :
        (outPorts op.1).port op.2 (rsyOutAt SCR' hOut' y op) =
          rsyOutAt SCR hOut (fun k => HS k (y k)) op := by
      obtain ⟨j, q⟩ := op
      simpa [rsyOutAt_eq_componentReadoutAt] using
        alwaysOutputs_port_readout (SCR.VSCR.Z j) (Z' j) (HS j) (HO j)
          (outPorts j) (hOut j) (hOut' j) (hread j) (y j) q
    rw [← hreadout]
    exact (heq_fun_apply hty' htyS (matched op ⟨i, port⟩ hspec)
      (rsyOutAt SCR' hOut' y op)).symm

/-! ## Recipe equality transport for resultants -/

/--
Transport a homomorphic-image witness along an equality of coupling recipes.
Used when an elaboration recipe is identified with an induced mode recipe
(`elabRecipe E = sysmoscr D`).
-/
noncomputable def moveResultantHom {n : Nat} {Sf If Of : Type}
    {Zfun : DiscreteSystem Sf If Of}
    {SCR1 SCR2 : SystemCouplingRecipe n}
    (h : SCR1 = SCR2)
    (h1 : ∀ i, AlwaysOutputs (SCR1.VSCR.Z i))
    (h2 : ∀ i, AlwaysOutputs (SCR2.VSCR.Z i))
    (hom : HomomorphicImageWitness Zfun (rsy SCR1 h1)) :
    HomomorphicImageWitness Zfun (rsy SCR2 h2) := by
  subst h
  exact hom

/-!
## Def 3.97 resultant packaging (historical note)

Exercise 5.142 previously exposed a Prop `DiscreteSystemStateReflection` for
injectivity of `DiscreteSystem` in its state argument, needed when Def 3.97 used
only `HEq Z (rsy SCR _)`.  The definition now uses `IsResultantOf` (type-parameter
equalities + dynamics) and `IsSubrecipeOf.sz`, so that card transport is
definitional and no reflection hypothesis remains.  See
[`Mbse.Wymore.IsResultantOf`](WymoreCouplingStructure.lean) and
[`Mbse.TextbookExercises.Ch05`](TextbookExercises/Ch05.lean).
-/
abbrev DiscreteSystemStateReflectionDoc : String :=
  "Historical: DiscreteSystemStateReflection was the HEq-era Ex 5.142 hyp; " ++
    "superseded by IsResultantOf / IsSubrecipeOf.sz (see WymoreCouplingStructure.lean)"

end Homomorphism
