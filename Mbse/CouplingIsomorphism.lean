import Mbse.Isomorphism
import Mbse.WymoreCouplingStructure

/-!
# Chapter 4: isomorphisms between system resultants

Coupling-level Chapter 4 results, building on the resultant machinery `rsy` of Chapter 3 and the
homomorphism/copy algebra of [`Mbse.Isomorphism`](Isomorphism.lean):

* Exercise 4.85 — rearranging a connectable vector by a permutation `F` of the component indices,
  keeping the same connectivity, preserves `UISCR` and `UOSCR` and yields an isomorphic resultant.
* Theorem 4.56 — if every component of one recipe is a port-preserving homomorphic image of the
  corresponding component of another, and the connectivities agree with matched port
  homomorphisms, then the resultants are port-preserving homomorphic images.
* Corollary 4.59 — the same statement with "copy" in place of "homomorphic image".
* Exercise 4.66 — deleting the components of null order from a coupling recipe leaves `UISCR` and
  `UOSCR` unchanged and makes the new resultant a homomorphic image of the original one.
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

/-! ## Rearranging a connectable vector -/

/-- [textbook/exercise4.85/definition/rearranged_vector] `VSCR$ = (Z_F(1), …, Z_F(n))`. -/
def reindexVector {n : Nat} (V : PortSystemVector n) (F : Fin n ≃ Fin n) :
    PortSystemVector n where
  SZ := fun i => V.SZ (F i)
  Port := fun i => V.Port (F i)
  PortVal := fun i => V.PortVal (F i)
  OutPort := fun i => V.OutPort (F i)
  OutPortVal := fun i => V.OutPortVal (F i)
  Z := fun i => V.Z (F i)
  distinct := fun i j hij => V.distinct (F i) (F j) fun h => hij (F.injective h)

/-- Renaming of tagged output ports induced by the rearrangement. -/
def reindexOutTag {n : Nat} (V : PortSystemVector n) (F : Fin n ≃ Fin n) :
    (Σ i, (reindexVector V F).OutPort i) ≃ (Σ j, V.OutPort j) :=
  Equiv.sigmaCongrLeft F

/-- Renaming of tagged input ports induced by the rearrangement. -/
def reindexInTag {n : Nat} (V : PortSystemVector n) (F : Fin n ≃ Fin n) :
    (Σ i, (reindexVector V F).Port i) ≃ (Σ j, V.Port j) :=
  Equiv.sigmaCongrLeft F

/-- [textbook/exercise4.85/definition/rearranged_connectivity] `CSCR$ = CSCR`, read through the renaming. -/
def reindexCSCR {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    Set ((Σ i, (reindexVector SCR.VSCR F).OutPort i) × (Σ i, (reindexVector SCR.VSCR F).Port i)) :=
  { p | (reindexOutTag SCR.VSCR F p.1, reindexInTag SCR.VSCR F p.2) ∈ SCR.CSCR }

theorem reindex_connectivity {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    IsSystemConnectivity (reindexVector SCR.VSCR F) (reindexCSCR SCR F) := by
  obtain ⟨h11, hdom, hrng, hcompat⟩ := SCR.connectivity
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y1 y2 h1 h2
    exact (reindexInTag SCR.VSCR F).injective (h11.1 _ _ _ h1 h2)
  · intro x1 x2 y h1 h2
    exact (reindexOutTag SCR.VSCR F).injective (h11.2 _ _ _ h1 h2)
  · intro hall
    apply hdom
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : (reindexOutTag SCR.VSCR F).symm x ∈ { x | ∃ y, (x, y) ∈ reindexCSCR SCR F } := by
      rw [hall]; trivial
    refine ⟨reindexInTag SCR.VSCR F this.choose, ?_⟩
    have hy := this.choose_spec
    simpa [reindexCSCR, Equiv.apply_symm_apply] using hy
  · intro hall
    apply hrng
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : (reindexInTag SCR.VSCR F).symm y ∈ { y | ∃ x, (x, y) ∈ reindexCSCR SCR F } := by
      rw [hall]; trivial
    refine ⟨reindexOutTag SCR.VSCR F this.choose, ?_⟩
    have hx := this.choose_spec
    simpa [reindexCSCR, Equiv.apply_symm_apply] using hx
  · intro op ip hmem
    exact hcompat _ _ hmem

/-- [textbook/exercise4.85/definition/rearranged_recipe] `SCR$ = (VSCR$, CSCR$)`. -/
def reindexRecipe {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    SystemCouplingRecipe n where
  VSCR := reindexVector SCR.VSCR F
  CSCR := reindexCSCR SCR F
  connectivity := reindex_connectivity SCR F

/-! ## Port-set correspondence -/

theorem reindex_mem_ciscr {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (ip : Σ i, (reindexVector SCR.VSCR F).Port i) :
    ip ∈ CISCR (reindexRecipe SCR F) ↔ reindexInTag SCR.VSCR F ip ∈ CISCR SCR := by
  constructor
  · rintro ⟨op, hop⟩
    exact ⟨reindexOutTag SCR.VSCR F op, hop⟩
  · rintro ⟨op, hop⟩
    refine ⟨(reindexOutTag SCR.VSCR F).symm op, ?_⟩
    show (reindexOutTag SCR.VSCR F ((reindexOutTag SCR.VSCR F).symm op),
      reindexInTag SCR.VSCR F ip) ∈ SCR.CSCR
    rwa [Equiv.apply_symm_apply]

theorem reindex_mem_uiscr {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (ip : Σ i, (reindexVector SCR.VSCR F).Port i) :
    ip ∈ UISCR (reindexRecipe SCR F) ↔ reindexInTag SCR.VSCR F ip ∈ UISCR SCR :=
  not_congr (reindex_mem_ciscr SCR F ip)

theorem reindex_mem_coscr {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (op : Σ i, (reindexVector SCR.VSCR F).OutPort i) :
    op ∈ COSCR (reindexRecipe SCR F) ↔ reindexOutTag SCR.VSCR F op ∈ COSCR SCR := by
  constructor
  · rintro ⟨ip, hip⟩
    exact ⟨reindexInTag SCR.VSCR F ip, hip⟩
  · rintro ⟨ip, hip⟩
    refine ⟨(reindexInTag SCR.VSCR F).symm ip, ?_⟩
    show (reindexOutTag SCR.VSCR F op,
      reindexInTag SCR.VSCR F ((reindexInTag SCR.VSCR F).symm ip)) ∈ SCR.CSCR
    rwa [Equiv.apply_symm_apply]

theorem reindex_mem_uoscr {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (op : Σ i, (reindexVector SCR.VSCR F).OutPort i) :
    op ∈ UOSCR (reindexRecipe SCR F) ↔ reindexOutTag SCR.VSCR F op ∈ UOSCR SCR :=
  not_congr (reindex_mem_coscr SCR F op)

/-- [textbook/exercise4.85/theorem/uiscr_preserved] `UISCR = UISCR$`. -/
def reindexUnconnIn {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    UnconnInPort (reindexRecipe SCR F) ≃ UnconnInPort SCR :=
  Equiv.subtypeEquiv (reindexInTag SCR.VSCR F) (reindex_mem_uiscr SCR F)

/-- [textbook/exercise4.85/theorem/uoscr_preserved] `UOSCR = UOSCR$`. -/
def reindexUnconnOut {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    UnconnOutPort (reindexRecipe SCR F) ≃ UnconnOutPort SCR :=
  Equiv.subtypeEquiv (reindexOutTag SCR.VSCR F) (reindex_mem_uoscr SCR F)

/-! ## The isomorphism -/

def reindexHS {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (x : rsy_SZ SCR) : rsy_SZ (reindexRecipe SCR F) := fun i => x (F i)

def reindexHI {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (g : rsy_IZ SCR) : rsy_IZ (reindexRecipe SCR F) := fun ip => g (reindexUnconnIn SCR F ip)

def reindexHO {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (g : rsy_OZ SCR) : rsy_OZ (reindexRecipe SCR F) := fun op => g (reindexUnconnOut SCR F op)

theorem reindexHS_eq {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    reindexHS SCR F = (Equiv.piCongrLeft SCR.VSCR.SZ F).symm := rfl

theorem reindexHI_eq {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    reindexHI SCR F =
      (Equiv.piCongrLeft (fun jp : UnconnInPort SCR => SCR.VSCR.PortVal jp.val.1 jp.val.2)
        (reindexUnconnIn SCR F)).symm := rfl

theorem reindexHO_eq {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n) :
    reindexHO SCR F =
      (Equiv.piCongrLeft (fun jp : UnconnOutPort SCR => SCR.VSCR.OutPortVal jp.val.1 jp.val.2)
        (reindexUnconnOut SCR F)).symm := rfl

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

theorem reindex_component_input {n : Nat} (SCR : SystemCouplingRecipe n) (F : Fin n ≃ Fin n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : (reindexRecipe SCR F).VSCR.Port i) :
    rsy_component_input_fun (reindexRecipe SCR F) (fun k => hOut (F k)) i
        (reindexHI SCR F extIn) (reindexHS SCR F x) port =
      rsy_component_input_fun SCR hOut (F i) extIn x port := by
  classical
  by_cases hU : (⟨i, port⟩ : Σ j, (reindexRecipe SCR F).VSCR.Port j) ∈ UISCR (reindexRecipe SCR F)
  · have hU' : (⟨F i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ UISCR SCR :=
      (reindex_mem_uiscr SCR F _).mp hU
    rw [rsy_component_input_uiscr _ _ _ _ _ _ hU, rsy_component_input_uiscr _ _ _ _ _ _ hU']
    rfl
  · have hC : (⟨i, port⟩ : Σ j, (reindexRecipe SCR F).VSCR.Port j) ∈
        CISCR (reindexRecipe SCR F) := by
      simpa [UISCR, Set.mem_compl_iff] using hU
    set op1 := connectedOutput (reindexRecipe SCR F) ⟨i, port⟩ hC with hop1def
    have hspec : (op1, (⟨i, port⟩ : Σ j, (reindexRecipe SCR F).VSCR.Port j)) ∈
        (reindexRecipe SCR F).CSCR := connectedOutput_spec (reindexRecipe SCR F) ⟨i, port⟩ hC
    have hspec' : ((reindexOutTag SCR.VSCR F op1), (⟨F i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈
        SCR.CSCR := hspec
    have hty : SCR.VSCR.OutPortVal (F op1.1) op1.2 = SCR.VSCR.PortVal (F i) port :=
      SCR.connectivity.2.2.2 _ _ hspec'
    rw [rsy_component_input_of_conn (reindexRecipe SCR F) (fun k => hOut (F k)) i
          (reindexHI SCR F extIn) (reindexHS SCR F x) port op1 hspec hty,
        rsy_component_input_of_conn SCR hOut (F i) extIn x port
          (reindexOutTag SCR.VSCR F op1) hspec' hty]
    rfl

noncomputable def reindexIsomorphismWitness {n : Nat} (SCR : SystemCouplingRecipe n)
    (F : Fin n ≃ Fin n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    IsomorphismWitness (rsy (reindexRecipe SCR F) (fun k => hOut (F k))) (rsy SCR hOut) where
  HS := reindexHS SCR F
  HI := reindexHI SCR F
  HO := reindexHO SCR F
  HS_surjective := by
    rw [reindexHS_eq]; exact (Equiv.piCongrLeft _ F).symm.surjective
  HI_surjective := by
    rw [reindexHI_eq]; exact (Equiv.piCongrLeft _ (reindexUnconnIn SCR F)).symm.surjective
  HO_surjective := by
    rw [reindexHO_eq]; exact (Equiv.piCongrLeft _ (reindexUnconnOut SCR F)).symm.surjective
  HS_injective := by
    rw [reindexHS_eq]; exact (Equiv.piCongrLeft _ F).symm.injective
  HI_injective := by
    rw [reindexHI_eq]; exact (Equiv.piCongrLeft _ (reindexUnconnIn SCR F)).symm.injective
  HO_injective := by
    rw [reindexHO_eq]; exact (Equiv.piCongrLeft _ (reindexUnconnOut SCR F)).symm.injective
  preserves_transition := by
    intro x oi
    funext i
    have hfun : ∀ e : rsy_IZ SCR,
        rsy_component_input_fun (reindexRecipe SCR F) (fun k => hOut (F k)) i
            (reindexHI SCR F e) (reindexHS SCR F x) =
          rsy_component_input_fun SCR hOut (F i) e x :=
      fun e => funext fun port => reindex_component_input SCR F hOut i e x port
    cases oi with
    | none => rfl
    | some e =>
        show (SCR.VSCR.Z (F i)).NZ (x (F i))
            (some (rsy_component_input_fun SCR hOut (F i) e x)) = _
        rw [← hfun e]
        rfl
  preserves_readout := by intro x; rfl

/--
  [textbook/exercise4.85/theorem/rearrangement_isomorphic]
  Exercise 4.85: rearranging a connectable vector by `F` while keeping the same connectivity
  preserves `UISCR` and `UOSCR` and yields an isomorphic resultant.
-/
theorem ex4_85_rearrangement_isomorphic {n : Nat} (SCR : SystemCouplingRecipe n)
    (F : Fin n ≃ Fin n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    (∀ ip, ip ∈ UISCR (reindexRecipe SCR F) ↔ reindexInTag SCR.VSCR F ip ∈ UISCR SCR) ∧
      (∀ op, op ∈ UOSCR (reindexRecipe SCR F) ↔ reindexOutTag SCR.VSCR F op ∈ UOSCR SCR) ∧
      IsIsomorphicTo (rsy (reindexRecipe SCR F) (fun k => hOut (F k))) (rsy SCR hOut) :=
  ⟨reindex_mem_uiscr SCR F, reindex_mem_uoscr SCR F,
    ⟨reindexIsomorphismWitness SCR F hOut⟩⟩

/-! ## Theorem 4.56: componentwise port-preserving homomorphisms lift to the resultant -/

/-- Transporting an application across a heterogeneous equality of functions. -/
lemma heq_fun_apply {A A' B B' : Type} (hA : A = A') (hB : B = B') {f : A → B} {g : A' → B'}
    (h : HEq f g) (v : A) : hB ▸ f v = g (hA ▸ v) := by
  subst hA; subst hB; cases h; rfl

/--
  [textbook/theorem4.56/definition/componentwise_elaboration]
  The hypotheses of Theorem 4.56: an elaboration of every component of `SCR` over the *same* port
  skeleton, together with the port-preserving homomorphisms `HSᵢ`, `SHISᵢ`, `SHOSᵢ` and the
  matching condition `HOji = HImk` on connected pairs.

  Sharing the port index families `SCR.VSCR.Port` and `SCR.VSCR.OutPort` is exactly Def 4.27
  clause (i) together with the textbook's requirement that `(OiZj, IkZm) ∈ CSCR` if and only if
  `(OiZ$j, IkZ$m) ∈ CSCR$`: the two recipes carry literally the same connectivity set.
-/
structure ComponentwiseElaboration {n : Nat} (SCR : SystemCouplingRecipe n) where
  /-- State spaces of the elaborated components. -/
  SZ : Fin n → Type
  /-- Input port value sets of the elaborated components. -/
  PortVal : (i : Fin n) → SCR.VSCR.Port i → Type
  /-- Output port value sets of the elaborated components. -/
  OutPortVal : (i : Fin n) → SCR.VSCR.OutPort i → Type
  /-- [textbook/theorem4.56/component/elaborated_components] The components `Z$ᵢ`. -/
  Z : (i : Fin n) → DiscreteSystem (SZ i)
        ((p : SCR.VSCR.Port i) → PortVal i p) ((q : SCR.VSCR.OutPort i) → OutPortVal i q)
  /-- `VSCR$` is a connectable vector. -/
  distinct : ∀ i j, i ≠ j → ¬ HEq (Z i) (Z j)
  /-- [textbook/theorem4.56/component/component_homomorphism] `Zᵢ = HIMSY(Z$ᵢ, HSᵢ, HIᵢ, HOᵢ)`. -/
  hom : (i : Fin n) → HomomorphicImageWitness (SCR.VSCR.Z i) (Z i)
  /-- [textbook/theorem4.56/component/shis] `SHISᵢ`: `HIᵢ` acts portwise. -/
  inPorts : (i : Fin n) → PreservesPorts (Equiv.refl (SCR.VSCR.Port i)) (hom i).HI
  /-- [textbook/theorem4.56/component/shos] `SHOSᵢ`: `HOᵢ` acts portwise. -/
  outPorts : (i : Fin n) → PreservesPorts (Equiv.refl (SCR.VSCR.OutPort i)) (hom i).HO
  /-- Connected ports of `SCR$` carry matching value sets, so `CSCR$ = CSCR` is a connectivity. -/
  compat : ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR → OutPortVal op.1 op.2 = PortVal ip.1 ip.2
  /-- [textbook/theorem4.56/requirement/matched_port_homomorphisms] `HOji = HImk`. -/
  matched : ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR → HEq ((outPorts op.1).port op.2) ((inPorts ip.1).port ip.2)

/-- [textbook/theorem4.56/definition/elaborated_vector] `VSCR$ = (Z$1, …, Z$n)`. -/
def elabVector {n : Nat} {SCR : SystemCouplingRecipe n} (E : ComponentwiseElaboration SCR) :
    PortSystemVector n where
  SZ := E.SZ
  Port := SCR.VSCR.Port
  PortVal := E.PortVal
  OutPort := SCR.VSCR.OutPort
  OutPortVal := E.OutPortVal
  Z := E.Z
  distinct := E.distinct

/-- [textbook/theorem4.56/definition/elaborated_recipe] `SCR$ = (VSCR$, CSCR)`. -/
def elabRecipe {n : Nat} {SCR : SystemCouplingRecipe n} (E : ComponentwiseElaboration SCR) :
    SystemCouplingRecipe n where
  VSCR := elabVector E
  CSCR := SCR.CSCR
  connectivity :=
    ⟨SCR.connectivity.1, SCR.connectivity.2.1, SCR.connectivity.2.2.1,
      fun op ip h => E.compat op ip h⟩

/-- The two recipes have literally the same connected input ports. -/
theorem elabRecipe_ciscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR) : CISCR (elabRecipe E) = CISCR SCR := rfl

/-- [textbook/theorem4.56/theorem/uiscr_preserved] `UISCR$ = UISCR`. -/
theorem elabRecipe_uiscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR) : UISCR (elabRecipe E) = UISCR SCR := rfl

/-- [textbook/theorem4.56/theorem/uoscr_preserved] `UOSCR$ = UOSCR`. -/
theorem elabRecipe_uoscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR) : UOSCR (elabRecipe E) = UOSCR SCR := rfl

/-- Componentwise readouts intertwine with the port homomorphisms. -/
theorem elab_readout {n : Nat} {SCR : SystemCouplingRecipe n} (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (y : rsy_SZ (elabRecipe E)) (op : Σ i, SCR.VSCR.OutPort i) :
    (E.outPorts op.1).port op.2 (rsyOutAt (elabRecipe E) hOut2 y op) =
      rsyOutAt SCR hOut1 (fun i => (E.hom i).HS (y i)) op := by
  classical
  obtain ⟨i, q⟩ := op
  have h2 : (E.Z i).RZ (y i) = some (Classical.choose (hOut2 i (y i))) :=
    Classical.choose_spec (hOut2 i (y i))
  have h1 : (SCR.VSCR.Z i).RZ ((E.hom i).HS (y i)) =
      some (Classical.choose (hOut1 i ((E.hom i).HS (y i)))) :=
    Classical.choose_spec (hOut1 i ((E.hom i).HS (y i)))
  have hmap := (E.hom i).preserves_readout (y i)
  rw [h2, h1] at hmap
  have hval : (E.hom i).HO (Classical.choose (hOut2 i (y i))) =
      Classical.choose (hOut1 i ((E.hom i).HS (y i))) := Option.some.inj hmap
  have hproj : (E.hom i).HO (Classical.choose (hOut2 i (y i))) q =
      (E.outPorts i).port q (Classical.choose (hOut2 i (y i)) q) :=
    (E.outPorts i).proj _ q
  show (E.outPorts i).port q (Classical.choose (hOut2 i (y i)) q) = _
  rw [← hproj, hval]
  rfl

/-- Componentwise resolved inputs intertwine with the port homomorphisms. -/
theorem elab_component_input {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (i : Fin n) (e : rsy_IZ (elabRecipe E)) (y : rsy_SZ (elabRecipe E)) :
    (E.hom i).HI (rsy_component_input_fun (elabRecipe E) hOut2 i e y) =
      rsy_component_input_fun SCR hOut1 i
        (fun ip => (E.inPorts ip.val.1).port ip.val.2 (e ip))
        (fun k => (E.hom k).HS (y k)) := by
  classical
  funext port
  have hproj : (E.hom i).HI (rsy_component_input_fun (elabRecipe E) hOut2 i e y) port =
      (E.inPorts i).port port (rsy_component_input_fun (elabRecipe E) hOut2 i e y port) :=
    (E.inPorts i).proj _ port
  rw [hproj]
  by_cases hU : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ UISCR SCR
  · rw [rsy_component_input_uiscr (elabRecipe E) hOut2 i e y port hU,
      rsy_component_input_uiscr SCR hOut1 i _ _ port hU]
    rfl
  · have hC : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ CISCR SCR := by
      simpa [UISCR, Set.mem_compl_iff] using hU
    set op := connectedOutput SCR ⟨i, port⟩ hC with hopdef
    have hspec : (op, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR :=
      connectedOutput_spec SCR ⟨i, port⟩ hC
    have htyE : (elabRecipe E).VSCR.OutPortVal op.1 op.2 =
        (elabRecipe E).VSCR.PortVal i port := E.compat op ⟨i, port⟩ hspec
    have htyS : SCR.VSCR.OutPortVal op.1 op.2 = SCR.VSCR.PortVal i port :=
      SCR.connectivity.2.2.2 op ⟨i, port⟩ hspec
    rw [rsy_component_input_of_conn (elabRecipe E) hOut2 i e y port op hspec htyE,
      rsy_component_input_of_conn SCR hOut1 i _ _ port op hspec htyS]
    rw [← elab_readout E hOut1 hOut2 y op]
    exact (heq_fun_apply htyE htyS (E.matched op ⟨i, port⟩ hspec)
      (rsyOutAt (elabRecipe E) hOut2 y op)).symm

/--
  [textbook/theorem4.56/proof/resultant_homomorphism]
  The resultant homomorphism `HS = ×HSᵢ`, `HI` and `HO` acting portwise on the external ports.
-/
noncomputable def elabResultantWitness {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k)) :
    PortPreservingHomWitness (rsy SCR hOut1) (rsy (elabRecipe E) hOut2) where
  HS := fun y i => (E.hom i).HS (y i)
  HI := fun e ip => (E.inPorts ip.val.1).port ip.val.2 (e ip)
  HO := fun g op => (E.outPorts op.val.1).port op.val.2 (g op)
  HS_surjective := by
    intro x
    exact ⟨fun i => ((E.hom i).HS_surjective (x i)).choose,
      funext fun i => ((E.hom i).HS_surjective (x i)).choose_spec⟩
  HI_surjective := by
    intro f
    exact ⟨fun ip => ((E.inPorts ip.val.1).port_surjective ip.val.2 (f ip)).choose,
      funext fun ip => ((E.inPorts ip.val.1).port_surjective ip.val.2 (f ip)).choose_spec⟩
  HO_surjective := by
    intro f
    exact ⟨fun op => ((E.outPorts op.val.1).port_surjective op.val.2 (f op)).choose,
      funext fun op => ((E.outPorts op.val.1).port_surjective op.val.2 (f op)).choose_spec⟩
  preserves_transition := by
    intro y oj
    funext i
    cases oj with
    | none =>
        show (E.hom i).HS ((E.Z i).NZ (y i) none) = _
        exact (E.hom i).preserves_transition (y i) none
    | some e =>
        show (E.hom i).HS
            ((E.Z i).NZ (y i) (some (rsy_component_input_fun (elabRecipe E) hOut2 i e y))) = _
        rw [(E.hom i).preserves_transition (y i)
          (some (rsy_component_input_fun (elabRecipe E) hOut2 i e y))]
        show (SCR.VSCR.Z i).NZ ((E.hom i).HS (y i))
            (some ((E.hom i).HI (rsy_component_input_fun (elabRecipe E) hOut2 i e y))) = _
        rw [elab_component_input E hOut1 hOut2 i e y]
        rfl
  preserves_readout := by
    intro y
    show some (fun op : UnconnOutPort SCR =>
        (E.outPorts op.val.1).port op.val.2 (rsyOutAt (elabRecipe E) hOut2 y op.val)) = _
    exact congrArg some (funext fun op => elab_readout E hOut1 hOut2 y op.val)
  inIdx := Equiv.refl (UnconnInPort SCR)
  outIdx := Equiv.refl (UnconnOutPort SCR)
  inPorts :=
    { port := fun ip => (E.inPorts ip.val.1).port ip.val.2
      port_surjective := fun ip => (E.inPorts ip.val.1).port_surjective ip.val.2
      proj := fun _ _ => rfl }
  outPorts :=
    { port := fun op => (E.outPorts op.val.1).port op.val.2
      port_surjective := fun op => (E.outPorts op.val.1).port_surjective op.val.2
      proj := fun _ _ => rfl }

/--
  [textbook/theorem4.56/theorem/resultant_port_preserving_homomorphism]
  Theorem 4.56: the resultant of a coupling recipe each of whose components is a port-preserving
  homomorphic image of the corresponding component of another recipe with the same connectivity
  (and matched port homomorphisms on connected pairs) is a port-preserving homomorphic image of
  the resultant of the other recipe.
-/
theorem thm4_56_resultant_homomorphic_image {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k)) :
    UISCR (elabRecipe E) = UISCR SCR ∧ UOSCR (elabRecipe E) = UOSCR SCR ∧
      IsPortPreservingHomImage (rsy SCR hOut1) (rsy (elabRecipe E) hOut2) :=
  ⟨elabRecipe_uiscr E, elabRecipe_uoscr E, ⟨elabResultantWitness E hOut1 hOut2⟩⟩

/-! ## Corollary 4.59: componentwise copies lift to the resultant -/

/--
  [textbook/corollary4.59/proof/copy_witness]
  When every component homomorphism is in addition `1TO1`, the resultant homomorphism of
  Theorem 4.56 is a copy: `HS` is injective because it is a product of injections, and `HI`, `HO`
  are injective because they act portwise through injections.
-/
noncomputable def elabResultantCopyWitness {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (hS : ∀ i, Function.Injective (E.hom i).HS)
    (hI : ∀ (i : Fin n) (p : SCR.VSCR.Port i), Function.Injective ((E.inPorts i).port p))
    (hO : ∀ (i : Fin n) (q : SCR.VSCR.OutPort i), Function.Injective ((E.outPorts i).port q)) :
    CopyWitness (rsy SCR hOut1) (rsy (elabRecipe E) hOut2) where
  toIsomorphismWitness :=
    { toHomomorphicImageWitness :=
        (elabResultantWitness E hOut1 hOut2).toHomomorphicImageWitness
      HS_injective := fun _ _ h => funext fun i => hS i (congr_fun h i)
      HI_injective := fun _ _ h => funext fun ip => hI ip.val.1 ip.val.2 (congr_fun h ip)
      HO_injective := fun _ _ h => funext fun op => hO op.val.1 op.val.2 (congr_fun h op) }
  inIdx := Equiv.refl (UnconnInPort SCR)
  outIdx := Equiv.refl (UnconnOutPort SCR)
  inPorts := (elabResultantWitness E hOut1 hOut2).inPorts
  outPorts := (elabResultantWitness E hOut1 hOut2).outPorts

/--
  [textbook/corollary4.59/theorem/resultant_copy]
  Corollary 4.59: resultants of coupling recipes with the same number of components, the same
  connectivity and matched port homomorphisms, such that each pair of components are copies, are
  copies. (By Exercise 4.84 the copy relation is symmetric, so the direction of the statement is
  immaterial.)
-/
theorem cor4_59_resultant_copy {n : Nat} {SCR : SystemCouplingRecipe n}
    (E : ComponentwiseElaboration SCR)
    (hOut1 : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hOut2 : ∀ k, AlwaysOutputs ((elabRecipe E).VSCR.Z k))
    (hS : ∀ i, Function.Injective (E.hom i).HS)
    (hI : ∀ (i : Fin n) (p : SCR.VSCR.Port i), Function.Injective ((E.inPorts i).port p))
    (hO : ∀ (i : Fin n) (q : SCR.VSCR.OutPort i), Function.Injective ((E.outPorts i).port q)) :
    IsCopyOf (rsy SCR hOut1) (rsy (elabRecipe E) hOut2) :=
  ⟨elabResultantCopyWitness E hOut1 hOut2 hS hI hO⟩

/-! ## Exercise 4.66: deleting the components of null order -/

/--
  [textbook/exercise4.66/definition/retained_components]
  An enumeration `M = {Z_{i₁}, …, Z_{iₘ}}` of the components of `SCR` that are *not* of null
  order: `ι` is injective (textbook `{i₁, …, iₘ} ⊆ IJS[1, n]` lists distinct indices), every
  listed component has an order, and every component with an order is listed.
-/
structure NullOrderElimination {n : Nat} (SCR : SystemCouplingRecipe n) (m : Nat) where
  /-- The retained component indices `i₁, …, iₘ`. -/
  ι : Fin m → Fin n
  inj : Function.Injective ι
  /-- Every retained component is of some order, i.e. not of null order. -/
  retained : ∀ i, ComponentHasOrder SCR (ι i)
  /-- Every component that is not of null order is retained. -/
  complete : ∀ k, ComponentHasOrder SCR k → ∃ i, ι i = k

/-- Deleted components are exactly the components of null order. -/
theorem NullOrderElimination.deleted_iff_null_order {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (k : Fin n) :
    (¬ ∃ i, E.ι i = k) ↔ ComponentNullOrder SCR k := by
  constructor
  · intro h hord
    exact h (E.complete k hord)
  · rintro hnull ⟨i, hi⟩
    exact hnull (hi ▸ E.retained i)

/-- A coupled pair of components makes each of them a neighbour of the other. -/
theorem hasSCRConnection_of_mem_cscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i) (h : (op, ip) ∈ SCR.CSCR) :
    HasSCRConnection SCR op.1 ip.1 ∧ HasSCRConnection SCR ip.1 op.1 := by
  constructor
  · intro hempty
    have hmem : (op, ip) ∈ SCRInterface SCR op.1 ip.1 := ⟨h, Or.inl ⟨rfl, rfl⟩⟩
    rw [hempty] at hmem
    exact hmem
  · intro hempty
    have hmem : (op, ip) ∈ SCRInterface SCR ip.1 op.1 := ⟨h, Or.inr ⟨rfl, rfl⟩⟩
    rw [hempty] at hmem
    exact hmem

/--
  [textbook/exercise4.66/proof/order_propagates]
  Being of some order propagates along a connection, so a component coupled to a retained
  component is itself retained: no connection of `CSCR` joins a deleted component to a kept one.
-/
theorem hasOrder_of_mem_cscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i) (h : (op, ip) ∈ SCR.CSCR) :
    (ComponentHasOrder SCR ip.1 → ComponentHasOrder SCR op.1) ∧
      (ComponentHasOrder SCR op.1 → ComponentHasOrder SCR ip.1) :=
  ⟨fun hip => componentHasOrder_of_connection SCR (hasSCRConnection_of_mem_cscr SCR op ip h).1 hip,
    fun hop => componentHasOrder_of_connection SCR (hasSCRConnection_of_mem_cscr SCR op ip h).2 hop⟩

/-- An unconnected input port belongs to a component of order 0, hence to a retained one. -/
theorem hasOrder_of_mem_uiscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ i, SCR.VSCR.Port i) (h : ip ∈ UISCR SCR) : ComponentHasOrder SCR ip.1 :=
  ⟨0, Or.inl ⟨ip.2, h⟩⟩

/-- An unconnected output port belongs to a component of order 0, hence to a retained one. -/
theorem hasOrder_of_mem_uoscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (op : Σ i, SCR.VSCR.OutPort i) (h : op ∈ UOSCR SCR) : ComponentHasOrder SCR op.1 :=
  ⟨0, Or.inr ⟨op.2, h⟩⟩

/-- [textbook/exercise4.66/definition/reduced_vector] `VSCR$ = (Z_{i₁}, …, Z_{iₘ}) ⊆ VSCR`. -/
def elimVector {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m) :
    PortSystemVector m where
  SZ := fun i => SCR.VSCR.SZ (E.ι i)
  Port := fun i => SCR.VSCR.Port (E.ι i)
  PortVal := fun i => SCR.VSCR.PortVal (E.ι i)
  OutPort := fun i => SCR.VSCR.OutPort (E.ι i)
  OutPortVal := fun i => SCR.VSCR.OutPortVal (E.ι i)
  Z := fun i => SCR.VSCR.Z (E.ι i)
  distinct := fun i j hij => SCR.VSCR.distinct (E.ι i) (E.ι j) fun h => hij (E.inj h)

/-- Renaming of a retained tagged output port back into `SCR`. -/
def elimOutTag {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m)
    (op : Σ i, (elimVector E).OutPort i) : Σ j, SCR.VSCR.OutPort j := ⟨E.ι op.1, op.2⟩

/-- Renaming of a retained tagged input port back into `SCR`. -/
def elimInTag {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m)
    (ip : Σ i, (elimVector E).Port i) : Σ j, SCR.VSCR.Port j := ⟨E.ι ip.1, ip.2⟩

theorem elimOutTag_injective {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : Function.Injective (elimOutTag E) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hij : i = j := E.inj (congrArg Sigma.fst h)
  subst hij
  have hpq : p = q := by simpa [elimOutTag] using h
  simp [hpq]

theorem elimInTag_injective {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : Function.Injective (elimInTag E) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hij : i = j := E.inj (congrArg Sigma.fst h)
  subst hij
  have hpq : p = q := by simpa [elimInTag] using h
  simp [hpq]

/-- Every tagged output port of a retained component comes from `VSCR$`. -/
theorem elimOutTag_surjective_of_hasOrder {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (op : Σ j, SCR.VSCR.OutPort j)
    (h : ComponentHasOrder SCR op.1) : ∃ op', elimOutTag E op' = op := by
  obtain ⟨k, q⟩ := op
  obtain ⟨i, hi⟩ := E.complete k h
  subst hi
  exact ⟨⟨i, q⟩, rfl⟩

/-- Every tagged input port of a retained component comes from `VSCR$`. -/
theorem elimInTag_surjective_of_hasOrder {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (ip : Σ j, SCR.VSCR.Port j)
    (h : ComponentHasOrder SCR ip.1) : ∃ ip', elimInTag E ip' = ip := by
  obtain ⟨k, p⟩ := ip
  obtain ⟨i, hi⟩ := E.complete k h
  subst hi
  exact ⟨⟨i, p⟩, rfl⟩

/--
  [textbook/exercise4.66/definition/reduced_connectivity]
  `CSCR$ = {(B, A) ∈ CSCR : both ports belong to components of `VSCR$`}`. By
  `hasOrder_of_mem_cscr` requiring one endpoint to be retained already forces the other, so this
  is the textbook's set.
-/
def elimCSCR {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m) :
    Set ((Σ i, (elimVector E).OutPort i) × (Σ i, (elimVector E).Port i)) :=
  { p | (elimOutTag E p.1, elimInTag E p.2) ∈ SCR.CSCR }

theorem elim_connectivity {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : IsSystemConnectivity (elimVector E) (elimCSCR E) := by
  obtain ⟨h11, _hdom, _hrng, hcompat⟩ := SCR.connectivity
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y1 y2 hy1 hy2
    exact elimInTag_injective E (h11.1 _ _ _ hy1 hy2)
  · intro x1 x2 y hx1 hx2
    exact elimOutTag_injective E (h11.2 _ _ _ hx1 hx2)
  · intro hall
    obtain ⟨op, hop⟩ := scr_has_unconnected_output_port SCR
    obtain ⟨op', hop'⟩ := elimOutTag_surjective_of_hasOrder E op (hasOrder_of_mem_uoscr SCR op hop)
    have hmem : op' ∈ { x | ∃ y, (x, y) ∈ elimCSCR E } := by rw [hall]; trivial
    obtain ⟨ip', hconn⟩ := hmem
    exact hop ⟨elimInTag E ip', hop' ▸ hconn⟩
  · intro hall
    obtain ⟨ip, hip⟩ := scr_has_unconnected_input_port SCR
    obtain ⟨ip', hip'⟩ := elimInTag_surjective_of_hasOrder E ip (hasOrder_of_mem_uiscr SCR ip hip)
    have hmem : ip' ∈ { y | ∃ x, (x, y) ∈ elimCSCR E } := by rw [hall]; trivial
    obtain ⟨op', hconn⟩ := hmem
    exact hip ⟨elimOutTag E op', hip' ▸ hconn⟩
  · intro op ip hmem
    exact hcompat _ _ hmem

/-- [textbook/exercise4.66/definition/reduced_recipe] `SCR$ = (VSCR$, CSCR$)`. -/
def elimRecipe {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m) :
    SystemCouplingRecipe m where
  VSCR := elimVector E
  CSCR := elimCSCR E
  connectivity := elim_connectivity E

theorem elim_mem_ciscr {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (ip : Σ i, (elimVector E).Port i) :
    ip ∈ CISCR (elimRecipe E) ↔ elimInTag E ip ∈ CISCR SCR := by
  constructor
  · rintro ⟨op, hop⟩
    exact ⟨elimOutTag E op, hop⟩
  · rintro ⟨op, hop⟩
    have hord : ComponentHasOrder SCR op.1 :=
      (hasOrder_of_mem_cscr SCR op (elimInTag E ip) hop).1 (E.retained ip.1)
    obtain ⟨op', hop'⟩ := elimOutTag_surjective_of_hasOrder E op hord
    exact ⟨op', by show (elimOutTag E op', elimInTag E ip) ∈ SCR.CSCR; rw [hop']; exact hop⟩

theorem elim_mem_coscr {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (op : Σ i, (elimVector E).OutPort i) :
    op ∈ COSCR (elimRecipe E) ↔ elimOutTag E op ∈ COSCR SCR := by
  constructor
  · rintro ⟨ip, hip⟩
    exact ⟨elimInTag E ip, hip⟩
  · rintro ⟨ip, hip⟩
    have hord : ComponentHasOrder SCR ip.1 :=
      (hasOrder_of_mem_cscr SCR (elimOutTag E op) ip hip).2 (E.retained op.1)
    obtain ⟨ip', hip'⟩ := elimInTag_surjective_of_hasOrder E ip hord
    exact ⟨ip', by show (elimOutTag E op, elimInTag E ip') ∈ SCR.CSCR; rw [hip']; exact hip⟩

/-- [textbook/exercise4.66/theorem/uiscr_preserved] `UISCR$` is `UISCR` read through `ι`. -/
theorem elim_mem_uiscr {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (ip : Σ i, (elimVector E).Port i) :
    ip ∈ UISCR (elimRecipe E) ↔ elimInTag E ip ∈ UISCR SCR :=
  not_congr (elim_mem_ciscr E ip)

/-- [textbook/exercise4.66/theorem/uoscr_preserved] `UOSCR$` is `UOSCR` read through `ι`. -/
theorem elim_mem_uoscr {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (op : Σ i, (elimVector E).OutPort i) :
    op ∈ UOSCR (elimRecipe E) ↔ elimOutTag E op ∈ UOSCR SCR :=
  not_congr (elim_mem_coscr E op)

/-- `IZ@$ = IZ@`: the unconnected input ports of `SCR` all sit on retained components. -/
noncomputable def elimUnconnIn {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : UnconnInPort (elimRecipe E) ≃ UnconnInPort SCR :=
  Equiv.ofBijective (fun ip => ⟨elimInTag E ip.val, (elim_mem_uiscr E ip.val).mp ip.property⟩)
    ⟨fun ip1 ip2 h => Subtype.ext (elimInTag_injective E (congrArg Subtype.val h)),
      by
        rintro ⟨ip, hU⟩
        obtain ⟨ip', hip'⟩ := elimInTag_surjective_of_hasOrder E ip (hasOrder_of_mem_uiscr SCR ip hU)
        refine ⟨⟨ip', (elim_mem_uiscr E ip').mpr (hip' ▸ hU)⟩, ?_⟩
        exact Subtype.ext hip'⟩

/-- `OZ@$ = OZ@`: the unconnected output ports of `SCR` all sit on retained components. -/
noncomputable def elimUnconnOut {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : UnconnOutPort (elimRecipe E) ≃ UnconnOutPort SCR :=
  Equiv.ofBijective (fun op => ⟨elimOutTag E op.val, (elim_mem_uoscr E op.val).mp op.property⟩)
    ⟨fun op1 op2 h => Subtype.ext (elimOutTag_injective E (congrArg Subtype.val h)),
      by
        rintro ⟨op, hU⟩
        obtain ⟨op', hop'⟩ :=
          elimOutTag_surjective_of_hasOrder E op (hasOrder_of_mem_uoscr SCR op hU)
        refine ⟨⟨op', (elim_mem_uoscr E op').mpr (hop' ▸ hU)⟩, ?_⟩
        exact Subtype.ext hop'⟩

/-- [textbook/exercise4.66/component/HS] `HS = PJN({SZ$ : Z$ ∈ VSCR$})`. -/
def elimHS {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m)
    (x : rsy_SZ SCR) : rsy_SZ (elimRecipe E) := fun i => x (E.ι i)

/-- [textbook/exercise4.66/component/HI] `HI = ID(IZ@)`, read through `UISCR$ ≃ UISCR`. -/
noncomputable def elimHI {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (g : rsy_IZ SCR) : rsy_IZ (elimRecipe E) :=
  fun ip => g (elimUnconnIn E ip)

/-- [textbook/exercise4.66/component/HO] `HO = ID(OZ@)`, read through `UOSCR$ ≃ UOSCR`. -/
noncomputable def elimHO {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (g : rsy_OZ SCR) : rsy_OZ (elimRecipe E) :=
  fun op => g (elimUnconnOut E op)

theorem elimHI_eq {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m) :
    elimHI E =
      (Equiv.piCongrLeft (fun jp : UnconnInPort SCR => SCR.VSCR.PortVal jp.val.1 jp.val.2)
        (elimUnconnIn E)).symm := rfl

theorem elimHO_eq {n m : Nat} {SCR : SystemCouplingRecipe n} (E : NullOrderElimination SCR m) :
    elimHO E =
      (Equiv.piCongrLeft (fun jp : UnconnOutPort SCR => SCR.VSCR.OutPortVal jp.val.1 jp.val.2)
        (elimUnconnOut E)).symm := rfl

/-- Any state of the reduced resultant extends to a state of the original one. -/
noncomputable def elimSection {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (y : rsy_SZ (elimRecipe E)) : rsy_SZ SCR := by
  classical
  exact fun k =>
    if h : ∃ i, E.ι i = k then cast (congrArg SCR.VSCR.SZ h.choose_spec) (y h.choose)
    else Classical.choice (SCR.VSCR.Z k).sz_nonempty

/-- Two retained indices with the same image carry the same component state. -/
theorem elim_state_transport {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (y : rsy_SZ (elimRecipe E)) (j i : Fin m)
    (h : E.ι j = E.ι i) : cast (congrArg SCR.VSCR.SZ h) (y j) = y i := by
  have hji : j = i := E.inj h
  subst hji
  rfl

theorem elimHS_section {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (y : rsy_SZ (elimRecipe E)) :
    elimHS E (elimSection E y) = y := by
  classical
  funext i
  have hex : ∃ j, E.ι j = E.ι i := ⟨i, rfl⟩
  have hval : elimSection E y (E.ι i) =
      cast (congrArg SCR.VSCR.SZ hex.choose_spec) (y hex.choose) := by
    simp [elimSection, hex]
  rw [elimHS, hval]
  exact elim_state_transport E y hex.choose i hex.choose_spec

theorem elimHS_surjective {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) : Function.Surjective (elimHS E) :=
  fun y => ⟨elimSection E y, elimHS_section E y⟩

theorem elim_component_input {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin m)
    (extIn : rsy_IZ SCR) (x : rsy_SZ SCR) (port : (elimRecipe E).VSCR.Port i) :
    rsy_component_input_fun (elimRecipe E) (fun k => hOut (E.ι k)) i
        (elimHI E extIn) (elimHS E x) port =
      rsy_component_input_fun SCR hOut (E.ι i) extIn x port := by
  classical
  by_cases hU : (⟨i, port⟩ : Σ j, (elimRecipe E).VSCR.Port j) ∈ UISCR (elimRecipe E)
  · have hU' : (⟨E.ι i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ UISCR SCR :=
      (elim_mem_uiscr E _).mp hU
    rw [rsy_component_input_uiscr _ _ _ _ _ _ hU, rsy_component_input_uiscr _ _ _ _ _ _ hU']
    rfl
  · have hC : (⟨i, port⟩ : Σ j, (elimRecipe E).VSCR.Port j) ∈ CISCR (elimRecipe E) := by
      simpa [UISCR, Set.mem_compl_iff] using hU
    set op1 := connectedOutput (elimRecipe E) ⟨i, port⟩ hC with hop1def
    have hspec : (op1, (⟨i, port⟩ : Σ j, (elimRecipe E).VSCR.Port j)) ∈ (elimRecipe E).CSCR :=
      connectedOutput_spec (elimRecipe E) ⟨i, port⟩ hC
    have hspec' : (elimOutTag E op1, (⟨E.ι i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR := hspec
    have hty : SCR.VSCR.OutPortVal (E.ι op1.1) op1.2 = SCR.VSCR.PortVal (E.ι i) port :=
      SCR.connectivity.2.2.2 _ _ hspec'
    rw [rsy_component_input_of_conn (elimRecipe E) (fun k => hOut (E.ι k)) i
          (elimHI E extIn) (elimHS E x) port op1 hspec hty,
        rsy_component_input_of_conn SCR hOut (E.ι i) extIn x port
          (elimOutTag E op1) hspec' hty]
    rfl

/--
  [textbook/exercise4.66/proof/homomorphism_witness]
  `Z@$ = HIMSY(Z@, PJN({SZ$ : Z$ ∈ VSCR$}), ID(IZ@), ID(OZ@))`.
-/
noncomputable def elimHomWitness {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    HomomorphicImageWitness (rsy (elimRecipe E) (fun k => hOut (E.ι k))) (rsy SCR hOut) where
  HS := elimHS E
  HI := elimHI E
  HO := elimHO E
  HS_surjective := elimHS_surjective E
  HI_surjective := by
    rw [elimHI_eq]; exact (Equiv.piCongrLeft _ (elimUnconnIn E)).symm.surjective
  HO_surjective := by
    rw [elimHO_eq]; exact (Equiv.piCongrLeft _ (elimUnconnOut E)).symm.surjective
  preserves_transition := by
    intro x oi
    funext i
    have hfun : ∀ e : rsy_IZ SCR,
        rsy_component_input_fun (elimRecipe E) (fun k => hOut (E.ι k)) i
            (elimHI E e) (elimHS E x) =
          rsy_component_input_fun SCR hOut (E.ι i) e x :=
      fun e => funext fun port => elim_component_input E hOut i e x port
    cases oi with
    | none => rfl
    | some e =>
        show (SCR.VSCR.Z (E.ι i)).NZ (x (E.ι i))
            (some (rsy_component_input_fun SCR hOut (E.ι i) e x)) = _
        rw [← hfun e]
        rfl
  preserves_readout := by intro x; rfl

/--
  [textbook/exercise4.66/theorem/null_order_elimination]
  Exercise 4.66: deleting the components of null order leaves the unconnected input and output
  ports unchanged (they all sit on retained components) and makes the new resultant a homomorphic
  image of the original: `Z@$ = RSY(SCR$)` and
  `Z@$ = HIMSY(Z@, PJN({SZ$ : Z$ ∈ VSCR$}), ID(IZ@), ID(OZ@))`.
-/
theorem ex4_66_null_order_elimination {n m : Nat} {SCR : SystemCouplingRecipe n}
    (E : NullOrderElimination SCR m) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    (∀ ip, ip ∈ UISCR (elimRecipe E) ↔ elimInTag E ip ∈ UISCR SCR) ∧
      (∀ op, op ∈ UOSCR (elimRecipe E) ↔ elimOutTag E op ∈ UOSCR SCR) ∧
      IsHomomorphicImage (rsy (elimRecipe E) (fun k => hOut (E.ι k))) (rsy SCR hOut) :=
  ⟨elim_mem_uiscr E, elim_mem_uoscr E, ⟨elimHomWitness E hOut⟩⟩

end Homomorphism
