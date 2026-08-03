import Mbse.Wymore
import Mbse.WymoreCouplingStructure
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic

/-!
# Chapter 3 — coupling recipe exercises (3.113–3.119)
-/

namespace Mbse.TextbookExercises.Ch03

open Mbse.Wymore
open Classical

/-! ## Port-count infrastructure -/

def scr_input_port_count {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.Port i)] : Nat :=
  Fintype.card (Sigma SCR.VSCR.Port)

def scr_output_port_count {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.OutPort i)] : Nat :=
  Fintype.card (Sigma SCR.VSCR.OutPort)

noncomputable instance decidableMemCSCR {n : Nat} (SCR : SystemCouplingRecipe n)
    [Fintype ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))]
    [DecidableEq ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))] :
    DecidablePred (fun p => p ∈ SCR.CSCR) := by
  classical
  exact inferInstanceAs (DecidablePred (fun p => p ∈ SCR.CSCR))

noncomputable def scr_cscr_card {n : Nat} (SCR : SystemCouplingRecipe n)
    [Fintype ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))]
    [DecidableEq ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))] :
    Nat :=
  SCR.CSCR.toFinset.card

private lemma scr_cscr_injOn_fst {n : Nat} (SCR : SystemCouplingRecipe n) :
    Set.InjOn Prod.fst (SCR.CSCR : Set _) := by
  intro p hp q hq hfx
  rcases SCR.connectivity.1 with ⟨hinj_fst, _⟩
  rcases p with ⟨op1, ip1⟩
  rcases q with ⟨op2, ip2⟩
  dsimp at hfx
  have hq' : (op1, ip2) ∈ SCR.CSCR := by simpa [hfx] using hq
  exact Prod.ext hfx (hinj_fst op1 ip1 ip2 hp hq')

private lemma scr_cscr_injOn_snd {n : Nat} (SCR : SystemCouplingRecipe n) :
    Set.InjOn Prod.snd (SCR.CSCR : Set _) := by
  intro p hp q hq hsnd
  rcases SCR.connectivity.1 with ⟨_, hinj_snd⟩
  rcases p with ⟨op1, ip1⟩
  rcases q with ⟨op2, ip2⟩
  dsimp at hsnd
  have hq' : (op2, ip1) ∈ SCR.CSCR := by simpa [hsnd] using hq
  exact Prod.ext (hinj_snd op1 op2 ip1 hp hq') hsnd

private lemma card_sigma_port {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.Port i)] :
    Fintype.card (Sigma SCR.VSCR.Port) = ∑ i : Fin n, Fintype.card (SCR.VSCR.Port i) :=
  Fintype.card_sigma (ι := Fin n) (α := SCR.VSCR.Port)

private lemma card_sigma_out {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.OutPort i)] :
    Fintype.card (Sigma SCR.VSCR.OutPort) = ∑ i : Fin n, Fintype.card (SCR.VSCR.OutPort i) :=
  Fintype.card_sigma (ι := Fin n) (α := SCR.VSCR.OutPort)

/-! ## Exercise 3.113 -/

/--
  [textbook/exercise3.113/theorem/port_count_sum_eq_union]
-/
theorem scr_port_count_sum_eq_union {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.Port i)] [∀ i, Fintype (SCR.VSCR.OutPort i)] :
    scr_input_port_count SCR = ∑ i : Fin n, Fintype.card (SCR.VSCR.Port i) ∧
      scr_output_port_count SCR = ∑ i : Fin n, Fintype.card (SCR.VSCR.OutPort i) := by
  refine And.intro ?_ ?_
  · exact card_sigma_port SCR
  · exact card_sigma_out SCR

/-! ## Exercise 3.114 -/

/--
  [textbook/exercise3.114/theorem/unconnected_ports_exist]
-/
theorem scr_unconnected_ports_exist {n : Nat} (SCR : SystemCouplingRecipe n) :
    (∃ ip, ip ∈ UISCR SCR) ∧ (∃ op, op ∈ UOSCR SCR) := by
  exact ⟨scr_has_unconnected_input_port SCR, scr_has_unconnected_output_port SCR⟩

/--
  [textbook/exercise3.114/theorem/cscr_domain_range_eq]
  Domain and range of `CSCR` have equal cardinality.
-/
theorem scr_cscr_domain_range_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    [Fintype ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))]
    [DecidableEq ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))] :
    (SCR.CSCR.toFinset.image Prod.fst).card = (SCR.CSCR.toFinset.image Prod.snd).card := by
  have hdom := Finset.card_image_of_injOn
    (by
      intro a ha b hb hfx
      exact (scr_cscr_injOn_fst SCR) (Set.mem_toFinset.mp ha) (Set.mem_toFinset.mp hb) hfx)
  have hran := Finset.card_image_of_injOn
    (by
      intro a ha b hb hsnd
      exact (scr_cscr_injOn_snd SCR) (Set.mem_toFinset.mp ha) (Set.mem_toFinset.mp hb) hsnd)
  rw [hdom, hran]

/-! ## Exercise 3.115 -/

/--
  [textbook/exercise3.115/theorem/port_counts_gt_connections]
-/
theorem scr_port_counts_gt_connections {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i, Fintype (SCR.VSCR.Port i)] [∀ i, Fintype (SCR.VSCR.OutPort i)]
    [Fintype ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))]
    [DecidableEq ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))] :
    scr_input_port_count SCR > scr_cscr_card SCR ∧
      scr_output_port_count SCR > scr_cscr_card SCR := by
  have hin : scr_input_port_count SCR > scr_cscr_card SCR := by
    rcases scr_has_unconnected_input_port SCR with ⟨ip, hU⟩
    have hlt : (SCR.CSCR.toFinset.image Prod.snd).card <
        Fintype.card (Sigma SCR.VSCR.Port) := by
      have hsub : SCR.CSCR.toFinset.image Prod.snd ⊆ Finset.univ := Finset.subset_univ _
      have hne : ip ∉ SCR.CSCR.toFinset.image Prod.snd := by
        intro hx
        rcases Finset.mem_image.mp hx with ⟨p, hp, hfx⟩
        have hp_scr : (p.1, ip) ∈ SCR.CSCR := by
          have : (p.1, p.2) ∈ SCR.CSCR := Set.mem_toFinset.mp hp
          simpa [hfx] using this
        have hc : ip ∈ CISCR SCR := (mem_ciscr_iff SCR ip).mpr ⟨p.1, hp_scr⟩
        have hu : ip ∉ CISCR SCR := by simpa [UISCR, Set.mem_compl_iff] using hU
        exact hu hc
      have hne_univ : SCR.CSCR.toFinset.image Prod.snd ≠ Finset.univ := by
        intro heq
        exact hne (heq ▸ Finset.mem_univ ip)
      have hss : SCR.CSCR.toFinset.image Prod.snd ⊂ Finset.univ :=
        (Finset.ssubset_univ_iff.mpr hne_univ)
      exact Finset.card_lt_card hss
    have heq := Finset.card_image_of_injOn
      (by
        intro a ha b hb hsnd
        exact (scr_cscr_injOn_snd SCR) (Set.mem_toFinset.mp ha) (Set.mem_toFinset.mp hb) hsnd)
    have hltsigma : SCR.CSCR.toFinset.card < Fintype.card (Sigma SCR.VSCR.Port) := by
      rw [← heq]
      exact hlt
    dsimp [scr_cscr_card]
    exact hltsigma
  have hout : scr_output_port_count SCR > scr_cscr_card SCR := by
    rcases scr_has_unconnected_output_port SCR with ⟨op, hU⟩
    have hlt : (SCR.CSCR.toFinset.image Prod.fst).card <
        Fintype.card (Sigma SCR.VSCR.OutPort) := by
      have hsub : SCR.CSCR.toFinset.image Prod.fst ⊆ Finset.univ := Finset.subset_univ _
      have hne : op ∉ SCR.CSCR.toFinset.image Prod.fst := by
        intro hx
        rcases Finset.mem_image.mp hx with ⟨p, hp, hfx⟩
        have hp_scr : (op, p.2) ∈ SCR.CSCR := by
          have : (p.1, p.2) ∈ SCR.CSCR := Set.mem_toFinset.mp hp
          simpa [hfx] using this
        have hc : op ∈ COSCR SCR := ⟨p.2, hp_scr⟩
        have hu : op ∉ COSCR SCR := by simpa [UOSCR, Set.mem_compl_iff] using hU
        exact hu hc
      have hne_univ : SCR.CSCR.toFinset.image Prod.fst ≠ Finset.univ := by
        intro heq
        exact hne (heq ▸ Finset.mem_univ op)
      have hss : SCR.CSCR.toFinset.image Prod.fst ⊂ Finset.univ :=
        (Finset.ssubset_univ_iff.mpr hne_univ)
      exact Finset.card_lt_card hss
    have heq := Finset.card_image_of_injOn
      (by
        intro a ha b hb hfx
        exact (scr_cscr_injOn_fst SCR) (Set.mem_toFinset.mp ha) (Set.mem_toFinset.mp hb) hfx)
    have hltsigma : SCR.CSCR.toFinset.card < Fintype.card (Sigma SCR.VSCR.OutPort) := by
      rw [← heq]
      exact hlt
    dsimp [scr_cscr_card]
    exact hltsigma
  exact ⟨hin, hout⟩

/-! ## Exercise 3.116 -/

/--
  [textbook/exercise3.116/theorem/cascade_min_two_components]
-/
theorem cascade_scr_min_two_components {n : Nat} (SCR : SystemCouplingRecipe n)
    (hCas : IsCascade SCR) (hne : SCR.CSCR ≠ ∅) : n > 1 :=
  Mbse.Wymore.cascade_scr_min_two_components SCR hCas hne

/-! ## Exercise 3.117 -/

/--
  [textbook/exercise3.117/theorem/pure_feedback_min_ports]
-/
theorem pure_feedback_min_ports {n : Nat} (SCR : SystemCouplingRecipe n)
    (hPf : IsPureFeedback SCR)
    [∀ i, Fintype (SCR.VSCR.Port i)] [∀ i, Fintype (SCR.VSCR.OutPort i)]
    [Fintype ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))]
    [DecidableEq ((Σ (i : Fin n), SCR.VSCR.OutPort i) × (Σ (i : Fin n), SCR.VSCR.Port i))] :
    min (scr_input_port_count SCR) (scr_output_port_count SCR) ≥ 2 := by
  rcases hPf with ⟨hn, hne⟩
  subst hn
  have hin := scr_port_counts_gt_connections SCR
  have hcscr_pos : scr_cscr_card SCR > 0 := by
    rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨p, hp⟩
    exact Finset.card_pos.mpr ⟨p, Set.mem_toFinset.mpr hp⟩
  omega

/-! ## Exercise 3.118: two-component conjunctive witness -/

def ex3_118_toggle : DiscreteSystem Nat (Nat → Nat) (Nat → Nat) where
  sz_nonempty := ⟨0⟩
  NZ := fun n oi => match oi with | some f => f n | none => n
  RZ := fun n => some (fun _ => n)

def ex3_118_counter : DiscreteSystem Nat (Nat → Nat) (Nat → Nat) where
  sz_nonempty := ⟨0⟩
  NZ := fun n oi => match oi with | some f => n + f n | none => n
  RZ := fun n => some (fun _ => n)

lemma ex3_118_nz_ne : ex3_118_toggle.NZ ≠ ex3_118_counter.NZ := by
  intro hnz
  have h : (1 : Nat) = 0 := by
    simpa [ex3_118_toggle, ex3_118_counter] using
      congrArg (fun f => f 1 (some (fun _ => 0))) hnz
  omega

lemma ex3_118_toggle_ne_counter : ¬ HEq ex3_118_toggle ex3_118_counter := by
  intro h
  exact ex3_118_nz_ne (congrArg DiscreteSystem.NZ (eq_of_heq h))

private lemma fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨v, hv⟩
  rcases Nat.eq_zero_or_pos v with h0 | hpos
  · exact Or.inl (Fin.ext h0)
  · have h1 : v = 1 := by omega
    exact Or.inr (Fin.ext h1)

def ex3_118_Z (i : Fin 2) : DiscreteSystem Nat (Nat → Nat) (Nat → Nat) :=
  Fin.cases ex3_118_toggle (fun _ => ex3_118_counter) i

lemma ex3_118_Z_distinct (i j : Fin 2) (hne : i ≠ j) : ¬ HEq (ex3_118_Z i) (ex3_118_Z j) := by
  intro h
  rcases fin2_eq_zero_or_one i with hi | hi <;> rcases fin2_eq_zero_or_one j with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · subst hi; subst hj; exact ex3_118_toggle_ne_counter h
  · subst hi; subst hj; exact ex3_118_toggle_ne_counter (HEq.symm h)
  · exact absurd (hi.trans hj.symm) hne

def ex3_118_vscr : PortSystemVector 2 where
  SZ := fun _ => Nat
  Port := fun _ => Nat
  PortVal := fun _ _ => Nat
  OutPort := fun _ => Nat
  OutPortVal := fun _ _ => Nat
  Z := ex3_118_Z
  distinct := ex3_118_Z_distinct

def ex3_118_scr : SystemCouplingRecipe 2 where
  VSCR := ex3_118_vscr
  CSCR := ∅
  connectivity :=
    empty_scr_connectivity ex3_118_vscr
      ⟨⟨(0 : Fin 2), (0 : Nat)⟩⟩
      ⟨⟨(0 : Fin 2), (0 : Nat)⟩⟩

/--
  [textbook/exercise3.118/witness/simple_conjunction]
-/
theorem ex3_118_simple_conjunction :
    IsConjunctive ex3_118_scr ∧ IsNonsingularConjunctive ex3_118_scr := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro hs
      rcases hs with ⟨hn, _⟩
      omega

/-! ## Exercise 3.119: conjunctive port identification -/

/--
  [textbook/exercise3.119/theorem/conjunctive_port_identification]
-/
theorem ex3_119_conjunctive_port_identification {n : Nat} (SCR : SystemCouplingRecipe n)
    (_h : IsConjunctive SCR) (ip : UnconnInPort SCR) (op : UnconnOutPort SCR) :
    rsy_IS_map SCR ip = csy_IS_map SCR.VSCR ip.val ∧
      rsy_OS_map SCR op = csy_OS_map SCR.VSCR op.val ∧
      rsy_IP_map SCR ip = ip ∧
      rsy_OP_map SCR op = op := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rfl
  · rfl

end Mbse.TextbookExercises.Ch03
