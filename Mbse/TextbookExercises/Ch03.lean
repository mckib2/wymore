import Mbse.Wymore
import Mbse.WymoreCouplingStructure
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Chapter 3 — coupling recipe exercises (3.113–3.126)

Encoding choices for exercises 3.124–3.126 (homogeneous `uniformNatPortWrap`, `DependsOnInputPort`, distinctness) are documented in [proof_comparison_report.md](proof_comparison_report.md) §23–§25.
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

/-! ## Exercise 3.120: conjunctive port functions -/

/--
  [textbook/exercise3.120/theorem/conjunctive_port_functions]
  CSY port maps are FNS + 1TO1 + ONTO; structure maps agree with component port types.
-/
theorem ex3_120_conjunctive_port_functions {n : Nat} (VSCR : PortSystemVector n) :
    InFNS1TO1Onto (csy_IP_map VSCR) ∧
      InFNS1TO1Onto (csy_INIP_map VSCR) ∧
      (∀ ip, csy_IS_map VSCR ip = VSCR.PortVal ip.1 ip.2) ∧
      InFNS1TO1Onto (csy_OP_map VSCR) ∧
      (∀ op, csy_OS_map VSCR op = VSCR.OutPortVal op.1 op.2) :=
  ⟨csy_IP_map_inFNS1TO1Onto VSCR, csy_INIP_map_inFNS1TO1Onto VSCR,
    fun ip => csy_IS_map_eq VSCR ip, csy_OP_map_inFNS1TO1Onto VSCR,
    fun op => csy_OS_map_eq VSCR op⟩

/-! ## Exercise 3.121: resultant port functions -/

/--
  [textbook/exercise3.121/theorem/resultant_port_functions]
  RSY port maps are FNS + 1TO1 + ONTO on unconnected ports; structure maps agree with components.
-/
theorem ex3_121_resultant_port_functions {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : UnconnInPort SCR) (op : UnconnOutPort SCR) :
    InFNS1TO1Onto (rsy_IP_map SCR) ∧
      InFNS1TO1Onto (rsy_INIP_map SCR) ∧
      rsy_IS_map SCR ip = SCR.VSCR.PortVal ip.val.1 ip.val.2 ∧
      InFNS1TO1Onto (rsy_OP_map SCR) ∧
      InFNS1TO1Onto (rsy_INOP_map SCR) ∧
      rsy_OS_map SCR op = SCR.VSCR.OutPortVal op.val.1 op.val.2 :=
  ⟨rsy_IP_map_inFNS1TO1Onto SCR, rsy_INIP_map_inFNS1TO1Onto SCR, rsy_IS_map_eq SCR ip,
    rsy_OP_map_inFNS1TO1Onto SCR, rsy_INOP_map_inFNS1TO1Onto SCR, rsy_OS_map_eq SCR op⟩

/-! ## Exercise 3.122: every system is a resultant -/

/--
  [textbook/exercise3.122/theorem/every_system_is_resultant]
  Every port-encoded discrete system equals the resultant of its singular recipe `(Z, ∅)`.
-/
abbrev ex3_122_every_system_is_resultant {SZ Port OutPort : Type}
    (PortVal : Port → Type) (OutPortVal : OutPort → Type)
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((op : OutPort) → OutPortVal op))
    (hOut : AlwaysOutputs Z) (hPort : Nonempty Port) (hOutPort : Nonempty OutPort) :=
  every_port_system_is_resultant PortVal OutPortVal Z hOut hPort hOutPort

/-! ## Exercise 3.123: conjunctive RSY = CSY -/

/--
  [textbook/exercise3.123/theorem/conjunctive_rsy_eq_csy]
  On conjunctive recipes, `RSY(SCR)` and `CSY(VSCR)` agree on membership and dynamics.
-/
abbrev ex3_123_conjunctive_rsy_eq_csy {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :=
  conjunctive_rsy_eq_csy SCR h hOut
/-! ## Shared: homogeneous SCR layout (Exercises 3.124 / 3.126) -/

private lemma fin3_eq_zero_one_or_two (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

private def ex3_124_feed :
    (Σ (_ : Fin 2), Nat) × (Σ (_ : Fin 2), Nat) :=
  ⟨⟨(0 : Fin 2), (1 : Nat)⟩, ⟨(1 : Fin 2), (0 : Nat)⟩⟩

private def ex3_124_cscr :
    Set ((Σ (_ : Fin 2), Nat) × (Σ (_ : Fin 2), Nat)) :=
  {ex3_124_feed}

def ex3_124_Z (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (_hPort2 : DependsOnInputPort Z2' 2) (i : Fin 2) :
    DiscreteSystem Nat (Nat → Nat) (Nat → Nat) :=
  Fin.cases (uniformNatPortWrap 2 2 Z1) (fun _ => uniformNatPortWrap 3 1 Z2') i

lemma ex3_124_Z_distinct (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) (i j : Fin 2) (hne : i ≠ j) :
    ¬ HEq (ex3_124_Z Z1 Z2' hPort2 i) (ex3_124_Z Z1 Z2' hPort2 j) := by
  intro h
  rcases fin2_eq_zero_or_one i with hi | hi <;> rcases fin2_eq_zero_or_one j with hj | hj
  · exact absurd (hi.trans hj.symm) hne
  · subst hi; subst hj
    exact uniformNatPortWrap_distinct (by decide : 2 < 3) Z1 Z2' hPort2 h
  · subst hi; subst hj
    exact uniformNatPortWrap_distinct (by decide : 2 < 3) Z1 Z2' hPort2 (HEq.symm h)
  · exact absurd (hi.trans hj.symm) hne

def ex3_124_vscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) : PortSystemVector 2 where
  SZ := fun _ => Nat
  Port := fun _ => Nat
  PortVal := fun _ _ => Nat
  OutPort := fun _ => Nat
  OutPortVal := fun _ _ => Nat
  Z := ex3_124_Z Z1 Z2' hPort2
  distinct := ex3_124_Z_distinct Z1 Z2' hPort2

private lemma ex3_124_connectivity (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    IsSystemConnectivity (ex3_124_vscr Z1 Z2' hPort2) ex3_124_cscr := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩
  · refine ⟨ ?_, ?_ ⟩
    · intro x y1 y2 h1 h2
      simp only [ex3_124_cscr] at h1 h2
      exact congr_arg Prod.snd (h1.trans h2.symm)
    · intro x1 x2 y h1 h2
      simp only [ex3_124_cscr] at h1 h2
      exact congr_arg Prod.fst (h1.trans h2.symm)
  · intro heq
    have hnot : ⟨(0 : Fin 2), (0 : Nat)⟩ ∉ {x | ∃ y, (x, y) ∈ ex3_124_cscr} := by
      intro hmem
      obtain ⟨ip, hpair⟩ := hmem
      simp only [ex3_124_cscr, Set.mem_singleton_iff] at hpair
      cases hpair
    exact hnot (heq ▸ Set.mem_univ (α := Σ (_ : Fin 2), Nat) ⟨(0 : Fin 2), (0 : Nat)⟩)
  · intro heq
    have hnot : ⟨(0 : Fin 2), (1 : Nat)⟩ ∉ {y | ∃ x, (x, y) ∈ ex3_124_cscr} := by
      intro hmem
      obtain ⟨op, hpair⟩ := hmem
      simp only [ex3_124_cscr, Set.mem_singleton_iff] at hpair
      cases hpair
    exact hnot (heq ▸ Set.mem_univ (α := Σ (_ : Fin 2), Nat) ⟨(0 : Fin 2), (1 : Nat)⟩)
  · intro _ _ h
    simp only [ex3_124_cscr, ex3_124_feed] at h ⊢
    rfl

def ex3_124_scr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) : SystemCouplingRecipe 2 where
  VSCR := ex3_124_vscr Z1 Z2' hPort2
  CSCR := ex3_124_cscr
  connectivity := ex3_124_connectivity Z1 Z2' hPort2

private lemma ex3_124_ip10_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    ⟨(1 : Fin 2), (0 : Nat)⟩ ∈ CISCR (ex3_124_scr Z1 Z2' hPort2) := by
  rw [mem_ciscr_iff]
  exact ⟨⟨(0 : Fin 2), (1 : Nat)⟩, by
    change ex3_124_feed ∈ ex3_124_cscr
    simp [ex3_124_cscr]⟩

private lemma ex3_124_not_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (ip : Σ (_ : Fin 2), Nat) (hne : ip ≠ ⟨(1 : Fin 2), (0 : Nat)⟩) :
    ip ∉ CISCR (ex3_124_scr Z1 Z2' hPort2) := by
  intro hC
  obtain ⟨op, hop⟩ := (mem_ciscr_iff (ex3_124_scr Z1 Z2' hPort2) ip).mp hC
  have heq : (op, ip) = ex3_124_feed := by
    simpa [ex3_124_scr, ex3_124_cscr] using Set.mem_singleton_iff.mp hop
  exact hne (congr_arg Prod.snd heq)

private lemma ex3_124_in_uiscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (ip : Σ (_ : Fin 2), Nat) (hne : ip ≠ ⟨(1 : Fin 2), (0 : Nat)⟩) :
    ip ∈ UISCR (ex3_124_scr Z1 Z2' hPort2) :=
  mem_uiscr_of_not_mem_ciscr (ex3_124_scr Z1 Z2' hPort2) ip
    (ex3_124_not_in_ciscr Z1 Z2' hPort2 ip hne)

private def ex3_124_extInVal (g : Fin 4 → Nat) (ip : Σ (_ : Fin 2), Nat) : Nat :=
  match ip with
  | ⟨(0 : Fin 2), (0 : Nat)⟩ => g 0
  | ⟨(0 : Fin 2), (1 : Nat)⟩ => g 1
  | ⟨(1 : Fin 2), (1 : Nat)⟩ => g 2
  | ⟨(1 : Fin 2), (2 : Nat)⟩ => g 3
  | _ => g 0

noncomputable def ex3_124_extIn (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) (g : Fin 4 → Nat) :
    rsy_IZ (ex3_124_scr Z1 Z2' hPort2) :=
  fun ip => ex3_124_extInVal g ip.val

private lemma ex3_124_readout_Z1 (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (hOut1 : AlwaysOutputs Z1) (op : Nat) (hop : op < 2) (x : Nat) :
    componentReadoutAt (uniformNatPortWrap 2 2 Z1)
      (uniformNatPortWrap_alwaysOutputs 2 2 Z1 hOut1) op x =
      componentReadoutAt Z1 hOut1 ⟨op, hop⟩ x := by
  dsimp [componentReadoutAt]
  calc Classical.choose (uniformNatPortWrap_alwaysOutputs 2 2 Z1 hOut1 x) op
      _ = uniformNatPortEncode 2 (Classical.choose (hOut1 x)) op :=
        congrArg (fun f => f op) (uniformNatPortWrap_choose_encode 2 2 Z1 hOut1 x)
      _ = Classical.choose (hOut1 x) ⟨op, hop⟩ := uniformNatPortEncode_nat_lt 2 _ op hop

private lemma ex3_124_readout_Z2' (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hOut2 : AlwaysOutputs Z2') (op : Nat) (hop : op < 1) (x : Nat) :
    componentReadoutAt (uniformNatPortWrap 3 1 Z2')
      (uniformNatPortWrap_alwaysOutputs 3 1 Z2' hOut2) op x =
      componentReadoutAt Z2' hOut2 ⟨op, hop⟩ x := by
  dsimp [componentReadoutAt]
  calc Classical.choose (uniformNatPortWrap_alwaysOutputs 3 1 Z2' hOut2 x) op
      _ = uniformNatPortEncode 1 (Classical.choose (hOut2 x)) op :=
        congrArg (fun f => f op) (uniformNatPortWrap_choose_encode 3 1 Z2' hOut2 x)
      _ = Classical.choose (hOut2 x) ⟨op, hop⟩ := uniformNatPortEncode_nat_lt 1 _ op hop

private lemma ex3_124_vscr_hOut
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) (hOut1 : AlwaysOutputs Z1) (hOut2 : AlwaysOutputs Z2') :
    ∀ i : Fin 2, AlwaysOutputs ((ex3_124_vscr Z1 Z2' hPort2).Z i) := by
  intro i
  fin_cases i <;> dsimp [ex3_124_vscr, ex3_124_Z, Fin.cases]
  · exact uniformNatPortWrap_alwaysOutputs 2 2 Z1 hOut1
  · exact uniformNatPortWrap_alwaysOutputs 3 1 Z2' hOut2

/-! ## Exercise 3.124: simple cascade resultant -/

/--
  [textbook/exercise3.124/theorem/simple_cascade_rsy]
  Resultant of a simple cascade SCR: `O2Z1 → I1Z2`, external I/O and component `NZ`/`RZ` decomposition.
-/
theorem ex3_124_simple_cascade_rsy
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (hOut1 : AlwaysOutputs Z1) (hOut2 : AlwaysOutputs Z2')
    (x : Fin 2 → Nat) (g : Fin 4 → Nat) :
    let SCR := ex3_124_scr Z1 Z2' hPort2
    let hOut := ex3_124_vscr_hOut Z1 Z2' hPort2 hOut1 hOut2
    let extIn := ex3_124_extIn Z1 Z2' hPort2 g
    rsy_NZ SCR hOut x (some extIn) 0 = Z1.NZ (x 0)
        (some (fun p : Fin 2 => Fin.cases (g 0) (g 1) p)) ∧
      rsy_NZ SCR hOut x (some extIn) 1 = Z2'.NZ (x 1)
        (some (fun p : Fin 3 =>
          Fin.cases (componentReadoutAt Z1 hOut1 (1 : Fin 2) (x 0))
            (fun i => Fin.cases (g ⟨2, by decide⟩) (g ⟨3, by decide⟩) i) p)) ∧
      rsyOutAt SCR hOut x ⟨(0 : Fin 2), (0 : Nat)⟩ =
        componentReadoutAt Z1 hOut1 (0 : Fin 2) (x 0) ∧
      rsyOutAt SCR hOut x ⟨(1 : Fin 2), (0 : Nat)⟩ =
        componentReadoutAt Z2' hOut2 (0 : Fin 1) (x 1) := by
  intro SCR hOut extIn
  constructor
  · dsimp only [SCR, rsy_NZ, uniformNatPortWrap_NZ_some]
    apply congr_arg (Z1.NZ (x 0))
    apply congr_arg some
    have hfin :
        uniformNatPortDecode 2 (rsy_component_input_fun SCR hOut 0 extIn x) =
          fun p => Fin.cases (g 0) (g 1) p := by
      funext p
      fin_cases p
      · dsimp [uniformNatPortDecode, Fin.val_zero, Fin.cases]
        rw [rsy_two_component_input_uiscr SCR hOut 0 extIn x (0 : Nat)
          (ex3_124_in_uiscr Z1 Z2' hPort2 ⟨(0 : Fin 2), (0 : Nat)⟩ (by decide))]
        dsimp [extIn, ex3_124_extIn, ex3_124_extInVal]
      · dsimp [uniformNatPortDecode, Fin.cases]
        rw [rsy_two_component_input_uiscr SCR hOut 0 extIn x (1 : Nat)
          (ex3_124_in_uiscr Z1 Z2' hPort2 ⟨(0 : Fin 2), (1 : Nat)⟩ (by decide))]
        dsimp [extIn, ex3_124_extIn, ex3_124_extInVal]; rfl
    rw [hfin]
  · constructor
    · dsimp only [SCR, rsy_NZ, uniformNatPortWrap_NZ_some]
      apply congr_arg (Z2'.NZ (x 1))
      apply congr_arg some
      have hfin :
          uniformNatPortDecode 3 (rsy_component_input_fun SCR hOut 1 extIn x) =
            fun p => Fin.cases (componentReadoutAt Z1 hOut1 (1 : Fin 2) (x 0))
              (fun i => Fin.cases (g ⟨2, by decide⟩) (g ⟨3, by decide⟩) i) p := by
        funext p
        fin_cases p
        · dsimp [uniformNatPortDecode, Fin.val_zero, Fin.cases]
          have hC := ex3_124_ip10_in_ciscr Z1 Z2' hPort2
          rw [rsy_two_component_input_ciscr SCR hOut 1 extIn x (0 : Nat) hC]
          have hop := connectedOutput_spec SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC
          have heq : connectedOutput SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC = ⟨(0 : Fin 2), (1 : Nat)⟩ :=
            congr_arg Prod.fst (Set.mem_singleton_iff.mp (by simpa [ex3_124_cscr] using hop))
          suffices rsyOutAt SCR hOut x (connectedOutput SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC) =
              componentReadoutAt Z1 hOut1 1 (x 0) by
            simpa [heq] using this
          rw [heq]
          rw [rsyOutAt_eq_componentReadoutAt SCR hOut 0 (1 : Nat) x]
          exact ex3_124_readout_Z1 Z1 hOut1 1 (by decide) (x 0)
        · dsimp [uniformNatPortDecode, Fin.cases]
          rw [rsy_two_component_input_uiscr SCR hOut 1 extIn x (1 : Nat)
            (ex3_124_in_uiscr Z1 Z2' hPort2 ⟨(1 : Fin 2), (1 : Nat)⟩ (by decide))]
          dsimp [extIn, ex3_124_extIn, ex3_124_extInVal]; rfl
        · dsimp [uniformNatPortDecode, Fin.cases]
          rw [rsy_two_component_input_uiscr SCR hOut 1 extIn x (2 : Nat)
            (ex3_124_in_uiscr Z1 Z2' hPort2 ⟨(1 : Fin 2), (2 : Nat)⟩ (by decide))]
          dsimp [extIn, ex3_124_extIn, ex3_124_extInVal]; rfl
      rw [hfin]
    · constructor
      · dsimp [rsyOutAt]
        exact ex3_124_readout_Z1 Z1 hOut1 0 (by decide) (x 0)
      · dsimp [rsyOutAt]
        exact ex3_124_readout_Z2' Z2' hOut2 0 (by decide) (x 1)

/--
  [textbook/exercise3.124/theorem/is_cascade]
  The simple cascade recipe of Ex. 3.124 satisfies `IsCascade`.
-/
theorem ex3_124_is_cascade
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    IsCascade (ex3_124_scr Z1 Z2' hPort2) := by
  intro p hp
  have : p = ex3_124_feed := Set.mem_singleton_iff.mp (by simpa [ex3_124_scr, ex3_124_cscr] using hp)
  subst this
  simp [IsFeedback, ex3_124_feed]

/-! ## Exercise 3.125: simple pure feedback resultant -/

private def ex3_125_feed :
    (Σ (_ : Fin 1), Nat) × (Σ (_ : Fin 1), Nat) :=
  ⟨⟨(0 : Fin 1), (1 : Nat)⟩, ⟨(0 : Fin 1), (1 : Nat)⟩⟩

private def ex3_125_cscr : Set ((Σ (_ : Fin 1), Nat) × (Σ (_ : Fin 1), Nat)) :=
  {ex3_125_feed}

def ex3_125_Z (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) :
    DiscreteSystem Nat (Nat → Nat) (Nat → Nat) :=
  uniformNatPortWrap 2 2 Z1

def ex3_125_vscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) : PortSystemVector 1 where
  SZ := fun _ => Nat
  Port := fun _ => Nat
  PortVal := fun _ _ => Nat
  OutPort := fun _ => Nat
  OutPortVal := fun _ _ => Nat
  Z := fun _ => ex3_125_Z Z1
  distinct := fun i j hne => absurd (Trajectory.fin_one_eq i j) hne

private lemma ex3_125_connectivity (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) :
    IsSystemConnectivity (ex3_125_vscr Z1) ex3_125_cscr := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩
  · refine ⟨ ?_, ?_ ⟩
    · intro x y1 y2 h1 h2
      simp only [ex3_125_cscr] at h1 h2
      exact congr_arg Prod.snd (h1.trans h2.symm)
    · intro x1 x2 y h1 h2
      simp only [ex3_125_cscr] at h1 h2
      exact congr_arg Prod.fst (h1.trans h2.symm)
  · intro heq
    have hnot : ⟨(0 : Fin 1), (0 : Nat)⟩ ∉ {x | ∃ y, (x, y) ∈ ex3_125_cscr} := by
      intro hmem
      obtain ⟨ip, hpair⟩ := hmem
      simp only [ex3_125_cscr, Set.mem_singleton_iff] at hpair
      cases hpair
    exact hnot (heq ▸ Set.mem_univ (α := Σ (i : Fin 1), Nat) ⟨(0 : Fin 1), (0 : Nat)⟩)
  · intro heq
    have hnot : ⟨(0 : Fin 1), (0 : Nat)⟩ ∉ {y | ∃ x, (x, y) ∈ ex3_125_cscr} := by
      intro hmem
      obtain ⟨op, hpair⟩ := hmem
      simp only [ex3_125_cscr, Set.mem_singleton_iff] at hpair
      cases hpair
    exact hnot (heq ▸ Set.mem_univ (α := Σ (i : Fin 1), Nat) ⟨(0 : Fin 1), (0 : Nat)⟩)
  · intro _ _ h
    simp only [ex3_125_cscr, ex3_125_feed] at h ⊢
    rfl

def ex3_125_scr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) : SystemCouplingRecipe 1 where
  VSCR := ex3_125_vscr Z1
  CSCR := ex3_125_cscr
  connectivity := ex3_125_connectivity Z1

private lemma ex3_125_ip1_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) :
    ⟨(0 : Fin 1), (1 : Nat)⟩ ∈ CISCR (ex3_125_scr Z1) := by
  rw [mem_ciscr_iff]
  exact ⟨⟨(0 : Fin 1), (1 : Nat)⟩, by
    change ex3_125_feed ∈ ex3_125_cscr
    simp [ex3_125_cscr]⟩

private lemma ex3_125_ip0_in_uiscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) :
    ⟨(0 : Fin 1), (0 : Nat)⟩ ∈ UISCR (ex3_125_scr Z1) :=
  mem_uiscr_of_not_mem_ciscr (ex3_125_scr Z1) ⟨(0 : Fin 1), (0 : Nat)⟩ (by
    intro hC
    obtain ⟨op, hop⟩ := (mem_ciscr_iff (ex3_125_scr Z1) ⟨(0 : Fin 1), (0 : Nat)⟩).mp hC
    have heq := congr_arg Prod.snd (Set.mem_singleton_iff.mp (by simpa [ex3_125_scr, ex3_125_cscr] using hop))
    simp [ex3_125_feed] at heq
    cases heq)

private def ex3_125_extInVal (p : Nat) (ip : Σ (_ : Fin 1), Nat) : Nat :=
  match ip with
  | ⟨(0 : Fin 1), (0 : Nat)⟩ => p
  | _ => p

noncomputable def ex3_125_extIn (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (p : Nat) : rsy_IZ (ex3_125_scr Z1) :=
  fun ip => ex3_125_extInVal p ip.val

private lemma ex3_125_readout_Z1 (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (hOut1 : AlwaysOutputs Z1) (op : Nat) (hop : op < 2) (x : Nat) :
    componentReadoutAt (ex3_125_Z Z1) (uniformNatPortWrap_alwaysOutputs 2 2 Z1 hOut1) op x =
      componentReadoutAt Z1 hOut1 ⟨op, hop⟩ x :=
  ex3_124_readout_Z1 Z1 hOut1 op hop x

/--
  [textbook/exercise3.125/theorem/simple_feedback_rsy]
  Resultant of simple pure feedback: `O2Z1 → I2Z1`, external `I1Z1` / `O1Z1`.
-/
theorem ex3_125_simple_feedback_rsy
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (hOut1 : AlwaysOutputs Z1) (x : Nat) (p : Nat) :
    let SCR := ex3_125_scr Z1
    let hOut := fun _ => uniformNatPortWrap_alwaysOutputs 2 2 Z1 hOut1
    let extIn := ex3_125_extIn Z1 p
    rsy_NZ SCR hOut (fun _ => x) (some extIn) 0 = Z1.NZ x
        (some (fun i : Fin 2 =>
          Fin.cases p (componentReadoutAt Z1 hOut1 (1 : Fin 2) x) i)) ∧
      rsyOutAt SCR hOut (fun _ => x) ⟨(0 : Fin 1), (0 : Nat)⟩ =
        componentReadoutAt Z1 hOut1 (0 : Fin 2) x := by
  intro SCR hOut extIn
  constructor
  · dsimp [rsy_NZ, uniformNatPortWrap_NZ_some, ex3_125_Z]
    apply congr_arg (Z1.NZ x)
    apply congr_arg some
    have hfin :
        uniformNatPortDecode 2 (rsy_component_input_fun SCR hOut 0 extIn (fun _ => x)) =
          fun i => Fin.cases p (componentReadoutAt Z1 hOut1 (1 : Fin 2) x) i := by
      funext i
      fin_cases i
      · dsimp [uniformNatPortDecode, Fin.val_zero, Fin.cases]
        rw [rsy_two_component_input_uiscr SCR hOut 0 extIn (fun _ => x) (0 : Nat)
          (ex3_125_ip0_in_uiscr Z1)]
        dsimp [extIn, ex3_125_extIn, ex3_125_extInVal]
      · dsimp [uniformNatPortDecode, Fin.cases]
        have hC := ex3_125_ip1_in_ciscr Z1
        rw [rsy_two_component_input_ciscr SCR hOut 0 extIn (fun _ => x) (1 : Nat) hC]
        have hop := connectedOutput_spec SCR ⟨(0 : Fin 1), (1 : Nat)⟩ hC
        have heq : connectedOutput SCR ⟨(0 : Fin 1), (1 : Nat)⟩ hC = ⟨(0 : Fin 1), (1 : Nat)⟩ :=
          congr_arg Prod.fst (Set.mem_singleton_iff.mp (by simpa [ex3_125_cscr] using hop))
        suffices rsyOutAt SCR hOut (fun _ => x) (connectedOutput SCR ⟨(0 : Fin 1), (1 : Nat)⟩ hC) =
            componentReadoutAt Z1 hOut1 1 x by
          simpa [heq] using this
        rw [heq]
        rw [rsyOutAt_eq_componentReadoutAt SCR hOut 0 (1 : Nat) (fun _ => x)]
        exact ex3_125_readout_Z1 Z1 hOut1 1 (by decide) x
    rw [hfin]
  · dsimp [rsyOutAt]
    exact ex3_125_readout_Z1 Z1 hOut1 0 (by decide) x

/--
  [textbook/exercise3.125/theorem/is_pure_feedback]
  The simple feedback recipe of Ex. 3.125 satisfies `IsPureFeedback`.
-/
theorem ex3_125_is_pure_feedback (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat)) :
    IsPureFeedback (ex3_125_scr Z1) :=
  ⟨rfl, Set.singleton_ne_empty _⟩

/-! ## Exercise 3.126: simple mixed resultant -/

private def ex3_126_feed_cascade :
    (Σ (_ : Fin 2), Nat) × (Σ (_ : Fin 2), Nat) :=
  ⟨⟨(0 : Fin 2), (1 : Nat)⟩, ⟨(1 : Fin 2), (0 : Nat)⟩⟩

private def ex3_126_feed_back :
    (Σ (_ : Fin 2), Nat) × (Σ (_ : Fin 2), Nat) :=
  ⟨⟨(1 : Fin 2), (0 : Nat)⟩, ⟨(0 : Fin 2), (0 : Nat)⟩⟩

private def ex3_126_cscr :
    Set ((Σ (_ : Fin 2), Nat) × (Σ (_ : Fin 2), Nat)) :=
  insert ex3_126_feed_cascade {ex3_126_feed_back}

private lemma ex3_126_feeds_ne :
    ex3_126_feed_cascade ≠ ex3_126_feed_back := by
  intro h
  have hfst := congr_arg Prod.fst h
  simp [ex3_126_feed_cascade, ex3_126_feed_back] at hfst

private lemma ex3_126_connectivity (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    IsSystemConnectivity (ex3_124_vscr Z1 Z2' hPort2) ex3_126_cscr := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩
  · refine ⟨ ?_, ?_ ⟩
    · intro x y1 y2 h1 h2
      rcases Set.mem_insert_iff.mp h1 with h1c | h1b
      · rcases Set.mem_insert_iff.mp h2 with h2c | h2b
        · exact congr_arg Prod.snd (h1c.trans h2c.symm)
        · exfalso
          have hx := congr_arg Prod.fst h1c
          have hx' := congr_arg Prod.fst (Set.mem_singleton_iff.mp h2b)
          simp [ex3_126_feed_cascade, ex3_126_feed_back] at hx hx'
          exact (by decide : (0 : Fin 2) ≠ 1) (congr_arg Sigma.fst (hx.symm.trans hx'))
      · rcases Set.mem_insert_iff.mp h2 with h2c | h2b
        · exfalso
          have hx := congr_arg Prod.fst h2c
          have hx' := congr_arg Prod.fst (Set.mem_singleton_iff.mp h1b)
          simp [ex3_126_feed_cascade, ex3_126_feed_back] at hx hx'
          exact (by decide : (0 : Fin 2) ≠ 1) (congr_arg Sigma.fst (hx.symm.trans hx'))
        · exact congr_arg Prod.snd ((Set.mem_singleton_iff.mp h1b).trans (Set.mem_singleton_iff.mp h2b).symm)
    · intro x1 x2 y h1 h2
      rcases Set.mem_insert_iff.mp h1 with h1c | h1b
      · rcases Set.mem_insert_iff.mp h2 with h2c | h2b
        · exact congr_arg Prod.fst (h1c.trans h2c.symm)
        · exfalso
          have hy := congr_arg Prod.snd h1c
          have hy' := congr_arg Prod.snd (Set.mem_singleton_iff.mp h2b)
          simp [ex3_126_feed_cascade, ex3_126_feed_back] at hy hy'
          exact (by decide : (1 : Fin 2) ≠ 0) (congr_arg Sigma.fst (hy.symm.trans hy'))
      · rcases Set.mem_insert_iff.mp h2 with h2c | h2b
        · exfalso
          have hy := congr_arg Prod.snd h2c
          have hy' := congr_arg Prod.snd (Set.mem_singleton_iff.mp h1b)
          simp [ex3_126_feed_cascade, ex3_126_feed_back] at hy hy'
          exact (by decide : (1 : Fin 2) ≠ 0) (congr_arg Sigma.fst (hy.symm.trans hy'))
        · exact congr_arg Prod.fst ((Set.mem_singleton_iff.mp h1b).trans (Set.mem_singleton_iff.mp h2b).symm)
  · intro heq
    have hnot : ⟨(0 : Fin 2), (0 : Nat)⟩ ∉ {x | ∃ y, (x, y) ∈ ex3_126_cscr} := by
      intro hmem
      obtain ⟨ip, hpair⟩ := hmem
      rcases Set.mem_insert_iff.mp hpair with h1 | h2
      · have hfst := congr_arg Prod.fst h1
        simp [ex3_126_feed_cascade] at hfst
      · have h2eq := Set.mem_singleton_iff.mp h2
        have hfst := congr_arg Prod.fst h2eq
        simp [ex3_126_feed_back] at hfst
    exact hnot (heq ▸ Set.mem_univ (α := Σ (_ : Fin 2), Nat) ⟨(0 : Fin 2), (0 : Nat)⟩)
  · intro heq
    have hnot : ⟨(0 : Fin 2), (1 : Nat)⟩ ∉ {y | ∃ x, (x, y) ∈ ex3_126_cscr} := by
      intro hmem
      obtain ⟨op, hpair⟩ := hmem
      rcases Set.mem_insert_iff.mp hpair with h1 | h2
      · have hsnd := congr_arg Prod.snd h1
        simp [ex3_126_feed_cascade] at hsnd
      · have h2eq := Set.mem_singleton_iff.mp h2
        have hsnd := congr_arg Prod.snd h2eq
        simp [ex3_126_feed_back] at hsnd
    exact hnot (heq ▸ Set.mem_univ (α := Σ (_ : Fin 2), Nat) ⟨(0 : Fin 2), (1 : Nat)⟩)
  · intro op ip h
    rcases Set.mem_insert_iff.mp h with h1 | h2
    · rw [show op = ⟨(0 : Fin 2), (1 : Nat)⟩ from congr_arg Prod.fst h1,
        show ip = ⟨(1 : Fin 2), (0 : Nat)⟩ from congr_arg Prod.snd h1]
      rfl
    · have h2' := Set.mem_singleton_iff.mp h2
      rw [show op = ⟨(1 : Fin 2), (0 : Nat)⟩ from congr_arg Prod.fst h2',
        show ip = ⟨(0 : Fin 2), (0 : Nat)⟩ from congr_arg Prod.snd h2']
      rfl

noncomputable def ex3_126_scr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) : SystemCouplingRecipe 2 where
  VSCR := ex3_124_vscr Z1 Z2' hPort2
  CSCR := ex3_126_cscr
  connectivity := ex3_126_connectivity Z1 Z2' hPort2

private lemma ex3_126_ip00_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    ⟨(0 : Fin 2), (0 : Nat)⟩ ∈ CISCR (ex3_126_scr Z1 Z2' hPort2) := by
  rw [mem_ciscr_iff]
  exact ⟨⟨(1 : Fin 2), (0 : Nat)⟩, by
    change ex3_126_feed_back ∈ ex3_126_cscr
    simp [ex3_126_cscr]⟩

private lemma ex3_126_ip10_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) :
    ⟨(1 : Fin 2), (0 : Nat)⟩ ∈ CISCR (ex3_126_scr Z1 Z2' hPort2) := by
  rw [mem_ciscr_iff]
  exact ⟨⟨(0 : Fin 2), (1 : Nat)⟩, by
    change ex3_126_feed_cascade ∈ ex3_126_cscr
    simp [ex3_126_cscr]⟩

private lemma ex3_126_not_in_ciscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (ip : Σ (_ : Fin 2), Nat)
    (hne0 : ip ≠ ⟨(0 : Fin 2), (0 : Nat)⟩) (hne1 : ip ≠ ⟨(1 : Fin 2), (0 : Nat)⟩) :
    ip ∉ CISCR (ex3_126_scr Z1 Z2' hPort2) := by
  intro hC
  obtain ⟨op, hop⟩ := (mem_ciscr_iff (ex3_126_scr Z1 Z2' hPort2) ip).mp hC
  rcases Set.mem_insert_iff.mp (by simpa [ex3_126_scr, ex3_126_cscr] using hop) with h1 | h2
  · exact hne1 (congr_arg Prod.snd h1)
  · exact hne0 (congr_arg Prod.snd (Set.mem_singleton_iff.mp h2))

private lemma ex3_126_in_uiscr (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (ip : Σ (_ : Fin 2), Nat)
    (hne0 : ip ≠ ⟨(0 : Fin 2), (0 : Nat)⟩) (hne1 : ip ≠ ⟨(1 : Fin 2), (0 : Nat)⟩) :
    ip ∈ UISCR (ex3_126_scr Z1 Z2' hPort2) :=
  mem_uiscr_of_not_mem_ciscr (ex3_126_scr Z1 Z2' hPort2) ip
    (ex3_126_not_in_ciscr Z1 Z2' hPort2 ip hne0 hne1)

private def ex3_126_extInVal (g : Fin 3 → Nat) (ip : Σ (_ : Fin 2), Nat) : Nat :=
  match ip with
  | ⟨(0 : Fin 2), (1 : Nat)⟩ => g 0
  | ⟨(1 : Fin 2), (1 : Nat)⟩ => g 1
  | ⟨(1 : Fin 2), (2 : Nat)⟩ => g 2
  | _ => g 0

noncomputable def ex3_126_extIn (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2) (g : Fin 3 → Nat) :
    rsy_IZ (ex3_126_scr Z1 Z2' hPort2) :=
  fun ip => ex3_126_extInVal g ip.val

/--
  [textbook/exercise3.126/theorem/simple_mixed_rsy]
  Resultant of simple mixed SCR: cascade `O2Z1 → I1Z2` plus feedback `OZ2 → I1Z1`.
-/
theorem ex3_126_simple_mixed_rsy
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (hOut1 : AlwaysOutputs Z1) (hOut2 : AlwaysOutputs Z2')
    (x : Fin 2 → Nat) (g : Fin 3 → Nat) :
    let SCR := ex3_126_scr Z1 Z2' hPort2
    let hOut := ex3_124_vscr_hOut Z1 Z2' hPort2 hOut1 hOut2
    let extIn := ex3_126_extIn Z1 Z2' hPort2 g
    rsy_NZ SCR hOut x (some extIn) 0 = Z1.NZ (x 0)
        (some (fun p : Fin 2 =>
          Fin.cases (componentReadoutAt Z2' hOut2 (0 : Fin 1) (x 1)) (g 0) p)) ∧
      rsy_NZ SCR hOut x (some extIn) 1 = Z2'.NZ (x 1)
        (some (fun p : Fin 3 =>
          Fin.cases (componentReadoutAt Z1 hOut1 (1 : Fin 2) (x 0))
            (fun i => Fin.cases (g ⟨1, by decide⟩) (g ⟨2, by decide⟩) i) p)) ∧
      rsyOutAt SCR hOut x ⟨(0 : Fin 2), (0 : Nat)⟩ =
        componentReadoutAt Z1 hOut1 (0 : Fin 2) (x 0) := by
  intro SCR hOut extIn
  constructor
  · dsimp only [rsy_NZ, uniformNatPortWrap_NZ_some]
    apply congr_arg (Z1.NZ (x 0))
    apply congr_arg some
    have hfin :
        uniformNatPortDecode 2 (rsy_component_input_fun SCR hOut 0 extIn x) =
          fun p => Fin.cases (componentReadoutAt Z2' hOut2 (0 : Fin 1) (x 1)) (g 0) p := by
      funext p
      fin_cases p
      · dsimp [uniformNatPortDecode, Fin.val_zero, Fin.cases]
        have hC := ex3_126_ip00_in_ciscr Z1 Z2' hPort2
        rw [rsy_two_component_input_ciscr SCR hOut 0 extIn x (0 : Nat) hC]
        have hop := connectedOutput_spec SCR ⟨(0 : Fin 2), (0 : Nat)⟩ hC
        have heq : connectedOutput SCR ⟨(0 : Fin 2), (0 : Nat)⟩ hC = ⟨(1 : Fin 2), (0 : Nat)⟩ := by
          rcases Set.mem_insert_iff.mp (by simpa [ex3_126_cscr] using hop) with h | h
          · exfalso
            have h' := congr_arg Prod.snd h
            simp [ex3_126_feed_cascade] at h'
            exact (by decide : (0 : Fin 2) ≠ 1) (congr_arg Sigma.fst h')
          · exact congr_arg Prod.fst (Set.mem_singleton_iff.mp h)
        suffices rsyOutAt SCR hOut x (connectedOutput SCR ⟨(0 : Fin 2), (0 : Nat)⟩ hC) =
            componentReadoutAt Z2' hOut2 0 (x 1) by
          simpa [heq] using this
        rw [heq]
        rw [rsyOutAt_eq_componentReadoutAt SCR hOut 1 (0 : Nat) x]
        exact ex3_124_readout_Z2' Z2' hOut2 0 (by decide) (x 1)
      · dsimp [uniformNatPortDecode, Fin.cases]
        rw [rsy_two_component_input_uiscr SCR hOut 0 extIn x (1 : Nat)
          (ex3_126_in_uiscr Z1 Z2' hPort2 ⟨(0 : Fin 2), (1 : Nat)⟩ (by decide) (by decide))]
        dsimp [extIn, ex3_126_extIn, ex3_126_extInVal]; rfl
    rw [hfin]
  · constructor
    · dsimp only [SCR, rsy_NZ, uniformNatPortWrap_NZ_some]
      apply congr_arg (Z2'.NZ (x 1))
      apply congr_arg some
      have hfin :
          uniformNatPortDecode 3 (rsy_component_input_fun SCR hOut 1 extIn x) =
            fun p => Fin.cases (componentReadoutAt Z1 hOut1 (1 : Fin 2) (x 0))
              (fun i => Fin.cases (g ⟨1, by decide⟩) (g ⟨2, by decide⟩) i) p := by
        funext p
        fin_cases p
        · dsimp [uniformNatPortDecode, Fin.val_zero, Fin.cases]
          have hC := ex3_126_ip10_in_ciscr Z1 Z2' hPort2
          rw [rsy_two_component_input_ciscr SCR hOut 1 extIn x (0 : Nat) hC]
          have hop := connectedOutput_spec SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC
          have heq : connectedOutput SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC = ⟨(0 : Fin 2), (1 : Nat)⟩ := by
            rcases Set.mem_insert_iff.mp (by simpa [ex3_126_cscr] using hop) with h | h
            · exact congr_arg Prod.fst h
            · exfalso
              have h' := congr_arg Prod.snd (Set.mem_singleton_iff.mp h)
              simp [ex3_126_feed_back] at h'
              exact (by decide : (1 : Fin 2) ≠ 0) (congr_arg Sigma.fst h')
          suffices rsyOutAt SCR hOut x (connectedOutput SCR ⟨(1 : Fin 2), (0 : Nat)⟩ hC) =
              componentReadoutAt Z1 hOut1 1 (x 0) by
            simpa [heq] using this
          rw [heq]
          rw [rsyOutAt_eq_componentReadoutAt SCR hOut 0 (1 : Nat) x]
          exact ex3_124_readout_Z1 Z1 hOut1 1 (by decide) (x 0)
        · dsimp [uniformNatPortDecode, Fin.cases]
          rw [rsy_two_component_input_uiscr SCR hOut 1 extIn x (1 : Nat)
            (ex3_126_in_uiscr Z1 Z2' hPort2 ⟨(1 : Fin 2), (1 : Nat)⟩ (by decide) (by decide))]
          dsimp [extIn, ex3_126_extIn, ex3_126_extInVal]; rfl
        · dsimp [uniformNatPortDecode, Fin.cases]
          rw [rsy_two_component_input_uiscr SCR hOut 1 extIn x (2 : Nat)
            (ex3_126_in_uiscr Z1 Z2' hPort2 ⟨(1 : Fin 2), (2 : Nat)⟩ (by decide) (by decide))]
          dsimp [extIn, ex3_126_extIn, ex3_126_extInVal]; rfl
      rw [hfin]
    · dsimp [rsyOutAt]
      exact ex3_124_readout_Z1 Z1 hOut1 0 (by decide) (x 0)

/--
  [textbook/exercise3.126/theorem/mixed_readout_audit]
  Lean readout is `R1Z1(x1)`; textbook states `R1Z1(x2)` (likely typo).
-/
theorem ex3_126_readout_is_R1Z1_x1
    (Z1 : DiscreteSystem Nat (Fin 2 → Nat) (Fin 2 → Nat))
    (Z2' : DiscreteSystem Nat (Fin 3 → Nat) (Fin 1 → Nat))
    (hPort2 : DependsOnInputPort Z2' 2)
    (hOut1 : AlwaysOutputs Z1) (hOut2 : AlwaysOutputs Z2') (x : Fin 2 → Nat) :
    let SCR := ex3_126_scr Z1 Z2' hPort2
    let hOut := ex3_124_vscr_hOut Z1 Z2' hPort2 hOut1 hOut2
    rsyOutAt SCR hOut x ⟨(0 : Fin 2), (0 : Nat)⟩ =
      componentReadoutAt Z1 hOut1 (0 : Fin 2) (x 0) := by
  intro SCR hOut
  dsimp [rsyOutAt]
  exact ex3_124_readout_Z1 Z1 hOut1 0 (by decide) (x 0)

/-! ## Exercise 3.127: resultant vs conjunctive readout -/

/--
  [textbook/exercise3.127/theorem/resultant_conjunctive_readout]
  On conjunctive recipes, `RSY(SCR)` readout at unconnected outputs equals `CSY(VSCR)` readout.
-/
abbrev ex3_127_resultant_conjunctive_readout {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (x : rsy_SZ SCR) (op : Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  conjunctive_rsy_readout_eq_csy_readout SCR h hOut x op

/--
  [textbook/exercise3.127/theorem/rsy_RZ_eq_csy_readout_fun]
  Resultant readout function equals `CSY` readout on every unconnected output port.
-/
abbrev ex3_127_rsy_RZ_eq_csy_readout_fun {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (x : rsy_SZ SCR) :=
  conjunctive_rsy_RZ_eq_csy_readout_fun SCR h hOut x

/-! ## Exercise 3.128: a system that determines a nonsingular coupling recipe

Textbook data: a nonempty `A`, `n ≥ 2`, and `Ni ∈ FNS(A^(n+1), A)` for each `i`. Component `Zi`
has `SZi = A`, `IZi = OZi = A^(n+1)`, `NZi(x, p) = Ni(p)` and `RZi(x)` the constant vector `x`;
`CSCR = {(OiZj, IjZi)}` wires output `i` of `Zj` into input `j` of `Zi`, leaving port `n+1` of each
component free. Definition 3.3 requires the components of `VSCR` to be pairwise distinct, which the
textbook statement leaves implicit; since `Zi` is determined by `Ni`, that forces the extra
hypothesis `hN` below (with two equal `Ni` the hypotheses describe no connectable vector at all).
-/

/-- Component `Zi` of Ex. 3.128: state `A`, ports `A^(n+1)`, `NZi(x,p) = Ni(p)`, `RZi(x)` constant. -/
noncomputable def ex3_128_component {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (i : Fin n) :
    DiscreteSystem A (Fin (n + 1) → A) (Fin (n + 1) → A) :=
  DiscreteSystem.ofTotal (fun _ p => N i p) (fun x _ => x) inferInstance

lemma ex3_128_component_alwaysOutputs {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (i : Fin n) :
    AlwaysOutputs (ex3_128_component N i) :=
  ofTotal_alwaysOutputs _ _ _

/-- `RZi` is the constant vector, so every output port reports the state. -/
lemma ex3_128_component_readout {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (i : Fin n) (op : Fin (n + 1)) (x : A) :
    componentReadoutAt (ex3_128_component N i) (ex3_128_component_alwaysOutputs N i) op x = x := by
  have hspec := Classical.choose_spec (ex3_128_component_alwaysOutputs N i x)
  have hrz : (ex3_128_component N i).RZ x = some (fun _ => x) := rfl
  have heq : Classical.choose (ex3_128_component_alwaysOutputs N i x) = fun _ => x :=
    Option.some_injective _ (hspec.symm.trans hrz)
  simp [componentReadoutAt, heq]

/-- `Zi` determines `Ni`, so distinct components require distinct next-state functions. -/
lemma ex3_128_component_inj {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) {i j : Fin n}
    (h : HEq (ex3_128_component N i) (ex3_128_component N j)) : N i = N j := by
  have he : ex3_128_component N i = ex3_128_component N j := eq_of_heq h
  funext p
  have := congr_arg (fun Z => Z.NZ (Classical.choice ‹Nonempty A›) (some p)) he
  simpa [ex3_128_component, DiscreteSystem.ofTotal] using this

/-- `VSCR = (Z1,…,Zn)`: uniform state `A`, `n+1` input and output ports per component. -/
noncomputable def ex3_128_vscr {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) :
    PortSystemVector n where
  SZ := fun _ => A
  Port := fun _ => Fin (n + 1)
  PortVal := fun _ _ => A
  OutPort := fun _ => Fin (n + 1)
  OutPortVal := fun _ _ => A
  Z := ex3_128_component N
  distinct := fun i j hne h => hN i j hne (ex3_128_component_inj N h)

/-- The connection `(OiZj, IjZi)`: output port `i` of `Zj` feeds input port `j` of `Zi`. -/
def ex3_128_conn {n : Nat} (i j : Fin n) :
    (Σ (_ : Fin n), Fin (n + 1)) × (Σ (_ : Fin n), Fin (n + 1)) :=
  (⟨j, i.castSucc⟩, ⟨i, j.castSucc⟩)

/-- `CSCR = {(OiZj, IjZi) : (i,j) ∈ [1,n]²}`. -/
def ex3_128_cscr (n : Nat) :
    Set ((Σ (_ : Fin n), Fin (n + 1)) × (Σ (_ : Fin n), Fin (n + 1))) :=
  {p | ∃ i j : Fin n, p = ex3_128_conn i j}

/-- Port tags live in a constant fibre, so sigma equality splits into plain equalities. -/
private lemma ex3_128_sigma_eq {n : Nat} {j1 j2 : Fin n} {a1 a2 : Fin (n + 1)}
    (h : (⟨j1, a1⟩ : Σ (_ : Fin n), Fin (n + 1)) = ⟨j2, a2⟩) : j1 = j2 ∧ a1 = a2 := by
  simpa [Sigma.mk.injEq, heq_iff_eq] using h

lemma ex3_128_connectivity {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    IsSystemConnectivity (ex3_128_vscr N hN) (ex3_128_cscr n) := by
  have hpos : 0 < n := by omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro x y1 y2 ⟨i1, j1, h1⟩ ⟨i2, j2, h2⟩
    obtain ⟨hx1, hy1⟩ := Prod.mk.injEq .. ▸ h1
    obtain ⟨hx2, hy2⟩ := Prod.mk.injEq .. ▸ h2
    obtain ⟨hj, hi⟩ := ex3_128_sigma_eq (hx1.symm.trans hx2)
    have hi' : i1 = i2 := Fin.castSucc_inj.mp hi
    subst hi'; subst hj
    exact hy1.trans hy2.symm
  · rintro x1 x2 y ⟨i1, j1, h1⟩ ⟨i2, j2, h2⟩
    obtain ⟨hx1, hy1⟩ := Prod.mk.injEq .. ▸ h1
    obtain ⟨hx2, hy2⟩ := Prod.mk.injEq .. ▸ h2
    obtain ⟨hi, hj⟩ := ex3_128_sigma_eq (hy1.symm.trans hy2)
    have hj' : j1 = j2 := Fin.castSucc_inj.mp hj
    subst hi; subst hj'
    exact hx1.trans hx2.symm
  · intro heq
    have hnot : (⟨⟨0, hpos⟩, Fin.last n⟩ : Σ (_ : Fin n), Fin (n + 1)) ∉
        {x | ∃ y, (x, y) ∈ ex3_128_cscr n} := by
      rintro ⟨y, i, j, hp⟩
      obtain ⟨-, hlast⟩ :=
        ex3_128_sigma_eq (by simpa [ex3_128_conn] using congr_arg Prod.fst hp)
      exact absurd hlast.symm (Fin.castSucc_lt_last i).ne
    exact hnot (heq ▸ Set.mem_univ _)
  · intro heq
    have hnot : (⟨⟨0, hpos⟩, Fin.last n⟩ : Σ (_ : Fin n), Fin (n + 1)) ∉
        {y | ∃ x, (x, y) ∈ ex3_128_cscr n} := by
      rintro ⟨x, i, j, hp⟩
      obtain ⟨-, hlast⟩ :=
        ex3_128_sigma_eq (by simpa [ex3_128_conn] using congr_arg Prod.snd hp)
      exact absurd hlast.symm (Fin.castSucc_lt_last j).ne
    exact hnot (heq ▸ Set.mem_univ _)
  · intro _ _ _
    rfl

/-- `SCR = (VSCR, CSCR)` of Ex. 3.128. -/
noncomputable def ex3_128_scr {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    SystemCouplingRecipe n where
  VSCR := ex3_128_vscr N hN
  CSCR := ex3_128_cscr n
  connectivity := ex3_128_connectivity N hN hn

lemma ex3_128_hOut {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    ∀ i, AlwaysOutputs ((ex3_128_scr N hN hn).VSCR.Z i) :=
  fun i => ex3_128_component_alwaysOutputs N i

/-- The recipe is nonsingular: it has `n ≥ 2` components. -/
theorem ex3_128_not_singular {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    ¬ IsSingular (ex3_128_scr N hN hn) := by
  rintro ⟨h1, -⟩
  omega

/-- The recipe has genuine feedback: `CSCR ≠ ∅`. -/
theorem ex3_128_cscr_ne_empty {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    (ex3_128_scr N hN hn).CSCR ≠ ∅ := by
  have hpos : 0 < n := by omega
  intro hempty
  have hmem : ex3_128_conn (⟨0, hpos⟩ : Fin n) ⟨0, hpos⟩ ∈ (ex3_128_scr N hN hn).CSCR :=
    ⟨_, _, rfl⟩
  simpa [hempty] using hmem

/-- Input port `j` of component `i` is fed by output port `i` of component `j`. -/
lemma ex3_128_mem_ciscr {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (i j : Fin n) :
    (⟨i, j.castSucc⟩ : Σ (k : Fin n), (ex3_128_scr N hN hn).VSCR.Port k) ∈
      CISCR (ex3_128_scr N hN hn) :=
  (mem_ciscr_iff _ _).mpr ⟨⟨j, i.castSucc⟩, i, j, rfl⟩

/-- Input port `n+1` of each component is the only unconnected one. -/
lemma ex3_128_mem_uiscr {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (i : Fin n) :
    (⟨i, Fin.last n⟩ : Σ (k : Fin n), (ex3_128_scr N hN hn).VSCR.Port k) ∈
      UISCR (ex3_128_scr N hN hn) := by
  refine mem_uiscr_of_not_mem_ciscr _ _ ?_
  intro hC
  obtain ⟨op, i', j', hp⟩ := (mem_ciscr_iff _ _).mp hC
  have hsig : (⟨i, Fin.last n⟩ : Σ (_ : Fin n), Fin (n + 1)) = ⟨i', j'.castSucc⟩ :=
    congr_arg Prod.snd hp
  obtain ⟨-, hlast⟩ := ex3_128_sigma_eq hsig
  exact absurd hlast.symm (Fin.castSucc_lt_last j').ne

lemma ex3_128_connectedOutput {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (i j : Fin n) :
    connectedOutput (ex3_128_scr N hN hn) ⟨i, j.castSucc⟩ (ex3_128_mem_ciscr N hN hn i j) =
      ⟨j, i.castSucc⟩ :=
  (ex3_128_scr N hN hn).connectivity.1.2 _ _ _
    (connectedOutput_spec _ _ (ex3_128_mem_ciscr N hN hn i j)) ⟨i, j, rfl⟩

/-- External inputs: component `i` reads `gᵢ` on its single unconnected input port. -/
noncomputable def ex3_128_extIn {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (g : Fin n → A) : rsy_IZ (ex3_128_scr N hN hn) :=
  fun ip => g ip.val.1

/-- The resolved input of component `i` is `(x₁,…,xₙ, gᵢ)`. -/
lemma ex3_128_component_input {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (g : Fin n → A) (x : rsy_SZ (ex3_128_scr N hN hn)) (i : Fin n) :
    rsy_component_input_fun (ex3_128_scr N hN hn) (ex3_128_hOut N hN hn) i
        (ex3_128_extIn N hN hn g) x =
      Fin.snoc x (g i) := by
  funext p
  rcases Fin.eq_castSucc_or_eq_last p with ⟨j, hj⟩ | hlast
  · subst hj
    rw [rsy_component_input_ciscr _ _ _ _ _ _ (ex3_128_mem_ciscr N hN hn i j)]
    dsimp only
    rw [ex3_128_connectedOutput N hN hn i j, rsyOutAt_eq_componentReadoutAt]
    simpa using ex3_128_component_readout N j i.castSucc (x j)
  · subst hlast
    rw [rsy_component_input_uiscr _ _ _ _ _ _ (ex3_128_mem_uiscr N hN hn i)]
    simp [ex3_128_extIn]

/--
  [textbook/exercise3.128/theorem/rsy_next_state]
  `PJNᵢ(NZ@(x, g)) = Nᵢ(x₁,…,xₙ, gᵢ)`: the resultant's next state agrees with the given `Z0`.
-/
theorem ex3_128_rsy_NZ {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (g : Fin n → A) (x : rsy_SZ (ex3_128_scr N hN hn)) (i : Fin n) :
    rsy_NZ (ex3_128_scr N hN hn) (ex3_128_hOut N hN hn) x
        (some (ex3_128_extIn N hN hn g)) i =
      N i (Fin.snoc x (g i)) := by
  dsimp only [rsy_NZ, Option.map_some]
  rw [ex3_128_component_input N hN hn g x i]
  rfl

/--
  [textbook/exercise3.128/theorem/rsy_readout]
  `RZ@ = ID(SZ@)`: each component's readout reports its own state, so the resultant readout is
  the identity on `A^n`, matching `RZ0 = ID(SZ0)`.
-/
theorem ex3_128_rsy_readout {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n)
    (x : rsy_SZ (ex3_128_scr N hN hn)) (i : Fin n) (op : Fin (n + 1)) :
    rsyOutAt (ex3_128_scr N hN hn) (ex3_128_hOut N hN hn) x ⟨i, op⟩ = x i := by
  rw [rsyOutAt_eq_componentReadoutAt]
  simpa using ex3_128_component_readout N i op (x i)

/--
  [textbook/exercise3.128/theorem/determines_nonsingular_scr]
  Ex. 3.128 — the assertion holds. The stated data determine a nonsingular coupling recipe whose
  resultant is `Z0`: the state space is literally `A^n`, `PJNᵢ ∘ NZ@ = Nᵢ`, and `RZ@ = ID(SZ@)`.
-/
theorem ex3_128_determines_nonsingular_scr {A : Type} [Nonempty A] {n : Nat}
    (N : Fin n → (Fin (n + 1) → A) → A) (hN : ∀ i j, i ≠ j → N i ≠ N j) (hn : 2 ≤ n) :
    ¬ IsSingular (ex3_128_scr N hN hn) ∧
      (ex3_128_scr N hN hn).CSCR ≠ ∅ ∧
      (∀ (g : Fin n → A) (x : rsy_SZ (ex3_128_scr N hN hn)) (i : Fin n),
        rsy_NZ (ex3_128_scr N hN hn) (ex3_128_hOut N hN hn) x
            (some (ex3_128_extIn N hN hn g)) i =
          N i (Fin.snoc x (g i))) ∧
      (∀ (x : rsy_SZ (ex3_128_scr N hN hn)) (i : Fin n) (op : Fin (n + 1)),
        rsyOutAt (ex3_128_scr N hN hn) (ex3_128_hOut N hN hn) x ⟨i, op⟩ = x i) :=
  ⟨ex3_128_not_singular N hN hn, ex3_128_cscr_ne_empty N hN hn,
    ex3_128_rsy_NZ N hN hn, ex3_128_rsy_readout N hN hn⟩

/-! ## Exercise 3.129: recipe characterisation of the subsystem relation -/

/--
  [textbook/exercise3.129/theorem/subsystem_iff_recipes]
  `Z1` is a subsystem of `Z2` iff suitable coupling recipes exist (textbook (i)–(iv)).
-/
abbrev ex3_129_subsystem_iff_recipes {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2) :=
  subsystem_iff_recipes Z1 Z2

/-! ## Exercises 3.130 / 3.131: subsystem reflexivity and transitivity -/

/--
  [textbook/exercise3.130/theorem/subsystem_reflexive]
  Every resultant is a subsystem of itself.
-/
abbrev ex3_130_subsystem_reflexive {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (n : Nat) (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hZ : HEq Z (rsy SCR hOut)) :=
  subsystem_reflexive Z n SCR hOut hZ

/--
  [textbook/exercise3.131/theorem/subsystem_transitive]
  Subsystem relation is transitive: the recipe embeddings compose through the shared middle
  recipe, and forgetting the witnesses gives `IsSubsystemOf Z1 Z3`.
-/
abbrev ex3_131_subsystem_transitive {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    {n1 n2 n3 : Nat} {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    {SCR3 : SystemCouplingRecipe n3}
    {hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k)} {hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k)}
    {hOut3 : ∀ k, AlwaysOutputs (SCR3.VSCR.Z k)}
    {φ1 : Fin n1 → Fin n2} {φ2 : Fin n2 → Fin n3}
    (h12 : IsSubsystemVia Z1 Z2 SCR1 SCR2 hOut1 hOut2 φ1)
    (h23 : IsSubsystemVia Z2 Z3 SCR2 SCR3 hOut2 hOut3 φ2) :=
  subsystem_transitive_of_via h12 h23

/-! ## Exercise 3.132: singular SCR coupling function -/

/--
  [textbook/exercise3.132/theorem/singular_cfscr_eq_closed_loop]
  On singular recipes, `CFSCR(f,x)` equals closed-loop input as open-loop trajectory.
-/
abbrev ex3_132_singular_cfscr_eq_closed_loop {V : PortSystemVector 1}
    [∀ i p, Inhabited (V.PortVal i p)]
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i))
    (hOut : ∀ i, AlwaysOutputs (V.Z i))
    (f : rsyClosedLoopITZ (singularSCR V hOutNE hInNE))
    (x : rsy_SZ (singularSCR V hOutNE hInNE)) :=
  singular_cfscr_eq_closed_loop_trajectory (V := V) hOutNE hInNE hOut f x

abbrev ex3_132_singular_rsy_eq_component {V : PortSystemVector 1}
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i))
    (hOut : ∀ i, AlwaysOutputs (V.Z i)) :=
  singular_scr_rsy_agrees_component (V := V) hOutNE hInNE hOut

/-! ## Exercise 3.133: conjunctive SCR coupling function -/

/--
  [textbook/exercise3.133/theorem/conjunctive_cfscr_eq_closed_loop]
  On conjunctive recipes, `CFSCR(f,x)` equals closed-loop input lifted to open-loop ports.
-/
abbrev ex3_133_conjunctive_cfscr_eq_closed_loop {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) :=
  conjunctive_cfscr_eq_closed_loop_trajectory SCR h hOut f x

/--
  [textbook/exercise3.133/theorem/conjunctive_rsy_eq_csy]
  On conjunctive recipes, `RSY(SCR)` and `CSY(VSCR)` agree pointwise on next-state and readout.
-/
abbrev ex3_133_conjunctive_rsy_eq_csy {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :=
  conjunctive_rsy_agrees_csy SCR h hOut

end Mbse.TextbookExercises.Ch03
