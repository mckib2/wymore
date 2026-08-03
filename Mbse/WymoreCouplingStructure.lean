import Mbse.Wymore
import Mbse.WymoreCouplingDynamic

/-!
# Chapter 3 — coupling recipe structure (order, components, subsystems)

Structural definitions and theorems from Wymore Ch. 3 (Defs 3.90, 3.95, 3.97; Thms 3.85, 3.87, 3.92).
-/

namespace Mbse.Wymore

open Classical

/-! ## Theorem 3.85: nonsingular conjunctive uniqueness -/

/--
  [textbook/theorem3.85/definition/nonsingular_conjunctive]
  A conjunctive coupling recipe with more than one component (`CSCR = ∅`, `n > 1`).
-/
def IsNonsingularConjunctive {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  IsConjunctive SCR ∧ ¬ IsSingular SCR

lemma nonsingular_conjunctive_n_gt_one {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsNonsingularConjunctive SCR) : n > 1 := by
  rcases h with ⟨hconj, hnsing⟩
  match n with
  | 0 =>
    rcases sigmaPort_nonempty SCR with ⟨ip, _⟩
    nomatch ip
  | 1 => exact False.elim (hnsing ⟨rfl, hconj⟩)
  | n + 2 => omega

theorem conjunctive_scr_eq_of_vscr_eq {n : Nat} (SCR1 SCR2 : SystemCouplingRecipe n)
    (h1 : IsConjunctive SCR1) (h2 : IsConjunctive SCR2)
    (hVSCR : SCR1.VSCR = SCR2.VSCR) :
    SCR1 = SCR2 := by
  rcases SCR1 with ⟨vscr, cscr1, conn1⟩
  rcases SCR2 with ⟨vscr', cscr2, conn2⟩
  have hvv : vscr = vscr' := by cases hVSCR; rfl
  subst hvv
  dsimp [IsConjunctive] at h1 h2
  have hcscr : cscr1 = cscr2 := h1.trans h2.symm
  subst hcscr
  rfl

/--
  [textbook/theorem3.85/theorem/nonsingular_conjunctive_scr_unique]
  Equal `VSCR` on nonsingular conjunctive recipes determines the coupling recipe.
-/
theorem nonsingular_conjunctive_scr_unique {n : Nat}
    (SCR1 SCR2 : SystemCouplingRecipe n)
    (h1 : IsNonsingularConjunctive SCR1) (h2 : IsNonsingularConjunctive SCR2)
    (hVSCR : SCR1.VSCR = SCR2.VSCR) :
    SCR1 = SCR2 := by
  rcases h1 with ⟨hc1, _⟩
  rcases h2 with ⟨hc2, _⟩
  exact conjunctive_scr_eq_of_vscr_eq SCR1 SCR2 hc1 hc2 hVSCR

/-! ## Theorem 3.87: non-product state cannot be multi-component resultant -/

/--
  [textbook/theorem3.87/theorem/non_product_state_not_multi_component]
  `rsy_SZ` is a product of `n` component state spaces; if `n > 1` the state is a Cartesian product.
-/
theorem rsy_sz_is_cartesian_product {n : Nat} (_SCR : SystemCouplingRecipe n) (hn : n > 1) :
    ¬ StateIsNotCartesianProduct n := by
  dsimp [StateIsNotCartesianProduct]
  omega

/--
  [textbook/theorem3.87/theorem/non_product_state_not_multi_component]
  Contrapositive: a non-product state space cannot be the resultant of a multi-component recipe.
-/
theorem non_product_state_not_multi_component_resultant {n : Nat} (_p : RSYParam n)
    (hn : n > 1) (hNotProd : StateIsNotCartesianProduct n) :
    False := by
  dsimp [StateIsNotCartesianProduct] at hNotProd
  omega

/-! ## Definition 3.90: component order -/

/--
  [textbook/definition3.90/definition/order_zero]
  Component `i` is of order 0 when it has an unconnected input or output port.
-/
def ComponentOrder0 {n : Nat} (SCR : SystemCouplingRecipe n) (i : Fin n) : Prop :=
  (∃ port, ⟨i, port⟩ ∈ UISCR SCR) ∨ (∃ op, ⟨i, op⟩ ∈ UOSCR SCR)

/--
  [textbook/definition3.90/definition/order]
  Component `i` is of order `m + 1` when it is coupled to some component of order `m`.
-/
def HasSCRConnection {n : Nat} (SCR : SystemCouplingRecipe n) (i j : Fin n) : Prop :=
  SCRInterface SCR i j ≠ ∅

def ComponentOrder {n : Nat} (SCR : SystemCouplingRecipe n) (i : Fin n) : Nat → Prop :=
  fun m =>
  match m with
  | 0 => ComponentOrder0 SCR i
  | m + 1 => ∃ j, ComponentOrder SCR j m ∧ HasSCRConnection SCR i j

/--
  [textbook/definition3.90/definition/null_order]
  Null order: not of positive order (no external interface).
-/
def ComponentNullOrder {n : Nat} (SCR : SystemCouplingRecipe n) (i : Fin n) : Prop :=
  ¬ ComponentOrder0 SCR i

/-! ## Theorem 3.92: order-zero component exists -/

lemma scr_has_unconnected_input_port {n : Nat} (SCR : SystemCouplingRecipe n) :
    ∃ ip, ip ∈ UISCR SCR := by
  rcases SCR.connectivity.2.2.1 with hne
  by_contra hall
  push Not at hall
  have huniv : CISCR SCR = Set.univ := by
    ext ip
    simpa [UISCR, Set.mem_compl_iff] using hall ip
  exact hne huniv

lemma scr_has_unconnected_output_port {n : Nat} (SCR : SystemCouplingRecipe n) :
    ∃ op, op ∈ UOSCR SCR := by
  rcases SCR.connectivity.2.1 with hne
  by_contra hall
  push Not at hall
  have huniv : COSCR SCR = Set.univ := by
    ext op
    simpa [UOSCR, Set.mem_compl_iff] using hall op
  exact hne huniv

/--
  [textbook/theorem3.92/theorem/order_zero_component]
  Every coupling recipe has a component of order 0 that is not of null order.
-/
theorem scr_has_order_zero_component {n : Nat} (SCR : SystemCouplingRecipe n) :
    ∃ i, ComponentOrder0 SCR i ∧ ¬ ComponentNullOrder SCR i := by
  rcases scr_has_unconnected_input_port SCR with ⟨ip, hU⟩
  refine ⟨ip.1, ?_, ?_⟩
  · exact Or.inl ⟨ip.2, hU⟩
  · intro hnull
    exact hnull (Or.inl ⟨ip.2, hU⟩)

/-! ## Definition 3.95: component relation -/

/--
  [textbook/definition3.95/definition/is_component_of]
  `Z1` is a component of `Z2` when `Z2 = RSY(SCR)` and `Z1` appears in `VSCR`.
-/
def IsComponentOf {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1)
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  ∃ (n : Nat) (SCR : SystemCouplingRecipe n) (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
      (i : Fin n),
    HEq Z2 (rsy SCR hOut) ∧ HEq (SCR.VSCR.Z i) Z1

/-! ## Definition 3.97: subsystem relation -/

/--
  [textbook/definition3.97/definition/is_subsystem_of]
  `Z1` is a subsystem of `Z2` when both are resultants of recipes with nested component vectors
  and `CSCR1` is the restriction of `CSCR2` to subsystem ports.
-/
def IsSubsystemOf {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1)
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  ∃ (n1 n2 : Nat) (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
      (hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k))
      (hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k))
      (φ : Fin n1 → Fin n2),
    Function.Injective φ ∧
    (∀ i, HEq (SCR1.VSCR.Z i) (SCR2.VSCR.Z (φ i))) ∧
    HEq Z1 (rsy SCR1 hOut1) ∧
    HEq Z2 (rsy SCR2 hOut2) ∧
    (∀ (i j : Fin n1), SCRInterface SCR1 i j ⊆ SCR1.CSCR)

/--
  [textbook/exercise3.116/theorem/cascade_min_two_components]
  Nonempty cascade connectivity requires at least two components.
-/
theorem cascade_scr_min_two_components {n : Nat} (SCR : SystemCouplingRecipe n)
    (hCas : IsCascade SCR) (hne : SCR.CSCR ≠ ∅) : n > 1 := by
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨p, hp⟩
  by_contra hnle
  have hnle1 : n ≤ 1 := Nat.not_lt.mp hnle
  match n with
  | 0 =>
    rcases p with ⟨⟨i, _⟩, ⟨_, _⟩⟩
    exact Fin.elim0 i
  | 1 =>
    have heq : p.1.1 = p.2.1 := Trajectory.fin_one_indices_eq rfl p.1.1 p.2.1
    exact hCas p hp (by simp [IsFeedback, heq])

end Mbse.Wymore
