import Mbse.Wymore
import Mbse.WymoreCouplingDynamic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card

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

/-- Component `i` has *some* order: it is of order `m` for at least one `m`. -/
def ComponentHasOrder {n : Nat} (SCR : SystemCouplingRecipe n) (i : Fin n) : Prop :=
  ∃ m, ComponentOrder SCR i m

/--
  [textbook/definition3.90/definition/null_order]
  Null order: not of order `m` for any `m`, i.e. no chain of `SCR` couplings reaches a component
  with an external interface.
-/
def ComponentNullOrder {n : Nat} (SCR : SystemCouplingRecipe n) (i : Fin n) : Prop :=
  ¬ ComponentHasOrder SCR i

lemma componentHasOrder_of_order0 {n : Nat} (SCR : SystemCouplingRecipe n) {i : Fin n}
    (h : ComponentOrder0 SCR i) : ComponentHasOrder SCR i := ⟨0, h⟩

/-- Having an order propagates along couplings: a neighbour of an ordered component is ordered. -/
lemma componentHasOrder_of_connection {n : Nat} (SCR : SystemCouplingRecipe n) {i j : Fin n}
    (hconn : HasSCRConnection SCR i j) (hj : ComponentHasOrder SCR j) :
    ComponentHasOrder SCR i := by
  obtain ⟨m, hm⟩ := hj
  exact ⟨m + 1, ⟨j, hm, hconn⟩⟩

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
    exact hnull ⟨0, Or.inl ⟨ip.2, hU⟩⟩

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

/-- Component indices of `SCR2` that host the embedded subsystem `φ : Fin n₁ → Fin n₂`. -/
def SCRSubsystemIndices {n1 n2 : Nat} (φ : Fin n1 → Fin n2) : Set (Fin n2) :=
  Set.range φ

/-- `CSCR₂` pairs whose tagged output and input indices lie in the embedded subsystem. -/
def SCRSubsystemCscrPairs {n1 n2 : Nat} (SCR2 : SystemCouplingRecipe n2) (φ : Fin n1 → Fin n2) :
    Set ((Σ (i : Fin n2), SCR2.VSCR.OutPort i) × (Σ (i : Fin n2), SCR2.VSCR.Port i)) :=
  {p | p.1.1 ∈ SCRSubsystemIndices φ ∧ p.2.1 ∈ SCRSubsystemIndices φ}

/-- Embed a `SCR₁` connection pair into `SCR₂` tagged port indices via `φ`. -/
def scrEmbedOutPort {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : PortSystemVector n1) (SCR2 : PortSystemVector n2)
    (hOut : ∀ i, HEq (SCR1.OutPort i) (SCR2.OutPort (φ i)))
    (op : Σ (i : Fin n1), SCR1.OutPort i) : Σ (i : Fin n2), SCR2.OutPort i :=
  ⟨φ op.1, eq_of_heq (hOut op.1) ▸ op.2⟩

/-- Embed a `SCR₁` input port tag into `SCR₂`. -/
def scrEmbedInPort {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : PortSystemVector n1) (SCR2 : PortSystemVector n2)
    (hIn : ∀ i, HEq (SCR1.Port i) (SCR2.Port (φ i)))
    (ip : Σ (i : Fin n1), SCR1.Port i) : Σ (i : Fin n2), SCR2.Port i :=
  ⟨φ ip.1, eq_of_heq (hIn ip.1) ▸ ip.2⟩

/-- Embed a `SCR₁` `CSCR` pair into `SCR₂` port tags. -/
def scrEmbedCscrPair {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOut : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
    (hIn : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i)))
    (p : (Σ (i : Fin n1), SCR1.VSCR.OutPort i) × (Σ (i : Fin n1), SCR1.VSCR.Port i)) :
    (Σ (i : Fin n2), SCR2.VSCR.OutPort i) × (Σ (i : Fin n2), SCR2.VSCR.Port i) :=
  (scrEmbedOutPort φ SCR1.VSCR SCR2.VSCR hOut p.1, scrEmbedInPort φ SCR1.VSCR SCR2.VSCR hIn p.2)

lemma scrEmbedCscrPair_fst {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOut : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
    (hIn : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i)))
    (p : (Σ (i : Fin n1), SCR1.VSCR.OutPort i) × (Σ (i : Fin n1), SCR1.VSCR.Port i)) :
    (scrEmbedCscrPair φ SCR1 SCR2 hOut hIn p).1.1 = φ p.1.1 := rfl

lemma scrEmbedCscrPair_snd {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOut : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
    (hIn : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i)))
    (p : (Σ (i : Fin n1), SCR1.VSCR.OutPort i) × (Σ (i : Fin n1), SCR1.VSCR.Port i)) :
    (scrEmbedCscrPair φ SCR1 SCR2 hOut hIn p).2.1 = φ p.2.1 := rfl

lemma heq_of_eq' {α : Sort u} {a b : α} (h : a = b) : HEq a b :=
  h ▸ HEq.rfl

/-- Casting along a composite port-type `HEq` agrees with casting along each factor in turn. -/
lemma eq_of_heq_trans_cast {A B C : Sort u} (h1 : HEq A B) (h2 : HEq B C) (a : A) :
    eq_of_heq (HEq.trans h1 h2) ▸ a = eq_of_heq h2 ▸ (eq_of_heq h1 ▸ a) := by
  cases h1
  cases h2
  rfl

lemma scrEmbedOutPort_comp {n1 n2 n3 : Nat}
    (φ1 : Fin n1 → Fin n2) (φ2 : Fin n2 → Fin n3)
    (SCR1 : PortSystemVector n1) (SCR2 : PortSystemVector n2) (SCR3 : PortSystemVector n3)
    (hOut12 : ∀ i, HEq (SCR1.OutPort i) (SCR2.OutPort (φ1 i)))
    (hOut23 : ∀ i, HEq (SCR2.OutPort i) (SCR3.OutPort (φ2 i)))
    (op : Σ (i : Fin n1), SCR1.OutPort i) :
    scrEmbedOutPort (φ2 ∘ φ1) SCR1 SCR3
        (fun i => HEq.trans (hOut12 i) (hOut23 (φ1 i))) op =
      scrEmbedOutPort φ2 SCR2 SCR3 hOut23 (scrEmbedOutPort φ1 SCR1 SCR2 hOut12 op) := by
  dsimp [scrEmbedOutPort]
  ext
  · simp
  · exact heq_of_eq' (eq_of_heq_trans_cast (hOut12 op.1) (hOut23 (φ1 op.1)) op.2)

lemma scrEmbedInPort_comp {n1 n2 n3 : Nat}
    (φ1 : Fin n1 → Fin n2) (φ2 : Fin n2 → Fin n3)
    (SCR1 : PortSystemVector n1) (SCR2 : PortSystemVector n2) (SCR3 : PortSystemVector n3)
    (hIn12 : ∀ i, HEq (SCR1.Port i) (SCR2.Port (φ1 i)))
    (hIn23 : ∀ i, HEq (SCR2.Port i) (SCR3.Port (φ2 i)))
    (ip : Σ (i : Fin n1), SCR1.Port i) :
    scrEmbedInPort (φ2 ∘ φ1) SCR1 SCR3
        (fun i => HEq.trans (hIn12 i) (hIn23 (φ1 i))) ip =
      scrEmbedInPort φ2 SCR2 SCR3 hIn23 (scrEmbedInPort φ1 SCR1 SCR2 hIn12 ip) := by
  dsimp [scrEmbedInPort]
  ext
  · simp
  · exact heq_of_eq' (eq_of_heq_trans_cast (hIn12 ip.1) (hIn23 (φ1 ip.1)) ip.2)

lemma scrEmbedCscrPair_comp {n1 n2 n3 : Nat}
    (φ1 : Fin n1 → Fin n2) (φ2 : Fin n2 → Fin n3)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2) (SCR3 : SystemCouplingRecipe n3)
    (hOut12 : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ1 i)))
    (hIn12 : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ1 i)))
    (hOut23 : ∀ i, HEq (SCR2.VSCR.OutPort i) (SCR3.VSCR.OutPort (φ2 i)))
    (hIn23 : ∀ i, HEq (SCR2.VSCR.Port i) (SCR3.VSCR.Port (φ2 i)))
    (p : (Σ (i : Fin n1), SCR1.VSCR.OutPort i) × (Σ (i : Fin n1), SCR1.VSCR.Port i)) :
    scrEmbedCscrPair (φ2 ∘ φ1) SCR1 SCR3
        (fun i => HEq.trans (hOut12 i) (hOut23 (φ1 i)))
        (fun i => HEq.trans (hIn12 i) (hIn23 (φ1 i))) p =
      scrEmbedCscrPair φ2 SCR2 SCR3 hOut23 hIn23
        (scrEmbedCscrPair φ1 SCR1 SCR2 hOut12 hIn12 p) := by
  dsimp [scrEmbedCscrPair]
  congr 1
  · exact scrEmbedOutPort_comp φ1 φ2 SCR1.VSCR SCR2.VSCR SCR3.VSCR hOut12 hOut23 p.1
  · exact scrEmbedInPort_comp φ1 φ2 SCR1.VSCR SCR2.VSCR SCR3.VSCR hIn12 hIn23 p.2

lemma scrEmbedCscrPair_mem_subsystem {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOut : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
    (hIn : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i)))
    (p : (Σ (i : Fin n1), SCR1.VSCR.OutPort i) × (Σ (i : Fin n1), SCR1.VSCR.Port i)) :
    scrEmbedCscrPair φ SCR1 SCR2 hOut hIn p ∈ SCRSubsystemCscrPairs SCR2 φ := by
  dsimp [scrEmbedCscrPair, SCRSubsystemCscrPairs, SCRSubsystemIndices]
  refine ⟨?_, ?_⟩
  · exact ⟨p.1.1, rfl⟩
  · exact ⟨p.2.1, rfl⟩

/-- Textbook (iv): `CSCR₁` equals `CSCR₂` restricted to subsystem port pairs. -/
def SCRSubsystemCSCRRestriction {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOutPort : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
    (hInPort : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i))) : Prop :=
  ∀ p,
    p ∈ SCR1.CSCR ↔
      scrEmbedCscrPair φ SCR1 SCR2 hOutPort hInPort p ∈ SCR2.CSCR ∩ SCRSubsystemCscrPairs SCR2 φ

/--
  Recipe-level form of the subsystem relation: `φ` embeds `VSCR₁` into `VSCR₂` preserving
  components and port structure (textbook (iii)), and `CSCR₁` is `CSCR₂` restricted to the
  embedded ports (textbook (iv)).
-/
structure IsSubrecipeOf {n1 n2 : Nat} (φ : Fin n1 → Fin n2)
    (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2) : Prop where
  /-- Distinct components of `SCR₁` embed to distinct components of `SCR₂`. -/
  inj : Function.Injective φ
  /-- Output port tags are preserved by the embedding. -/
  outPort : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i))
  /-- Input port tags are preserved by the embedding. -/
  inPort : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i))
  /-- Embedded components are the same systems. -/
  component : ∀ i, HEq (SCR1.VSCR.Z i) (SCR2.VSCR.Z (φ i))
  /-- Textbook (iv): `CSCR₁` is the restriction of `CSCR₂` to embedded ports. -/
  cscr : SCRSubsystemCSCRRestriction φ SCR1 SCR2 outPort inPort

/--
  [textbook/definition3.97/definition/is_subsystem_of]
  `Z1` is a subsystem of `Z2` when both are resultants of recipes with nested component vectors
  and `CSCR1` is the restriction of `CSCR2` to subsystem ports (textbook (iv)).
-/
def IsSubsystemOf {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1)
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  ∃ (n1 n2 : Nat) (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
      (hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k))
      (hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k))
      (φ : Fin n1 → Fin n2)
      (hOutPort : ∀ i, HEq (SCR1.VSCR.OutPort i) (SCR2.VSCR.OutPort (φ i)))
      (hInPort : ∀ i, HEq (SCR1.VSCR.Port i) (SCR2.VSCR.Port (φ i))),
    Function.Injective φ ∧
    (∀ i, HEq (SCR1.VSCR.Z i) (SCR2.VSCR.Z (φ i))) ∧
    HEq Z1 (rsy SCR1 hOut1) ∧
    HEq Z2 (rsy SCR2 hOut2) ∧
    SCRSubsystemCSCRRestriction φ SCR1 SCR2 hOutPort hInPort

/--
  `Z1` is a subsystem of `Z2` *via* the named recipe witnesses. Recording the witnesses is what
  makes the relation composable: a resultant does not determine its own coupling recipe, so the
  witness-free `IsSubsystemOf` cannot be chained directly (see `subsystem_transitive`).
-/
def IsSubsystemVia {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2)
    {n1 n2 : Nat} (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
    (hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k)) (hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k))
    (φ : Fin n1 → Fin n2) : Prop :=
  IsSubrecipeOf φ SCR1 SCR2 ∧ HEq Z1 (rsy SCR1 hOut1) ∧ HEq Z2 (rsy SCR2 hOut2)

/-- Forgetting the recipe witnesses recovers the witness-free subsystem relation. -/
theorem IsSubsystemVia.isSubsystemOf {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {n1 n2 : Nat} {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    {hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k)} {hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k)}
    {φ : Fin n1 → Fin n2}
    (h : IsSubsystemVia Z1 Z2 SCR1 SCR2 hOut1 hOut2 φ) :
    IsSubsystemOf Z1 Z2 :=
  ⟨n1, n2, SCR1, SCR2, hOut1, hOut2, φ, h.1.outPort, h.1.inPort,
    h.1.inj, h.1.component, h.2.1, h.2.2, h.1.cscr⟩

/-! ## Exercise 3.129: recipe characterisation of the subsystem relation -/

/--
  [textbook/exercise3.129/theorem/subsystem_iff_recipes]
  Ex. 3.129 — the assertion holds. `Z1` is a subsystem of `Z2` exactly when there are coupling
  recipes with `Z1 = RSY(SCR1)` (i), `Z2 = RSY(SCR2)` (ii), `VSCR1 ⊆ VSCR2` via an injective
  component embedding (iii), and `CSCR1` the restriction of `CSCR2` to the embedded output/input
  ports (iv). Clauses (iii)–(iv) are exactly `IsSubrecipeOf`.
-/
theorem subsystem_iff_recipes {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2) :
    IsSubsystemOf Z1 Z2 ↔
      ∃ (n1 n2 : Nat) (SCR1 : SystemCouplingRecipe n1) (SCR2 : SystemCouplingRecipe n2)
        (hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k))
        (hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k))
        (φ : Fin n1 → Fin n2),
        IsSubsystemVia Z1 Z2 SCR1 SCR2 hOut1 hOut2 φ := by
  constructor
  · rintro ⟨n1, n2, SCR1, SCR2, hOut1, hOut2, φ, hOutPort, hInPort, hinj, hcomp, hZ1, hZ2, hcscr⟩
    exact ⟨n1, n2, SCR1, SCR2, hOut1, hOut2, φ, ⟨hinj, hOutPort, hInPort, hcomp, hcscr⟩, hZ1, hZ2⟩
  · rintro ⟨n1, n2, SCR1, SCR2, hOut1, hOut2, φ, h⟩
    exact IsSubsystemVia.isSubsystemOf h

/-! ## Exercises 3.130 / 3.131: subsystem reflexivity and transitivity -/

/-- Every recipe is a subrecipe of itself via the identity embedding. -/
theorem subrecipe_refl {n : Nat} (SCR : SystemCouplingRecipe n) : IsSubrecipeOf id SCR SCR where
  inj := Function.injective_id
  outPort := fun _ => HEq.rfl
  inPort := fun _ => HEq.rfl
  component := fun _ => HEq.rfl
  cscr := by
    intro p
    constructor
    · intro hp
      exact ⟨hp, scrEmbedCscrPair_mem_subsystem id SCR SCR (fun _ => HEq.rfl) (fun _ => HEq.rfl) p⟩
    · intro hp
      exact hp.1

/--
  Subrecipe embeddings compose: `φ₂ ∘ φ₁` embeds `SCR₁` into `SCR₃`, and the `CSCR`
  restrictions chain through the middle recipe.
-/
theorem subrecipe_trans {n1 n2 n3 : Nat}
    {φ1 : Fin n1 → Fin n2} {φ2 : Fin n2 → Fin n3}
    {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    {SCR3 : SystemCouplingRecipe n3}
    (h12 : IsSubrecipeOf φ1 SCR1 SCR2) (h23 : IsSubrecipeOf φ2 SCR2 SCR3) :
    IsSubrecipeOf (φ2 ∘ φ1) SCR1 SCR3 where
  inj := h23.inj.comp h12.inj
  outPort := fun i => HEq.trans (h12.outPort i) (h23.outPort (φ1 i))
  inPort := fun i => HEq.trans (h12.inPort i) (h23.inPort (φ1 i))
  component := fun i => HEq.trans (h12.component i) (h23.component (φ1 i))
  cscr := by
    intro p
    have hcomp :=
      scrEmbedCscrPair_comp φ1 φ2 SCR1 SCR2 SCR3
        h12.outPort h12.inPort h23.outPort h23.inPort p
    have hmid :=
      scrEmbedCscrPair_mem_subsystem φ1 SCR1 SCR2 h12.outPort h12.inPort p
    constructor
    · intro hp
      have h2 := (h12.cscr p).mp hp
      have h3 := (h23.cscr (scrEmbedCscrPair φ1 SCR1 SCR2 h12.outPort h12.inPort p)).mp h2.1
      refine ⟨?_, scrEmbedCscrPair_mem_subsystem (φ2 ∘ φ1) SCR1 SCR3 _ _ p⟩
      rw [hcomp]
      exact h3.1
    · intro hp
      refine (h12.cscr p).mpr ⟨?_, hmid⟩
      refine (h23.cscr (scrEmbedCscrPair φ1 SCR1 SCR2 h12.outPort h12.inPort p)).mpr ⟨?_, ?_⟩
      · rw [← hcomp]; exact hp.1
      · exact scrEmbedCscrPair_mem_subsystem φ2 SCR2 SCR3 h23.outPort h23.inPort _

/--
  [textbook/exercise3.130/theorem/subsystem_reflexive]
  Every resultant is a subsystem of itself (`φ = id`, `CSCR` restriction is reflexive).
-/
theorem subsystem_reflexive {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (n : Nat) (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hZ : HEq Z (rsy SCR hOut)) :
    IsSubsystemOf Z Z :=
  IsSubsystemVia.isSubsystemOf ⟨subrecipe_refl SCR, hZ, hZ⟩

lemma Fin.not_heq_of_lt {n m : Nat} (hlt : n < m) : ¬ HEq (Fin n) (Fin m) := by
  intro h
  exact Nat.ne_of_lt hlt (fin_injective (eq_of_heq h))

lemma Fin.not_heq_of_ne {n m : Nat} (h : n ≠ m) : ¬ HEq (Fin n) (Fin m) := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · exact Fin.not_heq_of_lt hlt
  · intro heq; exact Fin.not_heq_of_lt hgt (HEq.symm heq)

/--
  [textbook/exercise3.131/theorem/subsystem_transitive]
  The subsystem relation is transitive: the embeddings compose as `φ₂ ∘ φ₁` and the `CSCR`
  restrictions chain through the shared middle recipe.

  Transitivity is stated on `IsSubsystemVia` rather than `IsSubsystemOf` because a resultant does
  not determine its own coupling recipe: from `HEq Z2 (rsy SCR2 _)` and `HEq Z2 (rsy SCR2' _)` the
  equality `SCR2 = SCR2'` is not derivable (it would need injectivity of `Pi` types in the index,
  which Lean's type theory does not provide). Naming the middle recipe supplies exactly the
  identification the textbook argument uses implicitly.
-/
theorem subsystem_transitive {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    {n1 n2 n3 : Nat} {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    {SCR3 : SystemCouplingRecipe n3}
    {hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k)} {hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k)}
    {hOut3 : ∀ k, AlwaysOutputs (SCR3.VSCR.Z k)}
    {φ1 : Fin n1 → Fin n2} {φ2 : Fin n2 → Fin n3}
    (h12 : IsSubsystemVia Z1 Z2 SCR1 SCR2 hOut1 hOut2 φ1)
    (h23 : IsSubsystemVia Z2 Z3 SCR2 SCR3 hOut2 hOut3 φ2) :
    IsSubsystemVia Z1 Z3 SCR1 SCR3 hOut1 hOut3 (φ2 ∘ φ1) :=
  ⟨subrecipe_trans h12.1 h23.1, h12.2.1, h23.2.2⟩

/--
  [textbook/exercise3.131/theorem/subsystem_transitive]
  Witness-free form of Ex. 3.131: chaining two witnessed subsystem facts yields `IsSubsystemOf`.
-/
theorem subsystem_transitive_of_via {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    {n1 n2 n3 : Nat} {SCR1 : SystemCouplingRecipe n1} {SCR2 : SystemCouplingRecipe n2}
    {SCR3 : SystemCouplingRecipe n3}
    {hOut1 : ∀ k, AlwaysOutputs (SCR1.VSCR.Z k)} {hOut2 : ∀ k, AlwaysOutputs (SCR2.VSCR.Z k)}
    {hOut3 : ∀ k, AlwaysOutputs (SCR3.VSCR.Z k)}
    {φ1 : Fin n1 → Fin n2} {φ2 : Fin n2 → Fin n3}
    (h12 : IsSubsystemVia Z1 Z2 SCR1 SCR2 hOut1 hOut2 φ1)
    (h23 : IsSubsystemVia Z2 Z3 SCR2 SCR3 hOut2 hOut3 φ2) :
    IsSubsystemOf Z1 Z3 :=
  (subsystem_transitive h12 h23).isSubsystemOf
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
