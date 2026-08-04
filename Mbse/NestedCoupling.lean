import Mbse.CouplingIsomorphism
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exercise 4.86 — coupling components of components

If every component `Zᵢ` of a coupling recipe is itself a resultant `Zᵢ = RSY(SCRᵢ)`, the
components of the `SCRᵢ` can be gathered into a single connectable vector
`VSCR$ = (Z₁₁, …, Z₁m₁, …, Zₙ₁, …, Zₙmₙ)` whose connectivity `CSCR$` consists of the internal
connections of every `SCRᵢ` together with the external connections of `CSCR`, read on the ports of
the components that carry them. The resultant of the flattened recipe is isomorphic to the
original resultant, the state isomorphism being the currying
`(x₁₁, …, xₙmₙ) ↦ ((x₁₁, …, x₁m₁), …, (xₙ₁, …, xₙmₙ))`.

Component indices of the flattened recipe are `Fin (∑ i, mᵢ)`, identified with the dependent pairs
`Σ i, Fin mᵢ` by `finSigmaFinEquiv`; all constructions below are phrased on the pair form and
transported by that equivalence.
-/

namespace Homomorphism

open Homomorphism Mbse.Wymore

/-! ## The nested recipe -/

/--
  [textbook/exercise4.86/definition/nested_components]
  For each `i`, a coupling recipe `SCRᵢ` whose resultant will be the component `Zᵢ = RSY(SCRᵢ)`.
  The two distinctness conditions say that `VSCR` and the flattened `VSCR$` are connectable
  vectors (pairwise distinct components).
-/
structure NestedComponents (n : Nat) where
  /-- `mᵢ`, the number of components of `SCRᵢ`. -/
  m : Fin n → Nat
  /-- The inner recipes `SCRᵢ`. -/
  sub : (i : Fin n) → SystemCouplingRecipe (m i)
  /-- Inner components have total readouts, so `RSY(SCRᵢ)` is defined. -/
  hOut : (i : Fin n) → ∀ j, AlwaysOutputs ((sub i).VSCR.Z j)
  /-- `VSCR = (RSY(SCR₁), …, RSY(SCRₙ))` is a connectable vector. -/
  distinctOuter : ∀ i i', i ≠ i' → ¬ HEq (rsy (sub i) (hOut i)) (rsy (sub i') (hOut i'))
  /-- `VSCR$` is a connectable vector. -/
  distinctInner : ∀ x y : Σ i, Fin (m i), x ≠ y →
    ¬ HEq ((sub x.1).VSCR.Z x.2) ((sub y.1).VSCR.Z y.2)

/-- [textbook/exercise4.86/definition/outer_vector] `VSCR = (Z₁, …, Zₙ)` with `Zᵢ = RSY(SCRᵢ)`. -/
noncomputable def nestVector {n : Nat} (N : NestedComponents n) : PortSystemVector n where
  SZ := fun i => rsy_SZ (N.sub i)
  Port := fun i => UnconnInPort (N.sub i)
  PortVal := fun i p => (N.sub i).VSCR.PortVal p.val.1 p.val.2
  OutPort := fun i => UnconnOutPort (N.sub i)
  OutPortVal := fun i q => (N.sub i).VSCR.OutPortVal q.val.1 q.val.2
  Z := fun i => rsy (N.sub i) (N.hOut i)
  distinct := N.distinctOuter

/--
  [textbook/exercise4.86/definition/nested_recipe]
  `SCR = (VSCR, CSCR)` with `Zᵢ = RSY(SCRᵢ)`: the outer recipe couples the inner resultants.
-/
structure NestedCoupling (n : Nat) extends NestedComponents n where
  /-- The outer connectivity, on the external ports of the inner resultants. -/
  CSCR : Set ((Σ i, UnconnOutPort (sub i)) × (Σ i, UnconnInPort (sub i)))
  connectivity : IsSystemConnectivity (nestVector toNestedComponents) CSCR

/-- [textbook/exercise4.86/definition/nested_recipe] `SCR = (VSCR, CSCR)`. -/
noncomputable def nestRecipe {n : Nat} (N : NestedCoupling n) : SystemCouplingRecipe n where
  VSCR := nestVector N.toNestedComponents
  CSCR := N.CSCR
  connectivity := N.connectivity

/-- A resultant always produces an output, so the outer recipe again has total readouts. -/
theorem rsy_alwaysOutputs {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) : AlwaysOutputs (rsy SCR hOut) :=
  fun x => ⟨fun op => rsyOutAt SCR hOut x op.val, rfl⟩

/-- Total readouts of the outer components `Zᵢ = RSY(SCRᵢ)`. -/
theorem nest_hOut {n : Nat} (N : NestedCoupling n) (i : Fin n) :
    AlwaysOutputs ((nestRecipe N).VSCR.Z i) :=
  rsy_alwaysOutputs (N.sub i) (N.hOut i)

/-- The readout of an outer component is the readout of its own resultant. -/
theorem nest_outAt {n : Nat} (N : NestedCoupling n) (x : rsy_SZ (nestRecipe N))
    (op : Σ i, (nestRecipe N).VSCR.OutPort i) :
    rsyOutAt (nestRecipe N) (nest_hOut N) x op =
      rsyOutAt (N.sub op.1) (N.hOut op.1) (x op.1) op.2.val := by
  dsimp [rsyOutAt, csyOut]
  rw [Trajectory.choose_alwaysOutputs ((nestRecipe N).VSCR.Z op.1) (nest_hOut N op.1) (x op.1)
    (o := fun q : UnconnOutPort (N.sub op.1) => rsyOutAt (N.sub op.1) (N.hOut op.1) (x op.1) q.val)
    rfl]
  rfl

/-! ## The flattened recipe -/

/-- Component indices of the flattened recipe, in dependent-pair form. -/
abbrev FlatIdx {n : Nat} (N : NestedComponents n) : Type := Σ i : Fin n, Fin (N.m i)

/-- `Fin (∑ i, mᵢ) ≃ Σ i, Fin mᵢ`: the flattened component indexing. -/
def flatIdxEquiv {n : Nat} (N : NestedComponents n) : Fin (∑ i, N.m i) ≃ FlatIdx N :=
  finSigmaFinEquiv.symm

/-- [textbook/exercise4.86/definition/flat_vector] `VSCR$ = (Z₁₁, …, Z₁m₁, …, Zₙ₁, …, Zₙmₙ)`. -/
def flatVector {n : Nat} (N : NestedComponents n) : PortSystemVector (∑ i, N.m i) where
  SZ := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.SZ (flatIdxEquiv N k).2
  Port := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.Port (flatIdxEquiv N k).2
  PortVal := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.PortVal (flatIdxEquiv N k).2
  OutPort := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.OutPort (flatIdxEquiv N k).2
  OutPortVal := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.OutPortVal (flatIdxEquiv N k).2
  Z := fun k => (N.sub (flatIdxEquiv N k).1).VSCR.Z (flatIdxEquiv N k).2
  distinct := fun k l hkl =>
    N.distinctInner (flatIdxEquiv N k) (flatIdxEquiv N l)
      fun h => hkl ((flatIdxEquiv N).injective h)

/-- Tagged output ports of `VSCR$`, written as `(outer index, inner index, port)`. -/
abbrev FlatOutPort {n : Nat} (N : NestedComponents n) : Type :=
  Σ i : Fin n, Σ j : Fin (N.m i), (N.sub i).VSCR.OutPort j

/-- Tagged input ports of `VSCR$`, written as `(outer index, inner index, port)`. -/
abbrev FlatInPort {n : Nat} (N : NestedComponents n) : Type :=
  Σ i : Fin n, Σ j : Fin (N.m i), (N.sub i).VSCR.Port j

/-- Reading a tagged output port of `VSCR$` as a port of one of the inner recipes. -/
def flatOutTag {n : Nat} (N : NestedComponents n) :
    (Σ k, (flatVector N).OutPort k) ≃ FlatOutPort N :=
  (Equiv.sigmaCongrLeft (β := fun x : FlatIdx N => (N.sub x.1).VSCR.OutPort x.2)
    (flatIdxEquiv N)).trans
      (Equiv.sigmaAssoc fun (i : Fin n) (j : Fin (N.m i)) => (N.sub i).VSCR.OutPort j)

/-- Reading a tagged input port of `VSCR$` as a port of one of the inner recipes. -/
def flatInTag {n : Nat} (N : NestedComponents n) :
    (Σ k, (flatVector N).Port k) ≃ FlatInPort N :=
  (Equiv.sigmaCongrLeft (β := fun x : FlatIdx N => (N.sub x.1).VSCR.Port x.2)
    (flatIdxEquiv N)).trans
      (Equiv.sigmaAssoc fun (i : Fin n) (j : Fin (N.m i)) => (N.sub i).VSCR.Port j)

/--
  [textbook/exercise4.86/definition/flat_connectivity]
  `CSCR$ = {(OP@(SCRᵢ, Zᵢ)(OhZᵢ), IP@(SCRk, Zk)(IjZk)) : (OhZᵢ, IjZk) ∈ CSCR} ∪ {CSCRᵢ}`: all the
  internal connections of the inner recipes, together with the external connections of the outer
  recipe read on the components that carry the ports.
-/
def flatPairs {n : Nat} (N : NestedCoupling n) :
    Set (FlatOutPort N.toNestedComponents × FlatInPort N.toNestedComponents) :=
  { p | (∃ (i : Fin n) (op : Σ j, (N.sub i).VSCR.OutPort j) (ip : Σ j, (N.sub i).VSCR.Port j),
          (op, ip) ∈ (N.sub i).CSCR ∧ p = (⟨i, op⟩, ⟨i, ip⟩)) ∨
        (∃ (oo : Σ i, UnconnOutPort (N.sub i)) (ii : Σ i, UnconnInPort (N.sub i)),
          (oo, ii) ∈ N.CSCR ∧ p = (⟨oo.1, oo.2.val⟩, ⟨ii.1, ii.2.val⟩)) }

/-- Internal connections of `SCRᵢ` are connections of `SCR$`. -/
theorem flatPairs_internal {n : Nat} (N : NestedCoupling n) (i : Fin n)
    (op : Σ j, (N.sub i).VSCR.OutPort j) (ip : Σ j, (N.sub i).VSCR.Port j)
    (h : (op, ip) ∈ (N.sub i).CSCR) :
    ((⟨i, op⟩ : FlatOutPort _), (⟨i, ip⟩ : FlatInPort _)) ∈ flatPairs N :=
  Or.inl ⟨i, op, ip, h, rfl⟩

/-- External connections of `SCR` are connections of `SCR$`. -/
theorem flatPairs_external {n : Nat} (N : NestedCoupling n)
    (oo : Σ i, UnconnOutPort (N.sub i)) (ii : Σ i, UnconnInPort (N.sub i))
    (h : (oo, ii) ∈ N.CSCR) :
    ((⟨oo.1, oo.2.val⟩ : FlatOutPort _), (⟨ii.1, ii.2.val⟩ : FlatInPort _)) ∈ flatPairs N :=
  Or.inr ⟨oo, ii, h, rfl⟩

/-- An internally connected output port is a connected output port of its inner recipe. -/
theorem mem_coscr_of_flat_internal {n : Nat} {N : NestedCoupling n} {i : Fin n}
    {op : Σ j, (N.sub i).VSCR.OutPort j} {ip : Σ j, (N.sub i).VSCR.Port j}
    (h : (op, ip) ∈ (N.sub i).CSCR) : op ∈ COSCR (N.sub i) := ⟨ip, h⟩

/-- An internally connected input port is a connected input port of its inner recipe. -/
theorem mem_ciscr_of_flat_internal {n : Nat} {N : NestedCoupling n} {i : Fin n}
    {op : Σ j, (N.sub i).VSCR.OutPort j} {ip : Σ j, (N.sub i).VSCR.Port j}
    (h : (op, ip) ∈ (N.sub i).CSCR) : ip ∈ CISCR (N.sub i) := ⟨op, h⟩

/-- `CSCR$` transported to the `Fin (∑ i, mᵢ)` indexing of `VSCR$`. -/
def flatCSCR {n : Nat} (N : NestedCoupling n) :
    Set ((Σ k, (flatVector N.toNestedComponents).OutPort k) ×
      (Σ k, (flatVector N.toNestedComponents).Port k)) :=
  { p | (flatOutTag _ p.1, flatInTag _ p.2) ∈ flatPairs N }

/-! ## `CSCR$` is a connectivity -/

theorem flat_outPortVal_eq {n : Nat} (N : NestedComponents n)
    (P : Σ k, (flatVector N).OutPort k) (i : Fin n) (opi : Σ j, (N.sub i).VSCR.OutPort j)
    (h : flatOutTag N P = ⟨i, opi⟩) :
    (flatVector N).OutPortVal P.1 P.2 = (N.sub i).VSCR.OutPortVal opi.1 opi.2 := by
  have hrfl : (flatVector N).OutPortVal P.1 P.2 =
      (N.sub (flatOutTag N P).1).VSCR.OutPortVal (flatOutTag N P).2.1 (flatOutTag N P).2.2 := rfl
  rw [hrfl, h]

theorem flat_portVal_eq {n : Nat} (N : NestedComponents n)
    (P : Σ k, (flatVector N).Port k) (i : Fin n) (ipi : Σ j, (N.sub i).VSCR.Port j)
    (h : flatInTag N P = ⟨i, ipi⟩) :
    (flatVector N).PortVal P.1 P.2 = (N.sub i).VSCR.PortVal ipi.1 ipi.2 := by
  have hrfl : (flatVector N).PortVal P.1 P.2 =
      (N.sub (flatInTag N P).1).VSCR.PortVal (flatInTag N P).2.1 (flatInTag N P).2.2 := rfl
  rw [hrfl, h]

theorem flatPairs_oneToOne {n : Nat} (N : NestedCoupling n) : IsOneToOneRelation (flatPairs N) := by
  constructor
  · rintro X Y1 Y2 (⟨i, op, ip, hmem, hp⟩ | ⟨oo, ii, hmem, hp⟩)
      (⟨i', op', ip', hmem', hp'⟩ | ⟨oo', ii', hmem', hp'⟩) <;>
      obtain ⟨hX, hY⟩ := Prod.mk.injEq .. ▸ hp <;> obtain ⟨hX', hY'⟩ := Prod.mk.injEq .. ▸ hp' <;>
      subst hY <;> subst hY'
    · obtain ⟨rfl, hop⟩ := Sigma.mk.injEq .. ▸ (hX.symm.trans hX')
      obtain rfl : op = op' := eq_of_heq hop
      have : ip = ip' := (N.sub i).connectivity.1.1 op ip ip' hmem hmem'
      rw [this]
    · obtain ⟨rfl, hop⟩ := Sigma.mk.injEq .. ▸ (hX.symm.trans hX')
      obtain rfl : op = oo'.2.val := eq_of_heq hop
      exact absurd (mem_coscr_of_flat_internal hmem) oo'.2.property
    · obtain ⟨rfl, hop⟩ := Sigma.mk.injEq .. ▸ (hX.symm.trans hX')
      obtain rfl : oo.2.val = op' := eq_of_heq hop
      exact absurd (mem_coscr_of_flat_internal hmem') oo.2.property
    · obtain ⟨hi, hop⟩ := Sigma.mk.injEq .. ▸ (hX.symm.trans hX')
      obtain ⟨i1, o1⟩ := oo
      obtain ⟨i2, o2⟩ := oo'
      cases hi
      obtain rfl : o1 = o2 := Subtype.ext (eq_of_heq hop)
      have : ii = ii' := N.connectivity.1.1 _ ii ii' hmem hmem'
      rw [this]
  · rintro X1 X2 Y (⟨i, op, ip, hmem, hp⟩ | ⟨oo, ii, hmem, hp⟩)
      (⟨i', op', ip', hmem', hp'⟩ | ⟨oo', ii', hmem', hp'⟩) <;>
      obtain ⟨hX, hY⟩ := Prod.mk.injEq .. ▸ hp <;> obtain ⟨hX', hY'⟩ := Prod.mk.injEq .. ▸ hp' <;>
      subst hX <;> subst hX'
    · obtain ⟨rfl, hip⟩ := Sigma.mk.injEq .. ▸ (hY.symm.trans hY')
      obtain rfl : ip = ip' := eq_of_heq hip
      have : op = op' := (N.sub i).connectivity.1.2 op op' ip hmem hmem'
      rw [this]
    · obtain ⟨rfl, hip⟩ := Sigma.mk.injEq .. ▸ (hY.symm.trans hY')
      obtain rfl : ip = ii'.2.val := eq_of_heq hip
      exact absurd (mem_ciscr_of_flat_internal hmem) ii'.2.property
    · obtain ⟨rfl, hip⟩ := Sigma.mk.injEq .. ▸ (hY.symm.trans hY')
      obtain rfl : ii.2.val = ip' := eq_of_heq hip
      exact absurd (mem_ciscr_of_flat_internal hmem') ii.2.property
    · obtain ⟨hi, hip⟩ := Sigma.mk.injEq .. ▸ (hY.symm.trans hY')
      obtain ⟨i1, p1⟩ := ii
      obtain ⟨i2, p2⟩ := ii'
      cases hi
      obtain rfl : p1 = p2 := Subtype.ext (eq_of_heq hip)
      have : oo = oo' := N.connectivity.1.2 oo oo' _ hmem hmem'
      rw [this]

/-- An unconnected output port of the outer recipe is unconnected in `SCR$`. -/
theorem flat_uoscr_of_nest {n : Nat} (N : NestedCoupling n)
    (oo : Σ i, UnconnOutPort (N.sub i)) (h : oo ∈ UOSCR (nestRecipe N)) :
    ¬ ∃ Y, ((⟨oo.1, oo.2.val⟩ : FlatOutPort _), Y) ∈ flatPairs N := by
  rintro ⟨Y, hY | hY⟩
  · obtain ⟨i, op, ip, hmem, hp⟩ := hY
    obtain ⟨hX, _⟩ := Prod.mk.injEq .. ▸ hp
    obtain ⟨rfl, hop⟩ := Sigma.mk.injEq .. ▸ hX
    obtain rfl : oo.2.val = op := eq_of_heq hop
    exact absurd (mem_coscr_of_flat_internal hmem) oo.2.property
  · obtain ⟨oo', ii', hmem, hp⟩ := hY
    obtain ⟨hX, _⟩ := Prod.mk.injEq .. ▸ hp
    obtain ⟨hi, hop⟩ := Sigma.mk.injEq .. ▸ hX
    obtain ⟨i1, o1⟩ := oo
    obtain ⟨i2, o2⟩ := oo'
    cases hi
    obtain rfl : o1 = o2 := Subtype.ext (eq_of_heq hop)
    exact h ⟨ii', hmem⟩

/-- An unconnected input port of the outer recipe is unconnected in `SCR$`. -/
theorem flat_uiscr_of_nest {n : Nat} (N : NestedCoupling n)
    (ii : Σ i, UnconnInPort (N.sub i)) (h : ii ∈ UISCR (nestRecipe N)) :
    ¬ ∃ X, (X, (⟨ii.1, ii.2.val⟩ : FlatInPort _)) ∈ flatPairs N := by
  rintro ⟨X, hX | hX⟩
  · obtain ⟨i, op, ip, hmem, hp⟩ := hX
    obtain ⟨_, hY⟩ := Prod.mk.injEq .. ▸ hp
    obtain ⟨rfl, hip⟩ := Sigma.mk.injEq .. ▸ hY
    obtain rfl : ii.2.val = ip := eq_of_heq hip
    exact absurd (mem_ciscr_of_flat_internal hmem) ii.2.property
  · obtain ⟨oo', ii', hmem, hp⟩ := hX
    obtain ⟨_, hY⟩ := Prod.mk.injEq .. ▸ hp
    obtain ⟨hi, hip⟩ := Sigma.mk.injEq .. ▸ hY
    obtain ⟨i1, p1⟩ := ii
    obtain ⟨i2, p2⟩ := ii'
    cases hi
    obtain rfl : p1 = p2 := Subtype.ext (eq_of_heq hip)
    exact h ⟨oo', hmem⟩

theorem flat_connectivity {n : Nat} (N : NestedCoupling n) :
    IsSystemConnectivity (flatVector N.toNestedComponents) (flatCSCR N) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro X Y1 Y2 h1 h2
    exact (flatInTag _).injective ((flatPairs_oneToOne N).1 _ _ _ h1 h2)
  · intro X1 X2 Y h1 h2
    exact (flatOutTag _).injective ((flatPairs_oneToOne N).2 _ _ _ h1 h2)
  · intro hall
    obtain ⟨oo, hoo⟩ := scr_has_unconnected_output_port (nestRecipe N)
    have hmem : (flatOutTag _).symm ⟨oo.1, oo.2.val⟩ ∈ { X | ∃ Y, (X, Y) ∈ flatCSCR N } := by
      rw [hall]; trivial
    obtain ⟨Y, hY⟩ := hmem
    refine flat_uoscr_of_nest N oo hoo ⟨flatInTag _ Y, ?_⟩
    simpa [flatCSCR, Equiv.apply_symm_apply] using hY
  · intro hall
    obtain ⟨ii, hii⟩ := scr_has_unconnected_input_port (nestRecipe N)
    have hmem : (flatInTag _).symm ⟨ii.1, ii.2.val⟩ ∈ { Y | ∃ X, (X, Y) ∈ flatCSCR N } := by
      rw [hall]; trivial
    obtain ⟨X, hX⟩ := hmem
    refine flat_uiscr_of_nest N ii hii ⟨flatOutTag _ X, ?_⟩
    simpa [flatCSCR, Equiv.apply_symm_apply] using hX
  · rintro P1 P2 (⟨i, op, ip, hmem, hp⟩ | ⟨oo, ii, hmem, hp⟩)
    · obtain ⟨hX, hY⟩ := Prod.mk.injEq .. ▸ hp
      rw [flat_outPortVal_eq _ P1 i op hX, flat_portVal_eq _ P2 i ip hY]
      exact (N.sub i).connectivity.2.2.2 op ip hmem
    · obtain ⟨hX, hY⟩ := Prod.mk.injEq .. ▸ hp
      rw [flat_outPortVal_eq _ P1 oo.1 oo.2.val hX, flat_portVal_eq _ P2 ii.1 ii.2.val hY]
      exact N.connectivity.2.2.2 oo ii hmem

/-- [textbook/exercise4.86/definition/flat_recipe] `SCR$ = (VSCR$, CSCR$)`. -/
noncomputable def flatRecipe {n : Nat} (N : NestedCoupling n) :
    SystemCouplingRecipe (∑ i, N.m i) where
  VSCR := flatVector N.toNestedComponents
  CSCR := flatCSCR N
  connectivity := flat_connectivity N

/-! ## External ports of `SCR$` are the external ports of `SCR` -/

/--
  A flat input port is connected exactly when it is connected inside its own inner recipe, or it
  is an external port of that inner resultant which the outer recipe connects.
-/
theorem flat_mem_ciscr_iff {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).Port k) :
    P ∈ CISCR (flatRecipe N) ↔
      (flatInTag _ P).2 ∈ CISCR (N.sub (flatInTag _ P).1) ∨
        ∃ hU : (flatInTag _ P).2 ∈ UISCR (N.sub (flatInTag _ P).1),
          (⟨(flatInTag _ P).1, ⟨(flatInTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈
            CISCR (nestRecipe N) := by
  constructor
  · rintro ⟨X, hX | hX⟩
    · obtain ⟨i, op, ip, hmem, hp⟩ := hX
      obtain ⟨_, hY⟩ := Prod.mk.injEq .. ▸ hp
      rw [hY]
      exact Or.inl ⟨op, hmem⟩
    · obtain ⟨oo, ii, hmem, hp⟩ := hX
      obtain ⟨_, hY⟩ := Prod.mk.injEq .. ▸ hp
      rw [hY]
      exact Or.inr ⟨ii.2.property, ⟨oo, hmem⟩⟩
  · rintro (⟨op, hmem⟩ | ⟨hU, oo, hmem⟩)
    · refine ⟨(flatOutTag _).symm ⟨(flatInTag _ P).1, op⟩, ?_⟩
      show (flatOutTag _ ((flatOutTag _).symm ⟨(flatInTag _ P).1, op⟩), flatInTag _ P) ∈ flatPairs N
      rw [Equiv.apply_symm_apply]
      exact flatPairs_internal N (flatInTag _ P).1 op (flatInTag _ P).2 hmem
    · refine ⟨(flatOutTag _).symm ⟨oo.1, oo.2.val⟩, ?_⟩
      show (flatOutTag _ ((flatOutTag _).symm ⟨oo.1, oo.2.val⟩), flatInTag _ P) ∈ flatPairs N
      rw [Equiv.apply_symm_apply]
      exact flatPairs_external N oo ⟨(flatInTag _ P).1, ⟨(flatInTag _ P).2, hU⟩⟩ hmem

/-- Dual of `flat_mem_ciscr_iff` for output ports. -/
theorem flat_mem_coscr_iff {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).OutPort k) :
    P ∈ COSCR (flatRecipe N) ↔
      (flatOutTag _ P).2 ∈ COSCR (N.sub (flatOutTag _ P).1) ∨
        ∃ hU : (flatOutTag _ P).2 ∈ UOSCR (N.sub (flatOutTag _ P).1),
          (⟨(flatOutTag _ P).1, ⟨(flatOutTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.OutPort i) ∈
            COSCR (nestRecipe N) := by
  constructor
  · rintro ⟨Y, hY | hY⟩
    · obtain ⟨i, op, ip, hmem, hp⟩ := hY
      obtain ⟨hX, _⟩ := Prod.mk.injEq .. ▸ hp
      rw [hX]
      exact Or.inl ⟨ip, hmem⟩
    · obtain ⟨oo, ii, hmem, hp⟩ := hY
      obtain ⟨hX, _⟩ := Prod.mk.injEq .. ▸ hp
      rw [hX]
      exact Or.inr ⟨oo.2.property, ⟨ii, hmem⟩⟩
  · rintro (⟨ip, hmem⟩ | ⟨hU, ii, hmem⟩)
    · refine ⟨(flatInTag _).symm ⟨(flatOutTag _ P).1, ip⟩, ?_⟩
      show (flatOutTag _ P, flatInTag _ ((flatInTag _).symm ⟨(flatOutTag _ P).1, ip⟩)) ∈ flatPairs N
      rw [Equiv.apply_symm_apply]
      exact flatPairs_internal N (flatOutTag _ P).1 (flatOutTag _ P).2 ip hmem
    · refine ⟨(flatInTag _).symm ⟨ii.1, ii.2.val⟩, ?_⟩
      show (flatOutTag _ P, flatInTag _ ((flatInTag _).symm ⟨ii.1, ii.2.val⟩)) ∈ flatPairs N
      rw [Equiv.apply_symm_apply]
      exact flatPairs_external N ⟨(flatOutTag _ P).1, ⟨(flatOutTag _ P).2, hU⟩⟩ ii hmem

/-- [textbook/exercise4.86/theorem/uiscr_preserved] `UISCR$` corresponds to `UISCR`. -/
theorem flat_mem_uiscr_iff {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).Port k) :
    P ∈ UISCR (flatRecipe N) ↔
      ∃ hU : (flatInTag _ P).2 ∈ UISCR (N.sub (flatInTag _ P).1),
        (⟨(flatInTag _ P).1, ⟨(flatInTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈
          UISCR (nestRecipe N) := by
  constructor
  · intro hU
    have h := (flat_mem_ciscr_iff N P).not.mpr
    have hC : ¬ ((flatInTag _ P).2 ∈ CISCR (N.sub (flatInTag _ P).1) ∨ _) := fun hc =>
      hU ((flat_mem_ciscr_iff N P).mpr hc)
    refine ⟨fun hc => hC (Or.inl hc), fun hc => hC (Or.inr ⟨_, hc⟩)⟩
  · rintro ⟨hU, hOuter⟩ hC
    rcases (flat_mem_ciscr_iff N P).mp hC with hc | ⟨_, hc⟩
    · exact hU hc
    · exact hOuter hc

/-- [textbook/exercise4.86/theorem/uoscr_preserved] `UOSCR$` corresponds to `UOSCR`. -/
theorem flat_mem_uoscr_iff {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).OutPort k) :
    P ∈ UOSCR (flatRecipe N) ↔
      ∃ hU : (flatOutTag _ P).2 ∈ UOSCR (N.sub (flatOutTag _ P).1),
        (⟨(flatOutTag _ P).1, ⟨(flatOutTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.OutPort i) ∈
          UOSCR (nestRecipe N) := by
  constructor
  · intro hU
    have hC : ¬ ((flatOutTag _ P).2 ∈ COSCR (N.sub (flatOutTag _ P).1) ∨ _) := fun hc =>
      hU ((flat_mem_coscr_iff N P).mpr hc)
    refine ⟨fun hc => hC (Or.inl hc), fun hc => hC (Or.inr ⟨_, hc⟩)⟩
  · rintro ⟨hU, hOuter⟩ hC
    rcases (flat_mem_coscr_iff N P).mp hC with hc | ⟨_, hc⟩
    · exact hU hc
    · exact hOuter hc

/-! ## The external port correspondence -/

theorem flat_uiscr_inner {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).Port k) (h : P ∈ UISCR (flatRecipe N)) :
    (flatInTag _ P).2 ∈ UISCR (N.sub (flatInTag _ P).1) :=
  fun hc => h ((flat_mem_ciscr_iff N P).mpr (Or.inl hc))

theorem flat_uiscr_outer {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).Port k) (h : P ∈ UISCR (flatRecipe N)) :
    (⟨(flatInTag _ P).1, ⟨(flatInTag _ P).2, flat_uiscr_inner N P h⟩⟩ :
        Σ i, (nestRecipe N).VSCR.Port i) ∈ UISCR (nestRecipe N) :=
  fun hc => h ((flat_mem_ciscr_iff N P).mpr (Or.inr ⟨flat_uiscr_inner N P h, hc⟩))

theorem flat_uoscr_inner {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).OutPort k) (h : P ∈ UOSCR (flatRecipe N)) :
    (flatOutTag _ P).2 ∈ UOSCR (N.sub (flatOutTag _ P).1) :=
  fun hc => h ((flat_mem_coscr_iff N P).mpr (Or.inl hc))

theorem flat_uoscr_outer {n : Nat} (N : NestedCoupling n)
    (P : Σ k, (flatVector N.toNestedComponents).OutPort k) (h : P ∈ UOSCR (flatRecipe N)) :
    (⟨(flatOutTag _ P).1, ⟨(flatOutTag _ P).2, flat_uoscr_inner N P h⟩⟩ :
        Σ i, (nestRecipe N).VSCR.OutPort i) ∈ UOSCR (nestRecipe N) :=
  fun hc => h ((flat_mem_coscr_iff N P).mpr (Or.inr ⟨flat_uoscr_inner N P h, hc⟩))

/-- Transporting connectedness of an inner input port along an equality of tagged ports. -/
theorem mem_ciscr_congr {n : Nat} (N : NestedCoupling n)
    {A B : FlatInPort N.toNestedComponents} (h : A = B) (hc : A.2 ∈ CISCR (N.sub A.1)) :
    B.2 ∈ CISCR (N.sub B.1) := by
  subst h; exact hc

/-- Transporting connectedness of an inner output port along an equality of tagged ports. -/
theorem mem_coscr_congr {n : Nat} (N : NestedCoupling n)
    {A B : FlatOutPort N.toNestedComponents} (h : A = B) (hc : A.2 ∈ COSCR (N.sub A.1)) :
    B.2 ∈ COSCR (N.sub B.1) := by
  subst h; exact hc

/-- Rebuilding an external input port from equal underlying tagged ports. -/
theorem unconnIn_mk_eq {n : Nat} (N : NestedCoupling n)
    {A B : FlatInPort N.toNestedComponents} (h : A = B)
    (hA : A.2 ∈ UISCR (N.sub A.1)) (hB : B.2 ∈ UISCR (N.sub B.1)) :
    (⟨A.1, ⟨A.2, hA⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) = ⟨B.1, ⟨B.2, hB⟩⟩ := by
  subst h; rfl

/-- Rebuilding an external output port from equal underlying tagged ports. -/
theorem unconnOut_mk_eq {n : Nat} (N : NestedCoupling n)
    {A B : FlatOutPort N.toNestedComponents} (h : A = B)
    (hA : A.2 ∈ UOSCR (N.sub A.1)) (hB : B.2 ∈ UOSCR (N.sub B.1)) :
    (⟨A.1, ⟨A.2, hA⟩⟩ : Σ i, (nestRecipe N).VSCR.OutPort i) = ⟨B.1, ⟨B.2, hB⟩⟩ := by
  subst h; rfl

/-- An inner input port that is external for both levels is unconnected in `SCR$`. -/
theorem flat_uiscr_of {n : Nat} (N : NestedCoupling n) (i : Fin n)
    (ip : Σ j, (N.sub i).VSCR.Port j) (hU : ip ∈ UISCR (N.sub i))
    (hOuter : (⟨i, ⟨ip, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈ UISCR (nestRecipe N)) :
    (flatInTag _).symm ⟨i, ip⟩ ∈ UISCR (flatRecipe N) := by
  intro hC
  have htag : flatInTag N.toNestedComponents ((flatInTag _).symm (⟨i, ip⟩ : FlatInPort _)) =
      ⟨i, ip⟩ := Equiv.apply_symm_apply _ _
  rcases (flat_mem_ciscr_iff N _).mp hC with hc | ⟨hu', hc⟩
  · exact hU (mem_ciscr_congr N htag hc)
  · exact hOuter (unconnIn_mk_eq N htag hu' hU ▸ hc)

/-- An inner output port that is external for both levels is unconnected in `SCR$`. -/
theorem flat_uoscr_of {n : Nat} (N : NestedCoupling n) (i : Fin n)
    (op : Σ j, (N.sub i).VSCR.OutPort j) (hU : op ∈ UOSCR (N.sub i))
    (hOuter : (⟨i, ⟨op, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.OutPort i) ∈ UOSCR (nestRecipe N)) :
    (flatOutTag _).symm ⟨i, op⟩ ∈ UOSCR (flatRecipe N) := by
  intro hC
  have htag : flatOutTag N.toNestedComponents ((flatOutTag _).symm (⟨i, op⟩ : FlatOutPort _)) =
      ⟨i, op⟩ := Equiv.apply_symm_apply _ _
  rcases (flat_mem_coscr_iff N _).mp hC with hc | ⟨hu', hc⟩
  · exact hU (mem_coscr_congr N htag hc)
  · exact hOuter (unconnOut_mk_eq N htag hu' hU ▸ hc)

/-- `IZ@$ = IZ@`: external input ports of `SCR$` are the external input ports of `SCR`. -/
def flatToNestIn {n : Nat} (N : NestedCoupling n) (P : UnconnInPort (flatRecipe N)) :
    UnconnInPort (nestRecipe N) :=
  ⟨⟨(flatInTag _ P.val).1, ⟨(flatInTag _ P.val).2, flat_uiscr_inner N P.val P.property⟩⟩,
    flat_uiscr_outer N P.val P.property⟩

/-- `OZ@$ = OZ@`: external output ports of `SCR$` are the external output ports of `SCR`. -/
def flatToNestOut {n : Nat} (N : NestedCoupling n) (P : UnconnOutPort (flatRecipe N)) :
    UnconnOutPort (nestRecipe N) :=
  ⟨⟨(flatOutTag _ P.val).1, ⟨(flatOutTag _ P.val).2, flat_uoscr_inner N P.val P.property⟩⟩,
    flat_uoscr_outer N P.val P.property⟩

def nestToFlatIn {n : Nat} (N : NestedCoupling n) (Q : UnconnInPort (nestRecipe N)) :
    UnconnInPort (flatRecipe N) :=
  ⟨(flatInTag _).symm ⟨Q.val.1, Q.val.2.val⟩,
    flat_uiscr_of N Q.val.1 Q.val.2.val Q.val.2.property Q.property⟩

def nestToFlatOut {n : Nat} (N : NestedCoupling n) (Q : UnconnOutPort (nestRecipe N)) :
    UnconnOutPort (flatRecipe N) :=
  ⟨(flatOutTag _).symm ⟨Q.val.1, Q.val.2.val⟩,
    flat_uoscr_of N Q.val.1 Q.val.2.val Q.val.2.property Q.property⟩

/-- [textbook/exercise4.86/theorem/uiscr_preserved] `UISCR$ ≃ UISCR`. -/
def flatUnconnIn {n : Nat} (N : NestedCoupling n) :
    UnconnInPort (flatRecipe N) ≃ UnconnInPort (nestRecipe N) where
  toFun := flatToNestIn N
  invFun := nestToFlatIn N
  left_inv := by
    intro P
    apply Subtype.ext
    show (flatInTag _).symm ⟨(flatInTag _ P.val).1, (flatInTag _ P.val).2⟩ = P.val
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro Q
    apply Subtype.ext
    exact unconnIn_mk_eq N (Equiv.apply_symm_apply _ _) _ Q.val.2.property

/-- [textbook/exercise4.86/theorem/uoscr_preserved] `UOSCR$ ≃ UOSCR`. -/
def flatUnconnOut {n : Nat} (N : NestedCoupling n) :
    UnconnOutPort (flatRecipe N) ≃ UnconnOutPort (nestRecipe N) where
  toFun := flatToNestOut N
  invFun := nestToFlatOut N
  left_inv := by
    intro P
    apply Subtype.ext
    show (flatOutTag _).symm ⟨(flatOutTag _ P.val).1, (flatOutTag _ P.val).2⟩ = P.val
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro Q
    apply Subtype.ext
    exact unconnOut_mk_eq N (Equiv.apply_symm_apply _ _) _ Q.val.2.property

/-! ## The isomorphism -/

/-- Components of `VSCR$` are components of the inner recipes, so they have total readouts. -/
theorem flat_hOut {n : Nat} (N : NestedCoupling n) (k : Fin (∑ i, N.m i)) :
    AlwaysOutputs ((flatRecipe N).VSCR.Z k) :=
  N.hOut (flatIdxEquiv _ k).1 (flatIdxEquiv _ k).2

/--
  [textbook/exercise4.86/component/HS]
  `HS` is the currying `(x₁₁, …, xₙmₙ) ↦ ((x₁₁, …, x₁m₁), …, (xₙ₁, …, xₙmₙ))`, read here in the
  direction `SZ@ → SZ@$`.
-/
def flatHS {n : Nat} (N : NestedCoupling n) (x : rsy_SZ (nestRecipe N)) : rsy_SZ (flatRecipe N) :=
  fun k => x (flatIdxEquiv _ k).1 (flatIdxEquiv _ k).2

/-- `HS` as the composite of the reindexing and the currying equivalences. -/
def flatHSEquiv {n : Nat} (N : NestedCoupling n) : rsy_SZ (flatRecipe N) ≃ rsy_SZ (nestRecipe N) :=
  (Equiv.piCongrLeft (fun y : FlatIdx N.toNestedComponents => (N.sub y.1).VSCR.SZ y.2)
      (flatIdxEquiv N.toNestedComponents)).trans
    (Equiv.piCurry fun (i : Fin n) (j : Fin (N.m i)) => (N.sub i).VSCR.SZ j)

theorem flatHS_eq {n : Nat} (N : NestedCoupling n) : flatHS N = (flatHSEquiv N).symm := rfl

/-- [textbook/exercise4.86/component/HI] `HI = ID(IZ@$)`, read through `UISCR$ ≃ UISCR`. -/
def flatHI {n : Nat} (N : NestedCoupling n) (g : rsy_IZ (nestRecipe N)) : rsy_IZ (flatRecipe N) :=
  fun P => g (flatUnconnIn N P)

/-- [textbook/exercise4.86/component/HO] `HO = ID(OZ@$)`, read through `UOSCR$ ≃ UOSCR`. -/
def flatHO {n : Nat} (N : NestedCoupling n) (g : rsy_OZ (nestRecipe N)) : rsy_OZ (flatRecipe N) :=
  fun P => g (flatUnconnOut N P)

theorem flatHI_eq {n : Nat} (N : NestedCoupling n) :
    flatHI N =
      (Equiv.piCongrLeft
        (fun Q : UnconnInPort (nestRecipe N) => (nestRecipe N).VSCR.PortVal Q.val.1 Q.val.2)
        (flatUnconnIn N)).symm := rfl

theorem flatHO_eq {n : Nat} (N : NestedCoupling n) :
    flatHO N =
      (Equiv.piCongrLeft
        (fun Q : UnconnOutPort (nestRecipe N) => (nestRecipe N).VSCR.OutPortVal Q.val.1 Q.val.2)
        (flatUnconnOut N)).symm := rfl

/-- A readout of `VSCR$` is a readout of the corresponding inner component. -/
theorem flat_outAt {n : Nat} (N : NestedCoupling n) (x : rsy_SZ (nestRecipe N))
    (P : Σ k, (flatVector N.toNestedComponents).OutPort k) :
    rsyOutAt (flatRecipe N) (flat_hOut N) (flatHS N x) P =
      rsyOutAt (N.sub (flatOutTag _ P).1) (N.hOut (flatOutTag _ P).1)
        (x (flatOutTag _ P).1) (flatOutTag _ P).2 := rfl

/-- Readouts of equal tagged output ports agree after transport. -/
theorem outAt_tag_congr {n : Nat} (N : NestedCoupling n) (x : rsy_SZ (nestRecipe N))
    {A B : FlatOutPort N.toNestedComponents} (h : A = B) {T : Type}
    (hA : (N.sub A.1).VSCR.OutPortVal A.2.1 A.2.2 = T)
    (hB : (N.sub B.1).VSCR.OutPortVal B.2.1 B.2.2 = T) :
    hA ▸ rsyOutAt (N.sub A.1) (N.hOut A.1) (x A.1) A.2 =
      hB ▸ rsyOutAt (N.sub B.1) (N.hOut B.1) (x B.1) B.2 := by
  subst h
  exact eq_rec_proof_irrel _

/--
  [textbook/exercise4.86/proof/input_resolution]
  Resolving the input of a component of `VSCR$` in one step through `CSCR$` gives the same value
  as resolving it in two steps: first the external input of `Zᵢ = RSY(SCRᵢ)` through `CSCR`, then
  the input of the component inside `SCRᵢ`.
-/
theorem flat_component_input {n : Nat} (N : NestedCoupling n) (k : Fin (∑ i, N.m i))
    (extIn : rsy_IZ (nestRecipe N)) (x : rsy_SZ (nestRecipe N))
    (port : (flatRecipe N).VSCR.Port k) :
    rsy_component_input_fun (flatRecipe N) (flat_hOut N) k (flatHI N extIn) (flatHS N x) port =
      rsy_component_input_fun (N.sub (flatIdxEquiv _ k).1) (N.hOut (flatIdxEquiv _ k).1)
        (flatIdxEquiv _ k).2
        (rsy_component_input_fun (nestRecipe N) (nest_hOut N) (flatIdxEquiv _ k).1 extIn x)
        (x (flatIdxEquiv _ k).1) port := by
  classical
  set i := (flatIdxEquiv N.toNestedComponents k).1 with hi
  set j := (flatIdxEquiv N.toNestedComponents k).2 with hj
  set ip : Σ j, (N.sub i).VSCR.Port j := ⟨j, port⟩ with hip
  by_cases hInner : ip ∈ UISCR (N.sub i)
  · by_cases hOuter :
        (⟨i, ⟨ip, hInner⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈ UISCR (nestRecipe N)
    · have hUflat : (⟨k, port⟩ : Σ k, (flatRecipe N).VSCR.Port k) ∈ UISCR (flatRecipe N) :=
        (flat_mem_uiscr_iff N ⟨k, port⟩).mpr ⟨hInner, hOuter⟩
      rw [rsy_component_input_uiscr _ _ _ _ _ _ hUflat,
        rsy_component_input_uiscr (N.sub i) (N.hOut i) j _ (x i) port hInner,
        rsy_component_input_uiscr (nestRecipe N) (nest_hOut N) i extIn x _ hOuter]
      rfl
    · have hCouter : (⟨i, ⟨ip, hInner⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈
          CISCR (nestRecipe N) := by
        simpa [UISCR, Set.mem_compl_iff] using hOuter
      set OQ := connectedOutput (nestRecipe N) ⟨i, ⟨ip, hInner⟩⟩ hCouter with hOQ
      have hspecNest : (OQ, (⟨i, ⟨ip, hInner⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i)) ∈
          (nestRecipe N).CSCR := connectedOutput_spec (nestRecipe N) _ hCouter
      set X : Σ k, (flatRecipe N).VSCR.OutPort k :=
        (flatOutTag N.toNestedComponents).symm ⟨OQ.1, OQ.2.val⟩ with hX
      have hXtag : flatOutTag N.toNestedComponents X = ⟨OQ.1, OQ.2.val⟩ :=
        Equiv.apply_symm_apply _ _
      have hspecFlat : (X, (⟨k, port⟩ : Σ k, (flatRecipe N).VSCR.Port k)) ∈
          (flatRecipe N).CSCR := by
        show (flatOutTag _ X, flatInTag _ (⟨k, port⟩ : Σ k, (flatVector _).Port k)) ∈ flatPairs N
        rw [hXtag]
        exact flatPairs_external N OQ ⟨i, ⟨ip, hInner⟩⟩ hspecNest
      have htyFlat : (flatRecipe N).VSCR.OutPortVal X.1 X.2 =
          (flatRecipe N).VSCR.PortVal k port :=
        (flatRecipe N).connectivity.2.2.2 X ⟨k, port⟩ hspecFlat
      have htyNest : (nestRecipe N).VSCR.OutPortVal OQ.1 OQ.2 =
          (nestRecipe N).VSCR.PortVal i ⟨ip, hInner⟩ :=
        (nestRecipe N).connectivity.2.2.2 OQ ⟨i, ⟨ip, hInner⟩⟩ hspecNest
      rw [rsy_component_input_of_conn (flatRecipe N) (flat_hOut N) k (flatHI N extIn)
            (flatHS N x) port X hspecFlat htyFlat,
        rsy_component_input_uiscr (N.sub i) (N.hOut i) j _ (x i) port hInner,
        rsy_component_input_of_conn (nestRecipe N) (nest_hOut N) i extIn x ⟨ip, hInner⟩ OQ
          hspecNest htyNest,
        flat_outAt, nest_outAt]
      exact outAt_tag_congr N x hXtag _ _
  · have hCinner : ip ∈ CISCR (N.sub i) := by
      simpa [UISCR, Set.mem_compl_iff] using hInner
    set op := connectedOutput (N.sub i) ip hCinner with hop
    have hspecInner : (op, ip) ∈ (N.sub i).CSCR := connectedOutput_spec (N.sub i) ip hCinner
    set X : Σ k, (flatRecipe N).VSCR.OutPort k :=
      (flatOutTag N.toNestedComponents).symm ⟨i, op⟩ with hX
    have hXtag : flatOutTag N.toNestedComponents X = ⟨i, op⟩ := Equiv.apply_symm_apply _ _
    have hspecFlat : (X, (⟨k, port⟩ : Σ k, (flatRecipe N).VSCR.Port k)) ∈ (flatRecipe N).CSCR := by
      show (flatOutTag _ X, flatInTag _ (⟨k, port⟩ : Σ k, (flatVector _).Port k)) ∈ flatPairs N
      rw [hXtag]
      exact flatPairs_internal N i op ip hspecInner
    have htyFlat : (flatRecipe N).VSCR.OutPortVal X.1 X.2 = (flatRecipe N).VSCR.PortVal k port :=
      (flatRecipe N).connectivity.2.2.2 X ⟨k, port⟩ hspecFlat
    have htyInner : (N.sub i).VSCR.OutPortVal op.1 op.2 = (N.sub i).VSCR.PortVal j port :=
      (N.sub i).connectivity.2.2.2 op ip hspecInner
    rw [rsy_component_input_of_conn (flatRecipe N) (flat_hOut N) k (flatHI N extIn)
          (flatHS N x) port X hspecFlat htyFlat,
      rsy_component_input_of_conn (N.sub i) (N.hOut i) j _ (x i) port op hspecInner htyInner,
      flat_outAt]
    exact outAt_tag_congr N x hXtag _ _

/--
  [textbook/exercise4.86/proof/isomorphism_witness]
  `Z@$ = ISY(Z@, HS, HI, HO)` with `HS` the currying of the component states and `HI`, `HO` the
  identity on the external ports.
-/
noncomputable def flatIsomorphismWitness {n : Nat} (N : NestedCoupling n) :
    IsomorphismWitness (rsy (flatRecipe N) (flat_hOut N)) (rsy (nestRecipe N) (nest_hOut N)) where
  HS := flatHS N
  HI := flatHI N
  HO := flatHO N
  HS_surjective := by rw [flatHS_eq]; exact (flatHSEquiv N).symm.surjective
  HI_surjective := by
    rw [flatHI_eq]; exact (Equiv.piCongrLeft _ (flatUnconnIn N)).symm.surjective
  HO_surjective := by
    rw [flatHO_eq]; exact (Equiv.piCongrLeft _ (flatUnconnOut N)).symm.surjective
  HS_injective := by rw [flatHS_eq]; exact (flatHSEquiv N).symm.injective
  HI_injective := by
    rw [flatHI_eq]; exact (Equiv.piCongrLeft _ (flatUnconnIn N)).symm.injective
  HO_injective := by
    rw [flatHO_eq]; exact (Equiv.piCongrLeft _ (flatUnconnOut N)).symm.injective
  preserves_transition := by
    intro x oi
    funext k
    cases oi with
    | none => rfl
    | some e =>
        have h : rsy_component_input_fun (flatRecipe N) (flat_hOut N) k (flatHI N e)
              (flatHS N x) =
            rsy_component_input_fun (N.sub (flatIdxEquiv _ k).1) (N.hOut (flatIdxEquiv _ k).1)
              (flatIdxEquiv _ k).2
              (rsy_component_input_fun (nestRecipe N) (nest_hOut N) (flatIdxEquiv _ k).1 e x)
              (x (flatIdxEquiv _ k).1) :=
          funext fun port => flat_component_input N k e x port
        exact congrArg
          (fun f => ((flatRecipe N).VSCR.Z k).NZ (flatHS N x k) (some f)) h.symm
  preserves_readout := by
    intro x
    refine congrArg some (funext fun P => ?_)
    show rsyOutAt (nestRecipe N) (nest_hOut N) x (flatUnconnOut N P).val = _
    rw [nest_outAt]
    exact (flat_outAt N x P.val).symm

/--
  [textbook/exercise4.86/theorem/nested_coupling_isomorphic]
  Exercise 4.86: coupling the components of the components yields a resultant isomorphic to the
  original. The external ports are unchanged (`UISCR$` and `UOSCR$` correspond to `UISCR` and
  `UOSCR`), and `Z@$ = ISY(Z@, HS, HI, HO)` where `HS` regroups the flat state vector
  `(x₁₁, …, xₙmₙ)` into `((x₁₁, …, x₁m₁), …, (xₙ₁, …, xₙmₙ))` and `HI`, `HO` are the identity on
  the external ports. Since `ISY` is symmetric (Exercise 4.82), this is the textbook statement
  `Z@ = ISY(Z@$, HS, HI, HO)`.
-/
theorem ex4_86_nested_coupling_isomorphic {n : Nat} (N : NestedCoupling n) :
    (∀ P, P ∈ UISCR (flatRecipe N) ↔
        ∃ hU : (flatInTag _ P).2 ∈ UISCR (N.sub (flatInTag _ P).1),
          (⟨(flatInTag _ P).1, ⟨(flatInTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.Port i) ∈
            UISCR (nestRecipe N)) ∧
      (∀ P, P ∈ UOSCR (flatRecipe N) ↔
        ∃ hU : (flatOutTag _ P).2 ∈ UOSCR (N.sub (flatOutTag _ P).1),
          (⟨(flatOutTag _ P).1, ⟨(flatOutTag _ P).2, hU⟩⟩ : Σ i, (nestRecipe N).VSCR.OutPort i) ∈
            UOSCR (nestRecipe N)) ∧
      IsIsomorphicTo (rsy (flatRecipe N) (flat_hOut N)) (rsy (nestRecipe N) (nest_hOut N)) ∧
      IsIsomorphicTo (rsy (nestRecipe N) (nest_hOut N)) (rsy (flatRecipe N) (flat_hOut N)) :=
  ⟨flat_mem_uiscr_iff N, flat_mem_uoscr_iff N, ⟨flatIsomorphismWitness N⟩,
    isIsomorphicTo_symm ⟨flatIsomorphismWitness N⟩⟩

end Homomorphism
