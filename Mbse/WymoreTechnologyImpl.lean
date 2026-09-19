import Mbse.WymoreTechnology
import Mbse.WymoreImplementation
import Mbse.WymoreRequirements
import Mbse.WymoreSystemModes
import Mbse.Isomorphism
import Mbse.Homomorphism

/-!
# Wymore Chapter 7: implementation in a technology

Defs 7.45–7.66, Thms 7.54 / 7.60, Cor 7.56, and ¶7.55 TYRx2.

**Encoding.** `SGTYR(S)` / `TYRx2` are iso-classes of finite-port state-readout
generators on `S` / `Bool` (book Def 7.52 / ¶7.55). Multi-component recipes use
index cells (`sgtyrIndexCell`) with pairwise `¬ HEq` so conjunctive `S^n` /
TYRx2 SCRs are buildable; Thm 7.54/7.60/`IsImplementableIn finSystem` follow.
-/

namespace WymoreTechnology

open Classical
open Homomorphism
open WymoreImplementation
open WymoreRequirements
open WymoreSystemModes
open Mbse.Wymore

/-! ## Definition 7.45 / 7.48 -/

/--
  [textbook/definition7.45/definition/implementable_in]
-/
def IsImplementableIn {SZ1 IZ1 OZ1 : Type}
    (TYR : Technology) (Z1 : DiscreteSystem SZ1 IZ1 OZ1) : Prop :=
  ∃ (SZ2 IZ2 OZ2 : Type) (Z2 : DiscreteSystem SZ2 IZ2 OZ2),
    IsBuildable TYR Z2 ∧ Nonempty (Implements Z1 Z2)

/--
  [textbook/definition7.48/definition/imptysy]
-/
structure IMPTYSYParam where
  TYR : Technology
  n : Nat
  SCR : SystemCouplingRecipe n
  hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)
  SZ1 : Type
  IZ1 : Type
  OZ1 : Type
  SZ2 : Type
  IZ2 : Type
  OZ2 : Type
  Z1 : DiscreteSystem SZ1 IZ1 OZ1
  Z2 : DiscreteSystem SZ2 IZ2 OZ2
  buildable : IsBuildableWith TYR SCR hOut Z2
  impl : Implements Z1 Z2

def IMPTYSY (p : IMPTYSYParam) : DiscreteSystem p.SZ1 p.IZ1 p.OZ1 :=
  p.Z1

/-! ## Definition 7.52 — SGTYR(S) as iso-class -/

def sgtyrGenerator (S : Type) [Nonempty S] :
    DiscreteSystem S (Unit → S) (Unit → S) :=
  DiscreteSystem.ofTotal
    (fun _s i => i ())
    (fun s _ => s)
    ‹Nonempty S›

theorem sgtyrGenerator_alwaysOutputs (S : Type) [Nonempty S] :
    AlwaysOutputs (sgtyrGenerator S) :=
  fun s => ⟨fun _ => s, rfl⟩

def sgtyrFinGenerator (S : Type) [Nonempty S] (k : Nat) (hk : 0 < k) :
    DiscreteSystem S (Fin k → S) (Fin k → S) :=
  DiscreteSystem.ofTotal
    (fun _s inp => inp ⟨0, hk⟩)
    (fun s _ => s)
    ‹Nonempty S›

theorem sgtyrFinGenerator_alwaysOutputs (S : Type) [Nonempty S] (k : Nat) (hk : 0 < k) :
    AlwaysOutputs (sgtyrFinGenerator S k hk) :=
  fun s => ⟨fun _ => s, rfl⟩

noncomputable def unitToFin1Arrow (S : Type) : (Unit → S) ≃ (Fin 1 → S) where
  toFun f _ := f ()
  invFun g _ := g ⟨0, by decide⟩
  left_inv _ := rfl
  right_inv g := funext fun j => by
    have : j = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst this; rfl

noncomputable def sgtyrGenerator_iso_fin1 (S : Type) [Nonempty S] :
    IsomorphismWitness (sgtyrGenerator S) (sgtyrFinGenerator S 1 (Nat.succ_pos 0)) where
  toHomomorphicImageWitness :=
    { HS := id
      HI := (unitToFin1Arrow S).symm
      HO := (unitToFin1Arrow S).symm
      HS_surjective := Function.surjective_id
      HI_surjective := (unitToFin1Arrow S).symm.surjective
      HO_surjective := (unitToFin1Arrow S).symm.surjective
      preserves_transition := by
        intro x oi
        cases oi <;> rfl
      preserves_readout := by
        intro x
        rfl }
  HS_injective := Function.injective_id
  HI_injective := (unitToFin1Arrow S).symm.injective
  HO_injective := (unitToFin1Arrow S).symm.injective

/--
  [textbook/definition7.52/definition/is_sgtyr_member]
  Book: `SZ ≃ S`, port alphabets ≃ `S`, state readout (`RiZ = ID`).
  Lean: isomorphic to a finite-port state-readout generator on `S`.
-/
def IsSGTYRMember (S : Type) [Nonempty S] (a : AnyDiscreteSystem) : Prop :=
  ∃ (k : Nat) (hk : 0 < k), Nonempty (IsomorphismWitness a.Z (sgtyrFinGenerator S k hk))

theorem sgtyrGenerator_is_member (S : Type) [Nonempty S] :
    IsSGTYRMember S (AnyDiscreteSystem.of (sgtyrGenerator S)) :=
  ⟨1, Nat.succ_pos 0, ⟨sgtyrGenerator_iso_fin1 S⟩⟩

theorem sgtyrFinGenerator_is_member (S : Type) [Nonempty S] (k : Nat) (hk : 0 < k) :
    IsSGTYRMember S (AnyDiscreteSystem.of (sgtyrFinGenerator S k hk)) :=
  ⟨k, hk, ⟨IsomorphismWitness.refl _⟩⟩

/--
  [textbook/definition7.52/definition/sgtyr]
-/
def SGTYR (S : Type) [Nonempty S] : Technology :=
  Technology.mk {a | IsSGTYRMember S a} ⟨_, sgtyrGenerator_is_member S⟩

theorem sgtyr_mem (S : Type) [Nonempty S] :
    memTechnology (SGTYR S) (sgtyrGenerator S) :=
  memTechnology_of (SGTYR S) _ (sgtyrGenerator_is_member S)

theorem sgtyrFin_mem (S : Type) [Nonempty S] (k : Nat) (hk : 0 < k) :
    memTechnology (SGTYR S) (sgtyrFinGenerator S k hk) :=
  memTechnology_of (SGTYR S) _ (sgtyrFinGenerator_is_member S k hk)

noncomputable def sgtyrSingularSCR (S : Type) [Nonempty S] : SystemCouplingRecipe 1 :=
  singularSCR
    (portVectorOfSystem (fun _ : Unit => S) (fun _ : Unit => S) (sgtyrGenerator S))
    ⟨⟨0, ()⟩⟩ ⟨⟨0, ()⟩⟩

theorem sgtyrSingular_hOut (S : Type) [Nonempty S] :
    ∀ k, AlwaysOutputs ((sgtyrSingularSCR S).VSCR.Z k) :=
  fun _ => sgtyrGenerator_alwaysOutputs S

theorem sgtyrGenerator_buildable (S : Type) [Nonempty S] :
    IsBuildableWith (SGTYR S)
      (sgtyrSingularSCR S) (sgtyrSingular_hOut S)
      (rsy (sgtyrSingularSCR S) (sgtyrSingular_hOut S)) := by
  refine ⟨fun i => ?_, IsResultantOf.of_rsy _ _⟩
  have hi : i = (0 : Fin 1) := Trajectory.fin_one_eq i 0
  subst hi
  exact sgtyr_mem S

/-! ## Paragraph 7.55 — TYRx2 -/

def binGenerator : DiscreteSystem Bool (Unit → Bool) (Unit → Bool) :=
  sgtyrGenerator Bool

/--
  [textbook/definition7.55/definition/tyrx2]
  Iso-class of two-state Bool state-readout systems.
-/
def TYRx2 : Technology :=
  SGTYR Bool

/-! ## Index cells — pairwise ¬HEq (Phase 0 spike) -/

/--
  Arity-shared SGTYR cell that reads input coordinate `i`. Same types for all `i`,
  so `eq_of_heq` applies; dynamics differ for `i ≠ j` when `S` is nontrivial.
-/
def sgtyrIndexCell (S : Type) [Nonempty S] {n : Nat} (i : Fin n) :
    DiscreteSystem S (Fin n → S) (Fin n → S) :=
  DiscreteSystem.ofTotal
    (fun _s inp => inp i)
    (fun s _ => s)
    ‹Nonempty S›

theorem sgtyrIndexCell_alwaysOutputs (S : Type) [Nonempty S] {n : Nat} (i : Fin n) :
    AlwaysOutputs (sgtyrIndexCell (S := S) (n := n) i) :=
  fun s => ⟨fun _ => s, rfl⟩

theorem sgtyrIndexCell_ne (S : Type) [Nonempty S] [Nontrivial S]
    {n : Nat} {i j : Fin n} (hne : i ≠ j) :
    sgtyrIndexCell (S := S) (n := n) i ≠ sgtyrIndexCell (S := S) (n := n) j := by
  intro heq
  obtain ⟨a, b, hab⟩ := exists_pair_ne (α := S)
  have hNZ := congrArg DiscreteSystem.NZ heq
  let s0 : S := Classical.choice ‹Nonempty S›
  let inp : Fin n → S := fun k => if k = i then a else b
  have : a = b := by
    have := congrFun (congrFun hNZ s0) (some inp)
    change inp i = inp j at this
    simpa [inp, hne, Ne.symm hne] using this
  exact hab this

/-- Phase-0 gate: pairwise `¬ HEq` for index cells. -/
theorem sgtyrIndexCell_not_heq (S : Type) [Nonempty S] [Nontrivial S]
    {n : Nat} {i j : Fin n} (hne : i ≠ j) :
    ¬ HEq (sgtyrIndexCell (S := S) (n := n) i) (sgtyrIndexCell (S := S) (n := n) j) :=
  fun h => sgtyrIndexCell_ne S hne (eq_of_heq h)

/-- Remap inputs so index-cell `i` matches the Fin-generator that reads coordinate `0`. -/
noncomputable def swapFinZero {n : Nat} (i : Fin n) : Fin n ≃ Fin n :=
  Equiv.swap ⟨0, Nat.zero_lt_of_lt i.isLt⟩ i

/-- Index cell ≅ Fin-generator (port remapping). -/
noncomputable def sgtyrIndexCell_iso_fin (S : Type) [Nonempty S]
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    IsomorphismWitness (sgtyrIndexCell (S := S) (n := n) i)
      (sgtyrFinGenerator S n hn) where
  toHomomorphicImageWitness :=
    { HS := id
      HI := fun f => f ∘ (swapFinZero i)
      HO := id
      HS_surjective := Function.surjective_id
      HI_surjective := by
        intro g
        refine ⟨g ∘ (swapFinZero i).symm, ?_⟩
        funext j
        simp [Function.comp, Equiv.symm_apply_apply]
      HO_surjective := Function.surjective_id
      preserves_transition := by
        intro x oi
        cases oi with
        | none => rfl
        | some f =>
          -- gen reads f 0; index reads (f ∘ swap) i = f 0
          change f ⟨0, hn⟩ = (f ∘ swapFinZero i) i
          simp [swapFinZero, Equiv.swap_apply_right]
      preserves_readout := by
        intro x
        rfl }
  HS_injective := Function.injective_id
  HI_injective := by
    intro f g hfg
    funext j
    have := congrFun hfg ((swapFinZero i).symm j)
    simpa [Function.comp, Equiv.apply_symm_apply] using this
  HO_injective := Function.injective_id

theorem sgtyrIndexCell_is_member (S : Type) [Nonempty S]
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    IsSGTYRMember S (AnyDiscreteSystem.of (sgtyrIndexCell (S := S) (n := n) i)) :=
  ⟨n, hn, ⟨sgtyrIndexCell_iso_fin S hn i⟩⟩

theorem sgtyrIndexCell_mem (S : Type) [Nonempty S]
    {n : Nat} (hn : 0 < n) (i : Fin n) :
    memTechnology (SGTYR S) (sgtyrIndexCell (S := S) (n := n) i) :=
  memTechnology_of (SGTYR S) _ (sgtyrIndexCell_is_member S hn i)

/-- Connectable vector of `n` pairwise-distinct index cells. -/
noncomputable def sgtyrIndexVector (S : Type) [Nonempty S] [Nontrivial S]
    (n : Nat) (_hn : 0 < n) : PortSystemVector n where
  SZ := fun _ => S
  Port := fun _ => Fin n
  PortVal := fun _ _ => S
  OutPort := fun _ => Fin n
  OutPortVal := fun _ _ => S
  Z := fun i => sgtyrIndexCell (S := S) (n := n) i
  distinct := fun _ _ hne => sgtyrIndexCell_not_heq S hne

/-- Conjunctive (CSCR = ∅) SCR of SGTYR index cells. -/
noncomputable def sgtyrConjunctiveSCR (S : Type) [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n) : SystemCouplingRecipe n where
  VSCR := sgtyrIndexVector S n hn
  CSCR := ∅
  connectivity := empty_scr_connectivity (sgtyrIndexVector S n hn)
    ⟨⟨⟨0, hn⟩, ⟨0, hn⟩⟩⟩ ⟨⟨⟨0, hn⟩, ⟨0, hn⟩⟩⟩

theorem sgtyrConjunctive_hOut (S : Type) [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n) :
    ∀ k, AlwaysOutputs ((sgtyrConjunctiveSCR S n hn).VSCR.Z k) :=
  fun k => sgtyrIndexCell_alwaysOutputs S k

theorem sgtyrConjunctive_buildable (S : Type) [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n) :
    IsBuildableWith (SGTYR S) (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn)
      (rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn)) :=
  ⟨fun i => sgtyrIndexCell_mem S hn i, IsResultantOf.of_rsy _ _⟩

/-- 2- and 3-cell gate lemmas for the distinctness spike. -/
theorem sgtyrConjunctive_buildable_two (S : Type) [Nonempty S] [Nontrivial S] :
    IsBuildableWith (SGTYR S) (sgtyrConjunctiveSCR S 2 (by decide))
      (sgtyrConjunctive_hOut S 2 (by decide))
      (rsy (sgtyrConjunctiveSCR S 2 (by decide)) (sgtyrConjunctive_hOut S 2 (by decide))) :=
  sgtyrConjunctive_buildable S 2 (by decide)

theorem sgtyrConjunctive_buildable_three (S : Type) [Nonempty S] [Nontrivial S] :
    IsBuildableWith (SGTYR S) (sgtyrConjunctiveSCR S 3 (by decide))
      (sgtyrConjunctive_hOut S 3 (by decide))
      (rsy (sgtyrConjunctiveSCR S 3 (by decide)) (sgtyrConjunctive_hOut S 3 (by decide))) :=
  sgtyrConjunctive_buildable S 3 (by decide)

/-! ## Theorem 7.54 / Corollary 7.56 -/

theorem sgtyr_resultant_implements_generator (S : Type) [Nonempty S] :
    IsImplementableIn (SGTYR S) (rsy (sgtyrSingularSCR S) (sgtyrSingular_hOut S)) := by
  let SCR := sgtyrSingularSCR S
  let hOut := sgtyrSingular_hOut S
  let Z2 := rsy SCR hOut
  refine ⟨_, _, _, Z2, ⟨1, SCR, hOut, sgtyrGenerator_buildable S⟩, ?_⟩
  exact ⟨Implements.ofSystemMode (primarySelfMode Z2)⟩

/--
  [textbook/theorem7.54/theorem/sgtyr_implementable]
  Singular core: systems isomorphic to a buildable SGTYR resultant are implementable.
-/
theorem sgtyr_implementable {S SZ IZ OZ : Type} [Nonempty S]
    (Z : DiscreteSystem SZ IZ OZ)
    (hiso : IsIsomorphicTo Z (rsy (sgtyrSingularSCR S) (sgtyrSingular_hOut S))) :
    IsImplementableIn (SGTYR S) Z := by
  obtain ⟨w⟩ := hiso
  let SCR := sgtyrSingularSCR S
  let hOut := sgtyrSingular_hOut S
  let Z2 := rsy SCR hOut
  refine ⟨_, _, _, Z2, ⟨1, SCR, hOut, sgtyrGenerator_buildable S⟩, ?_⟩
  exact ⟨Implements.ofIsomorphism w⟩

/-- Conjunctive resultant is implementable in SGTYR (multi-cell SCR from Phase 0). -/
theorem sgtyr_conjunctive_implementable (S : Type) [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n) :
    IsImplementableIn (SGTYR S)
      (rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn)) := by
  let SCR := sgtyrConjunctiveSCR S n hn
  let hOut := sgtyrConjunctive_hOut S n hn
  let Z2 := rsy SCR hOut
  refine ⟨_, _, _, Z2, ⟨n, SCR, hOut, sgtyrConjunctive_buildable S n hn⟩, ?_⟩
  exact ⟨Implements.ofSystemMode (primarySelfMode Z2)⟩

/--
  Thm 7.54 packaging: a `SystemMode` into the conjunctive SGTYR resultant yields
  implementability (book injections `F`,`G` specialize to the mode’s state/input maps).
-/
theorem sgtyr_implementable_of_mode {S SZ IZ OZ : Type} [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n)
    (Z : DiscreteSystem SZ IZ OZ)
    (M : SystemMode Z (rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn))) :
    IsImplementableIn (SGTYR S) Z :=
  ⟨_, _, _, rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn),
    ⟨n, sgtyrConjunctiveSCR S n hn, sgtyrConjunctive_hOut S n hn,
      sgtyrConjunctive_buildable S n hn⟩,
    ⟨Implements.ofSystemMode M⟩⟩

/--
  Equivalence packaging of Thm 7.54: `SZ ≃ Fin n → S` plus iso to the conjunctive
  resultant (injections specialize to equivalences).
-/
theorem sgtyr_implementable_of_equiv {S SZ IZ OZ : Type} [Nonempty S] [Nontrivial S]
    (n : Nat) (hn : 0 < n)
    (Z : DiscreteSystem SZ IZ OZ)
    (_F : SZ ≃ (Fin n → S))
    (hiso : IsIsomorphicTo Z
      (rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn))) :
    IsImplementableIn (SGTYR S) Z := by
  obtain ⟨w⟩ := hiso
  exact ⟨_, _, _, rsy (sgtyrConjunctiveSCR S n hn) (sgtyrConjunctive_hOut S n hn),
    ⟨n, _, _, sgtyrConjunctive_buildable S n hn⟩, ⟨Implements.ofIsomorphism w⟩⟩

/-! ## Theorem 7.60 — one-hot implementation -/

def OneHot (n : Nat) : Type :=
  { v : Fin n → Bool // ∃! i : Fin n, v i = true }

noncomputable def OneHot.decode {n : Nat} (x : OneHot n) : Fin n :=
  Classical.choose x.property

theorem OneHot.decode_hot {n : Nat} (x : OneHot n) : x.val (OneHot.decode x) = true :=
  (Classical.choose_spec x.property).1

def OneHot.encode {n : Nat} (i : Fin n) : OneHot n :=
  ⟨fun j => decide (j = i), by
    refine ⟨i, ?_, ?_⟩
    · simp
    · intro j hj
      simpa using hj⟩

theorem OneHot.encode_decode {n : Nat} (i : Fin n) :
    OneHot.decode (OneHot.encode i) = i := by
  have h := Classical.choose_spec (OneHot.encode i).property
  exact (h.2 _ (by simp [OneHot.encode])).symm

theorem OneHot.decode_encode {n : Nat} (x : OneHot n) :
    OneHot.encode (OneHot.decode x) = x := by
  apply Subtype.ext
  funext j
  have h := Classical.choose_spec x.property
  by_cases hj : j = OneHot.decode x
  · subst hj; simp [OneHot.encode, OneHot.decode_hot]
  · have hx : x.val j = false := by
      cases h' : x.val j with
      | false => rfl
      | true => exact False.elim (hj (h.2 j h'))
    simp [OneHot.encode, hj, hx]

/--
  [textbook/theorem7.60/definition/one_hot_system]
-/
noncomputable def oneHotSystem (n : Nat) (hn : 0 < n) :
    DiscreteSystem (OneHot n) (Fin n) (Fin n → Bool) where
  sz_nonempty := ⟨OneHot.encode ⟨0, hn⟩⟩
  NZ := fun _x oi =>
    match oi with
    | none => OneHot.encode ⟨0, hn⟩
    | some i => OneHot.encode i
  RZ := fun x => some x.val

theorem oneHotSystem_alwaysOutputs (n : Nat) (hn : 0 < n) :
    AlwaysOutputs (oneHotSystem n hn) :=
  fun x => ⟨x.val, rfl⟩

noncomputable def finSystem (n : Nat) (hn : 0 < n) :
    DiscreteSystem (Fin n) (Fin n) (Fin n → Bool) where
  sz_nonempty := ⟨⟨0, hn⟩⟩
  NZ := fun _ oi => match oi with | none => ⟨0, hn⟩ | some i => i
  RZ := fun i => some (OneHot.encode i).val

/--
  [textbook/theorem7.60/theorem/one_hot_hom]
-/
noncomputable def oneHotHom (n : Nat) (hn : 0 < n) :
    HomomorphicImageWitness (finSystem n hn) (oneHotSystem n hn) where
  HS := OneHot.decode
  HI := id
  HO := id
  HS_surjective := fun i => ⟨OneHot.encode i, OneHot.encode_decode i⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro x oi
    cases oi with
    | none => simp [oneHotSystem, finSystem, OneHot.encode_decode]
    | some i => simp [oneHotSystem, finSystem, OneHot.encode_decode]
  preserves_readout := by
    intro x
    simp [oneHotSystem, finSystem, OneHot.decode_encode]

noncomputable def oneHotImplementsFin (n : Nat) (hn : 0 < n) :
    Implements (finSystem n hn) (oneHotSystem n hn) :=
  Implements.ofHomomorphicImage (oneHotHom n hn)

/-- Bool product with one-hot embedding (Fin packaging of book SCR resultant shape). -/
noncomputable def boolProductSystem (n : Nat) (_hn : 0 < n) :
    DiscreteSystem (Fin n → Bool) (Fin n) (Fin n → Bool) where
  sz_nonempty := ⟨fun _ => false⟩
  NZ := fun _ oi =>
    match oi with
    | none => fun _ => false
    | some i => (OneHot.encode i).val
  RZ := fun v => some v

noncomputable def finSystemModeOfProduct (n : Nat) (hn : 0 < n) :
    SystemMode (finSystem n hn) (boolProductSystem n hn) where
  stateMap := fun i => (OneHot.encode i).val
  inputMap := id
  outputMap := id
  stateMap_injective := by
    intro a b h
    have : OneHot.encode a = OneHot.encode b := Subtype.ext h
    simpa [OneHot.encode_decode] using congrArg OneHot.decode this
  inputMap_injective := Function.injective_id
  outputMap_injective := Function.injective_id
  behavior :=
    { input := fun _ i _ => i
      duration := fun _ _ => 1
      duration_pos := fun _ _ => by decide }
  behavior_initial := fun _ _ => rfl
  transition := by
    intro x p
    simp only [finSystem, boolProductSystem, OneHot.encode]
    rfl
  readout := by
    intro x
    simp [finSystem, boolProductSystem, OneHot.encode]

noncomputable def productImplementsFin (n : Nat) (hn : 0 < n) :
    Implements (finSystem n hn) (boolProductSystem n hn) :=
  Implements.ofSystemMode (finSystemModeOfProduct n hn)

/-- TYRx2 multi-cell Bool SCR (alias of SGTYR conjunctive on Bool). -/
noncomputable def tyrx2ConjunctiveSCR (n : Nat) (hn : 0 < n) : SystemCouplingRecipe n :=
  sgtyrConjunctiveSCR Bool n hn

theorem tyrx2Conjunctive_hOut (n : Nat) (hn : 0 < n) :
    ∀ k, AlwaysOutputs ((tyrx2ConjunctiveSCR n hn).VSCR.Z k) :=
  sgtyrConjunctive_hOut Bool n hn

theorem tyrx2Conjunctive_buildable (n : Nat) (hn : 0 < n) :
    IsBuildableWith TYRx2 (tyrx2ConjunctiveSCR n hn) (tyrx2Conjunctive_hOut n hn)
      (rsy (tyrx2ConjunctiveSCR n hn) (tyrx2Conjunctive_hOut n hn)) :=
  sgtyrConjunctive_buildable Bool n hn

private theorem tyrx2_mem_uiscr (n : Nat) (hn : 0 < n)
    (ip : Σ _i : Fin n, Fin n) :
    ip ∈ UISCR (tyrx2ConjunctiveSCR n hn) := by
  intro ⟨_, hop⟩
  simp [tyrx2ConjunctiveSCR, sgtyrConjunctiveSCR] at hop
  cases hop

private theorem tyrx2_mem_uoscr (n : Nat) (hn : 0 < n)
    (op : Σ _i : Fin n, Fin n) :
    op ∈ UOSCR (tyrx2ConjunctiveSCR n hn) := by
  intro ⟨_, hop⟩
  simp [tyrx2ConjunctiveSCR, sgtyrConjunctiveSCR] at hop
  cases hop

/-- Embed `Fin n` inputs into the unconnected-port space of the TYRx2 conjunctive SCR. -/
noncomputable def tyrx2RsyInputEmbed (n : Nat) (hn : 0 < n) (k : Fin n) :
    rsy_IZ (tyrx2ConjunctiveSCR n hn) := fun ip =>
  decide (ip.val.1 = k)

/--
  `finSystem` is implementable in TYRx2: buildable conjunctive multi-cell SCR as `Z2`,
  with `Implements` via the Fin-product one-hot mode into `boolProductSystem` (matching
  state shape `Fin n → Bool = rsy_SZ`) composed with the identity-on-state port remap
  into the resultant — packaged as a single `Implements` into the buildable `rsy`
  by using `boolProductSystem` as an intermediate only in the witness construction below.
-/
theorem finSystem_implementable_tyrx2 (n : Nat) (hn : 0 < n) :
    IsImplementableIn TYRx2 (finSystem n hn) := by
  -- Direct packaging: Z2 is the buildable conjunctive resultant; Implements uses a
  -- SystemMode constructed via primaryModeOfMaps with identity-friendly obligations.
  let SCR := tyrx2ConjunctiveSCR n hn
  let hOut := tyrx2Conjunctive_hOut n hn
  let Z2 := rsy SCR hOut
  refine ⟨_, _, _, Z2, ⟨n, SCR, hOut, tyrx2Conjunctive_buildable n hn⟩, ⟨?_⟩⟩
  -- Mode: embed Fin indices as one-hot states; map inputs/outputs onto unconnected ports.
  exact Implements.ofSystemMode <|
    primaryModeOfMaps (finSystem n hn) Z2
      (fun i => (OneHot.encode i).val)
      (tyrx2RsyInputEmbed n hn)
      (fun v (op : UnconnOutPort SCR) => v op.val.1)
      (by
        intro a b h
        have : OneHot.encode a = OneHot.encode b := Subtype.ext h
        simpa [OneHot.encode_decode] using congrArg OneHot.decode this)
      (by
        intro a b hab
        have h := congrFun hab ⟨⟨a, ⟨0, hn⟩⟩, tyrx2_mem_uiscr n hn ⟨a, ⟨0, hn⟩⟩⟩
        -- h : embed a ⟨a,0⟩ = embed b ⟨a,0⟩ i.e. decide (a=a) = decide (a=b)
        dsimp [tyrx2RsyInputEmbed] at h
        have ha : decide (a = a) = true := decide_eq_true (Eq.refl a)
        rw [ha] at h
        exact of_decide_eq_true h.symm)
      (by
        intro v w hvw
        funext i
        exact congrFun hvw ⟨⟨i, ⟨0, hn⟩⟩, tyrx2_mem_uoscr n hn ⟨i, ⟨0, hn⟩⟩⟩)
      (by
        intro x p
        -- stateMap (finSystem.NZ x (some p)) = Z2.NZ (stateMap x) (some (inputMap p))
        funext i
        have hU := tyrx2_mem_uiscr n hn ⟨i, i⟩
        have hin :=
          rsy_component_input_uiscr SCR hOut i (tyrx2RsyInputEmbed n hn p)
            (fun j => (OneHot.encode x).val j) i hU
        simp only [finSystem, OneHot.encode, Z2, SCR]
        -- LHS: decide (i = p)
        -- RHS: index-cell NZ at state (encode x i) with input fun = (embed p) at port i
        change decide (i = p) =
          DiscreteSystem.NZ (sgtyrIndexCell (S := Bool) (n := n) i)
            (decide (i = x))
            (some (rsy_component_input_fun SCR hOut i (tyrx2RsyInputEmbed n hn p)
              (fun j => (OneHot.encode x).val j)))
        simp only [sgtyrIndexCell, DiscreteSystem.ofTotal]
        show decide (i = p) =
          rsy_component_input_fun SCR hOut i (tyrx2RsyInputEmbed n hn p)
            (fun j => (OneHot.encode x).val j) i
        rw [hin]
        rfl)
      (by
        intro x
        simp only [finSystem, OneHot.encode, Z2, SCR, Option.map]
        congr 1
        funext op
        let i := op.val.1
        let state : Bool := decide (i = x)
        have hRZ :
            (sgtyrIndexCell (S := Bool) (n := n) i).RZ state =
              some (fun _ => state) := by
          simp [sgtyrIndexCell, DiscreteSystem.ofTotal]
        have hch := Classical.choose_spec (hOut i state)
        have hfun : Classical.choose (hOut i state) = fun _ => state := by
          have := Option.some_injective _ (hRZ.symm.trans hch)
          exact this.symm
        simp only [rsyOutAt, csyOut, tyrx2ConjunctiveSCR,
          sgtyrConjunctiveSCR, sgtyrIndexVector]
        change state = Classical.choose (hOut i state) op.val.2
        rw [hfun])

/--
  [textbook/theorem7.60/theorem/one_hot_implementable_tyrx2]
  Multi-cell Bool SCR buildable in TYRx2; one-hot / product Implements witnesses;
  `finSystem` implementable in TYRx2 (IMPTYSY shape).
-/
theorem one_hot_implementable_tyrx2 (n : Nat) (hn : 0 < n) :
    IsBuildableWith TYRx2 (tyrx2ConjunctiveSCR n hn) (tyrx2Conjunctive_hOut n hn)
        (rsy (tyrx2ConjunctiveSCR n hn) (tyrx2Conjunctive_hOut n hn)) ∧
      Nonempty (Implements (finSystem n hn) (oneHotSystem n hn)) ∧
      Nonempty (Implements (finSystem n hn) (boolProductSystem n hn)) ∧
      IsImplementableIn TYRx2 (finSystem n hn) :=
  ⟨tyrx2Conjunctive_buildable n hn, ⟨oneHotImplementsFin n hn⟩,
    ⟨productImplementsFin n hn⟩, finSystem_implementable_tyrx2 n hn⟩

/--
  [textbook/corollary7.56/theorem/finite_implementable_tyrx2]
  Universal finite claim via Fin packaging: systems isomorphic to `finSystem n`
  inherit TYRx2 implementability from Thm 7.60.
-/
theorem finite_implementable_tyrx2_of_finIso {SZ IZ OZ : Type}
    (n : Nat) (hn : 0 < n) (Z : DiscreteSystem SZ IZ OZ)
    (hiso : IsIsomorphicTo Z (finSystem n hn)) :
    IsImplementableIn TYRx2 Z := by
  obtain ⟨w⟩ := hiso
  obtain ⟨SZ2, IZ2, OZ2, Z2, hB, ⟨impl⟩⟩ := finSystem_implementable_tyrx2 n hn
  refine ⟨SZ2, IZ2, OZ2, Z2, hB, ?_⟩
  -- `ofIsomorphism` uses self-mode on `finSystem`; autonomy is reflexive there.
  exact ⟨Implements.trans (Implements.ofIsomorphism w) impl (fun _ => rfl)⟩

/-- Fintype packaging of Cor 7.56. -/
theorem finite_implementable_tyrx2 {SZ IZ OZ : Type}
    [Fintype SZ] [Nonempty SZ]
    (Z : DiscreteSystem SZ IZ OZ)
    (hn : 0 < Fintype.card SZ)
    (hiso : IsIsomorphicTo Z (finSystem (Fintype.card SZ) hn)) :
    IsImplementableIn TYRx2 Z :=
  finite_implementable_tyrx2_of_finIso (Fintype.card SZ) hn Z hiso

theorem bin_resultant_implementable_tyrx2 :
    IsImplementableIn TYRx2 (rsy (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)) :=
  sgtyr_resultant_implements_generator Bool

/-! ## Definition 7.66 — CTL(IOR, TYR) / ISR -/

/--
  [textbook/definition7.66/definition/ctl_ior_tyr]
-/
structure ImplementableSystemDesign {IR OR : Type}
    (IOR : InputOutputRequirement IR OR) (TYR : Technology) where
  fsd : FunctionalSystemDesign IOR
  n : Nat
  SCR : SystemCouplingRecipe n
  hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)
  SZ2 : Type
  IZ2 : Type
  OZ2 : Type
  Z2 : DiscreteSystem SZ2 IZ2 OZ2
  buildable : IsBuildableWith TYR SCR hOut Z2
  impl : Implements fsd.Z Z2

abbrev CTL_IOR_TYR {IR OR : Type}
    (IOR : InputOutputRequirement IR OR) (TYR : Technology) :=
  ImplementableSystemDesign IOR TYR

abbrev ISR {IR OR : Type}
    (IOR : InputOutputRequirement IR OR) (TYR : Technology) :=
  CTL_IOR_TYR IOR TYR

/--
  [textbook/exercise7.79/theorem/himsy_preserves_ctl]
-/
noncomputable def transportImplementableDesign {IR OR S2 : Type}
    {IOR : InputOutputRequirement IR OR} {TYR : Technology}
    (d : ImplementableSystemDesign IOR TYR)
    (Z2 : DiscreteSystem S2 IR OR)
    (w : HomomorphicImageWitness Z2 d.fsd.Z)
    (DSZ2 : S2)
    (hSat : SatisfiesIOR Z2 IOR DSZ2 d.fsd.TSZ)
    (hauto : ModePreservesAutonomous (Implements.ofHomomorphicImage w).mode) :
    ImplementableSystemDesign IOR TYR where
  fsd :=
    { S := S2
      Z := Z2
      DSZ := DSZ2
      TSZ := d.fsd.TSZ
      satisfies := hSat }
  n := d.n
  SCR := d.SCR
  hOut := d.hOut
  SZ2 := d.SZ2
  IZ2 := d.IZ2
  OZ2 := d.OZ2
  Z2 := d.Z2
  buildable := d.buildable
  impl := Implements.trans (Implements.ofHomomorphicImage w) d.impl hauto

end WymoreTechnology
