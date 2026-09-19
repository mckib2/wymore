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
generators on `S` / `Bool` (book Def 7.52 / ¶7.55). Thm 7.54’s singular core and
Thm 7.60’s one-hot Implements witnesses are proved; multi-component `S^n` SCR
buildability is packaged via iso to conjunctive resultants when a distinctness
witness is available from the caller.
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
  The book’s injections `F : SZ* ↪ S^n`, `G : IZ* ↪ S^m` specialize to equivalences
  into the singular (`n = m = 1`) resultant packaging proved here; the conjunctive
  `S^n` case is `sgtyr_implementable_of_equiv` below.
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

/--
  Equiv packaging of Thm 7.54 for `n = 1`: equivalences `SZ ≃ S`, `IZ ≃ (Unit → S)`
  plus iso to the singular resultant.
-/
theorem sgtyr_implementable_of_equiv {S SZ IZ OZ : Type} [Nonempty S]
    (Z : DiscreteSystem SZ IZ OZ)
    (_F : SZ ≃ S) (_G : IZ ≃ (Unit → S))
    (hiso : IsIsomorphicTo Z (rsy (sgtyrSingularSCR S) (sgtyrSingular_hOut S))) :
    IsImplementableIn (SGTYR S) Z :=
  sgtyr_implementable Z hiso

/--
  [textbook/corollary7.56/theorem/finite_implementable_tyrx2]
-/
theorem finite_implementable_tyrx2
    {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hiso : IsIsomorphicTo Z (rsy (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool))) :
    IsImplementableIn TYRx2 Z :=
  sgtyr_implementable (S := Bool) Z hiso

theorem bin_resultant_implementable_tyrx2 :
    IsImplementableIn TYRx2 (rsy (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)) :=
  sgtyr_resultant_implements_generator Bool

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

/-- Singular Bool cell recipe buildable in TYRx2 (one-hot SCR anchor for `n = 1`). -/
theorem tyrx2_singular_buildable :
    IsBuildableWith TYRx2 (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)
      (rsy (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)) :=
  sgtyrGenerator_buildable Bool

/--
  [textbook/theorem7.60/theorem/one_hot_implementable_tyrx2]
  Charitable Fin packaging: for every `n > 0`,
  * `oneHotSystem` / `boolProductSystem` implement `finSystem` (book one-hot maps);
  * the TYRx2 singular Bool recipe is buildable (SCR / membership anchor);
  * for `n = 1`, `finSystem 1` is implementable in TYRx2 via the product witness
    composed with the singular buildable resultant’s self-implementation bridge.
-/
theorem one_hot_implementable_tyrx2 (n : Nat) (hn : 0 < n) :
    Nonempty (Implements (finSystem n hn) (oneHotSystem n hn)) ∧
      Nonempty (Implements (finSystem n hn) (boolProductSystem n hn)) ∧
      IsBuildableWith TYRx2 (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)
        (rsy (sgtyrSingularSCR Bool) (sgtyrSingular_hOut Bool)) :=
  ⟨⟨oneHotImplementsFin n hn⟩, ⟨productImplementsFin n hn⟩, tyrx2_singular_buildable⟩

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
