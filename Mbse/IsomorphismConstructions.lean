import Mbse.Isomorphism

/-!
# Chapter 4: constructions of elaborations, copies and isomorphs

Concrete constructions accompanying the Chapter 4 algebra in [`Mbse.Isomorphism`](Isomorphism.lean):

* Definition A1.189 — choice functions `CHF(A)`.
* Theorem 4.58 — recoding an output port through a bijection yields a copy.
* Exercise 4.69 — a finite system *can* be a homomorphic image of a non-finite system
  (the assertion is refuted by a counterexample).
* Exercise 4.71 — every system is a homomorphic image of an explicitly constructed system.
* Exercise 4.72 — consistent elaboration with respect to states.
* Exercise 4.74 — consistent elaboration with respect to states, inputs and outputs.
* Exercise 4.83 — mutually homomorphic finite systems are isomorphic.
-/

namespace Homomorphism

/-! ## Definition A1.189: choice functions -/

/--
  [textbook/definition_a1.189/definition/chf]
  `CHF(A)`: a choice function for the subsets of `A` is a map `𝒫A → A` sending every nonempty
  `B ⊆ A` to an element of `B`.
-/
structure ChoiceFunction (A : Type) where
  /-- [textbook/definition_a1.189/component/function] `CHA ∈ FNS(𝒫A, A)`. -/
  pick : Set A → A
  /-- [textbook/definition_a1.189/requirement/mem] If `B ⊆ A` and `B ≠ ∅` then `CHA(B) ∈ B`. -/
  pick_mem : ∀ B : Set A, B.Nonempty → pick B ∈ B

/--
  [textbook/definition_a1.189/theorem/exists]
  `CHF(A) ≠ ∅` for every nonempty `A`.
-/
noncomputable def ChoiceFunction.ofNonempty (A : Type) [Nonempty A] : ChoiceFunction A := by
  classical
  exact
    { pick := fun B => if h : B.Nonempty then h.choose else Classical.arbitrary A
      pick_mem := fun B hB => by rw [dif_pos hB]; exact hB.choose_spec }

/-- The chosen element of a nonempty preimage `f ⁻¹' {y}` is a genuine preimage of `y`. -/
theorem ChoiceFunction.apply_pick_preimage {A B : Type} (ch : ChoiceFunction A) {f : A → B}
    (hf : Function.Surjective f) (y : B) : f (ch.pick (f ⁻¹' {y})) = y := by
  have hne : (f ⁻¹' {y}).Nonempty := by
    obtain ⟨a, ha⟩ := hf y
    exact ⟨a, ha⟩
  exact ch.pick_mem _ hne

/-! ## Theorem 4.58: recoding output ports through bijections produces a copy -/

/--
  [textbook/theorem4.58/definition/recoded_system]
  `Z₂` recodes each output port of `Z₁` along a bijection `Fq : OqZ₁ ≃ OqZ₂`, leaving `SZ`, `IZ`
  and `NZ` untouched and post-composing the readout.
-/
def recodeOutPorts {SZ IZ OutPort : Type} {OutVal1 OutVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ IZ ((q : OutPort) → OutVal1 q))
    (Fq : (q : OutPort) → OutVal1 q ≃ OutVal2 q) :
    DiscreteSystem SZ IZ ((q : OutPort) → OutVal2 q) where
  sz_nonempty := Z1.sz_nonempty
  NZ := Z1.NZ
  RZ := fun x => (Z1.RZ x).map (fun o q => Fq q (o q))

/--
  [textbook/theorem4.58/proof/copy_witness]
  The recoded system is a copy of the original: `HS = ID(SZ₁)`, `HI = ID(IZ₁)`, and `HO` is the
  portwise product of the `Fq`, so `SHOS = {Fq}`.
-/
def recodeOutPorts_copyWitness {SZ InPort OutPort : Type}
    {InVal : InPort → Type} {OutVal1 OutVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ ((p : InPort) → InVal p) ((q : OutPort) → OutVal1 q))
    (Fq : (q : OutPort) → OutVal1 q ≃ OutVal2 q) :
    CopyWitness (recodeOutPorts Z1 Fq) Z1 where
  HS := id
  HI := id
  HO := fun o q => Fq q (o q)
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := by
    intro g
    exact ⟨fun q => (Fq q).symm (g q), funext fun q => (Fq q).apply_symm_apply (g q)⟩
  HS_injective := Function.injective_id
  HI_injective := Function.injective_id
  HO_injective := by
    intro a b hab
    funext q
    exact (Fq q).injective (congr_fun hab q)
  preserves_transition := by intro x oi; simp [recodeOutPorts]
  preserves_readout := by intro x; rfl
  inIdx := Equiv.refl InPort
  outIdx := Equiv.refl OutPort
  inPorts := PreservesPorts.id
  outPorts :=
    { port := fun q => Fq q
      port_surjective := fun q => (Fq q).surjective
      proj := fun _ _ => rfl }

/--
  [textbook/theorem4.58/definition/output_port_values]
  Ex 4.58's output port value family: port `n` now carries `B`, every other port is unchanged.
-/
def replaceOutVal {OutPort : Type} [DecidableEq OutPort]
    (OutVal1 : OutPort → Type) (n : OutPort) (B : Type) : OutPort → Type :=
  fun q => if q = n then B else OutVal1 q

/-- Port `n` of the replaced family carries `B`. -/
theorem replaceOutVal_self {OutPort : Type} [DecidableEq OutPort]
    (OutVal1 : OutPort → Type) (n : OutPort) (B : Type) :
    replaceOutVal OutVal1 n B n = B := by
  simp [replaceOutVal]

/-- Every other port of the replaced family is unchanged. -/
theorem replaceOutVal_of_ne {OutPort : Type} [DecidableEq OutPort]
    (OutVal1 : OutPort → Type) {n q : OutPort} (h : q ≠ n) (B : Type) :
    replaceOutVal OutVal1 n B q = OutVal1 q := by
  simp [replaceOutVal, h]

/--
  [textbook/theorem4.58/definition/port_equiv_family]
  `SHOS`: the identity on every port except `n`, where it is the given bijection `F`.
-/
def replaceOutValEquiv {OutPort : Type} [DecidableEq OutPort]
    {OutVal1 : OutPort → Type} {n : OutPort} {B : Type} (F : OutVal1 n ≃ B) (q : OutPort) :
    OutVal1 q ≃ replaceOutVal OutVal1 n B q :=
  if h : q = n then
    ((Equiv.cast (congrArg OutVal1 h)).trans F).trans
      (Equiv.cast (replaceOutVal_self OutVal1 n B).symm |>.trans
        (Equiv.cast (congrArg (replaceOutVal OutVal1 n B) h.symm)))
  else
    Equiv.cast (replaceOutVal_of_ne OutVal1 h B).symm

/--
  [textbook/theorem4.58/theorem/replacement_is_copy]
  Theorem 4.58: if the port-homomorphism hypothesis fails at output port `n`, the offending
  component may be replaced by the system `Z₂` that carries the equivalent set `B` at port `n`.
  Then `Z₂ ∈ DSYSTEMS`, `OnZ₂ = B`, and `Z₂ = COPY(Z₁, ID(SZ₁), ID(IZ₁), HO, SHIS, SHOS)`.
-/
theorem replaceOutPort_isCopy {SZ InPort OutPort : Type} [DecidableEq OutPort]
    {InVal : InPort → Type} {OutVal1 : OutPort → Type}
    (Z1 : DiscreteSystem SZ ((p : InPort) → InVal p) ((q : OutPort) → OutVal1 q))
    (n : OutPort) {B : Type} (F : OutVal1 n ≃ B) :
    replaceOutVal OutVal1 n B n = B ∧
      IsCopyOf (recodeOutPorts Z1 (replaceOutValEquiv F)) Z1 :=
  ⟨replaceOutVal_self OutVal1 n B, ⟨recodeOutPorts_copyWitness Z1 (replaceOutValEquiv F)⟩⟩

/-! ## Exercise 4.69: a finite system can be a homomorphic image of a non-finite one -/

/-- A non-finite system: the state counter on `ℕ`. -/
def counterElaboration : DiscreteSystem Nat Unit Unit where
  sz_nonempty := ⟨0⟩
  NZ := fun x _ => x + 1
  RZ := fun _ => some ()

/-- A finite system: the one-state system on `Unit`. -/
def pointImage : DiscreteSystem Unit Unit Unit where
  sz_nonempty := ⟨()⟩
  NZ := fun _ _ => ()
  RZ := fun _ => some ()

/--
  [textbook/exercise4.69/proof/counterexample_witness]
  Collapsing every state of the counter to the single state of `pointImage` is a homomorphism.
-/
def pointImage_witness : HomomorphicImageWitness pointImage counterElaboration where
  HS := fun _ => ()
  HI := id
  HO := id
  HS_surjective := fun _ => ⟨0, rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by intro x oi; rfl
  preserves_readout := by intro x; rfl

theorem pointImage_isFinite : IsFinite pointImage :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem counterElaboration_not_isFinite : ¬ IsFinite counterElaboration := by
  intro h
  exact Infinite.not_finite (α := Nat) h.1

/--
  [textbook/exercise4.69/theorem/counterexample]
  Exercise 4.69: the assertion is **false**. `pointImage` is finite, `counterElaboration` is not,
  and yet `pointImage` is a homomorphic image of `counterElaboration`.
-/
theorem ex4_69_counterexample :
    IsFinite pointImage ∧ ¬ IsFinite counterElaboration ∧
      IsHomomorphicImage pointImage counterElaboration :=
  ⟨pointImage_isFinite, counterElaboration_not_isFinite, ⟨pointImage_witness⟩⟩

/--
  [textbook/exercise4.69/theorem/assertion_refuted]
  Exercise 4.69: the stated assertion — a finite system is never a homomorphic image of a
  non-finite system — does not hold.
-/
theorem ex4_69_assertion_false :
    ¬ ∀ (SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type)
        (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2),
        IsFinite Z1 → ¬ IsFinite Z2 → ¬ IsHomomorphicImage Z1 Z2 := by
  intro h
  exact h _ _ _ _ _ _ pointImage counterElaboration pointImage_isFinite
    counterElaboration_not_isFinite ⟨pointImage_witness⟩

/-! ## Exercise 4.71: a system of which a given system is a homomorphic image -/

/--
  [textbook/exercise4.71/definition/state_space]
  `SZ₂ = {(x, NZ₁(x, p)) : x ∈ SZ₁, p ∈ IZ₁} ∪ {(x, x) : x ∈ SZ₁}`, modeled as a subtype of
  `SZ₁ × SZ₁`. The autonomous step `none` of the `Option` encoding is admitted alongside the
  textbook's inputs `p ∈ IZ₁`.
-/
def PredecessorState {SZ IZ OZ : Type} (Z1 : DiscreteSystem SZ IZ OZ) : Type :=
  { xy : SZ × SZ // xy.2 = xy.1 ∨ ∃ oi, xy.2 = Z1.NZ xy.1 oi }

/--
  [textbook/exercise4.71/definition/system]
  `Z₂ = (SZ₂, IZ₁, OZ₁, NZ₂, RZ₂)` with `NZ₂((x, y), p) = (y, NZ₁(y, p))` and `RZ₂ = RZ₁ ∘ PJN₂`.
-/
def predecessorSystem {SZ IZ OZ : Type} (Z1 : DiscreteSystem SZ IZ OZ) :
    DiscreteSystem (PredecessorState Z1) IZ OZ where
  sz_nonempty :=
    have : Nonempty SZ := Z1.sz_nonempty
    ⟨⟨(Classical.arbitrary SZ, Classical.arbitrary SZ), Or.inl rfl⟩⟩
  NZ := fun y oi => ⟨(y.1.2, Z1.NZ y.1.2 oi), Or.inr ⟨oi, rfl⟩⟩
  RZ := fun y => Z1.RZ y.1.2

/--
  [textbook/exercise4.71/proof/homomorphism]
  `PJN₂` is the state homomorphism: `Z₁ = HIMSY(Z₂, PJN(SZ₂, 2), ID(IZ₂), ID(OZ₂))`.
-/
def predecessorSystem_witness {SZ IZ OZ : Type} (Z1 : DiscreteSystem SZ IZ OZ) :
    HomomorphicImageWitness Z1 (predecessorSystem Z1) where
  HS := fun y => y.1.2
  HI := id
  HO := id
  HS_surjective := fun x => ⟨⟨(x, x), Or.inl rfl⟩, rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by intro y oi; simp [predecessorSystem]
  preserves_readout := by intro y; simp [predecessorSystem]

/--
  [textbook/exercise4.71/theorem/construction]
  Exercise 4.71: the constructed `Z₂` is a discrete system of which `Z₁` is the homomorphic image
  under the second projection.
-/
theorem ex4_71_construction {SZ IZ OZ : Type} (Z1 : DiscreteSystem SZ IZ OZ) :
    (∀ (y : PredecessorState Z1) (oi : Option IZ),
        ((predecessorSystem Z1).NZ y oi).1 = (y.1.2, Z1.NZ y.1.2 oi)) ∧
      (∀ y : PredecessorState Z1, (predecessorSystem Z1).RZ y = Z1.RZ y.1.2) ∧
      IsHomomorphicImage Z1 (predecessorSystem Z1) :=
  ⟨fun _ _ => rfl, fun _ => rfl, ⟨predecessorSystem_witness Z1⟩⟩

/-! ## Exercise 4.72: consistent elaboration with respect to states -/

/--
  [textbook/exercise4.72/definition/state_partition]
  The data `F ∈ FNS(SZ₁, 1TO1, 𝒫S)` of Exercise 4.72: a family of pairwise disjoint nonempty
  subsets of `S`, one for each state of `Z₁`.
-/
structure StatePartition (SZ1 S : Type) where
  /-- [textbook/exercise4.72/component/F] `F ∈ FNS(SZ₁, 𝒫S)`. -/
  F : SZ1 → Set S
  /-- Each block is nonempty (otherwise `HS` could not be `ONTO`). -/
  block_nonempty : ∀ x, (F x).Nonempty
  /-- [textbook/exercise4.72/requirement/disjoint] `x₁ ≠ x₂ → F(x₁) ∩ F(x₂) = ∅`. -/
  block_disjoint : ∀ x1 x2, x1 ≠ x2 → ∀ s, s ∈ F x1 → s ∈ F x2 → False

/--
  [textbook/exercise4.72/theorem/F_injective]
  `F` is automatically `1TO1`: distinct states have disjoint nonempty blocks.
-/
theorem StatePartition.F_injective {SZ1 S : Type} (e : StatePartition SZ1 S) :
    Function.Injective e.F := by
  intro x1 x2 h
  by_contra hne
  obtain ⟨s, hs⟩ := e.block_nonempty x1
  exact e.block_disjoint x1 x2 hne s hs (h ▸ hs)

/-- [textbook/exercise4.72/definition/state_space] `SZ₂ = ∪ RNG(F)`. -/
def StatePartition.State {SZ1 S : Type} (e : StatePartition SZ1 S) : Type :=
  { s : S // ∃ x, s ∈ e.F x }

/-- [textbook/exercise4.72/definition/HS] `HS` sends a point of `SZ₂` to the block containing it. -/
noncomputable def StatePartition.proj {SZ1 S : Type} (e : StatePartition SZ1 S)
    (s : e.State) : SZ1 :=
  s.2.choose

theorem StatePartition.mem_proj {SZ1 S : Type} (e : StatePartition SZ1 S) (s : e.State) :
    s.1 ∈ e.F (e.proj s) :=
  s.2.choose_spec

/-- Blocks are disjoint, so membership determines the block. -/
theorem StatePartition.proj_eq {SZ1 S : Type} (e : StatePartition SZ1 S) (s : e.State)
    {x : SZ1} (h : s.1 ∈ e.F x) : e.proj s = x := by
  by_contra hne
  exact e.block_disjoint (e.proj s) x hne s.1 (e.mem_proj s) h

/-- The canonical point of the block `F x`, used to show `HS` is `ONTO`. -/
noncomputable def StatePartition.rep {SZ1 S : Type} (e : StatePartition SZ1 S) (x : SZ1) :
    e.State :=
  ⟨(e.block_nonempty x).choose, ⟨x, (e.block_nonempty x).choose_spec⟩⟩

theorem StatePartition.proj_rep {SZ1 S : Type} (e : StatePartition SZ1 S) (x : SZ1) :
    e.proj (e.rep x) = x :=
  e.proj_eq _ (e.block_nonempty x).choose_spec

theorem StatePartition.proj_surjective {SZ1 S : Type} (e : StatePartition SZ1 S) :
    Function.Surjective e.proj :=
  fun x => ⟨e.rep x, e.proj_rep x⟩

theorem StatePartition.rep_injective {SZ1 S : Type} (e : StatePartition SZ1 S) :
    Function.Injective e.rep :=
  Function.LeftInverse.injective e.proj_rep

/--
  [textbook/exercise4.72/definition/system]
  `Z₂ = (∪RNG(F), IZ₁, OZ₁, NZ₂, RZ₂)` with `NZ₂(x, p) = CHS(F(NZ₁(HS(x), p)))` and
  `RZ₂(x) = RZ₁(HS(x))`.
-/
noncomputable def StatePartition.elaboration {SZ1 IZ OZ S : Type}
    (Z1 : DiscreteSystem SZ1 IZ OZ) (e : StatePartition SZ1 S) (ch : ChoiceFunction S) :
    DiscreteSystem e.State IZ OZ where
  sz_nonempty :=
    have : Nonempty SZ1 := Z1.sz_nonempty
    ⟨e.rep (Classical.arbitrary SZ1)⟩
  NZ := fun s oi =>
    ⟨ch.pick (e.F (Z1.NZ (e.proj s) oi)),
      ⟨Z1.NZ (e.proj s) oi, ch.pick_mem _ (e.block_nonempty _)⟩⟩
  RZ := fun s => Z1.RZ (e.proj s)

/--
  [textbook/exercise4.72/proof/homomorphism]
  `Z₁ = HIMSY(Z₂, HS, ID(IZ₂), ID(OZ₂))`: the choice function always lands in the block named by
  the next state of `Z₁`, so `HS` intertwines the transitions.
-/
noncomputable def StatePartition.elaboration_witness {SZ1 IZ OZ S : Type}
    (Z1 : DiscreteSystem SZ1 IZ OZ) (e : StatePartition SZ1 S) (ch : ChoiceFunction S) :
    HomomorphicImageWitness Z1 (e.elaboration Z1 ch) where
  HS := e.proj
  HI := id
  HO := id
  HS_surjective := e.proj_surjective
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro s oi
    have hmem : ((e.elaboration Z1 ch).NZ s oi).1 ∈ e.F (Z1.NZ (e.proj s) oi) :=
      ch.pick_mem _ (e.block_nonempty _)
    simpa using e.proj_eq _ hmem
  preserves_readout := by intro s; simp [StatePartition.elaboration]

/--
  [textbook/exercise4.72/theorem/consistent_elaboration_states]
  Exercise 4.72: `Z₂ ∈ DSYSTEMS`, `#SZ₂ ≥ #SZ₁` (witnessed by the injection `rep`), and
  `Z₁ = HIMSY(Z₂, HS, HI, HO)`.
-/
theorem ex4_72_consistent_elaboration {SZ1 IZ OZ S : Type}
    (Z1 : DiscreteSystem SZ1 IZ OZ) (e : StatePartition SZ1 S) (ch : ChoiceFunction S) :
    Function.Injective e.rep ∧ IsHomomorphicImage Z1 (e.elaboration Z1 ch) :=
  ⟨e.rep_injective, ⟨e.elaboration_witness Z1 ch⟩⟩

/-! ## Exercise 4.74: consistent elaboration with respect to states, inputs and outputs -/

/--
  [textbook/exercise4.74/definition/elaboration_data]
  The data of Exercise 4.74: three functions onto the state, input and output sets of `Z₁`.
  Textbook `RNG(HS) = SZ₁` is modeled by surjectivity onto the fixed codomain `SZ₁`.
-/
structure ElaborationData {SZ1 IZ1 OZ1 : Type} (_Z1 : DiscreteSystem SZ1 IZ1 OZ1)
    (SZ2 IZ2 OZ2 : Type) where
  /-- [textbook/exercise4.74/component/HS] `RNG(HS) = SZ₁`, so `SZ₂ = DMN(HS)`. -/
  HS : SZ2 → SZ1
  /-- [textbook/exercise4.74/component/HI] `RNG(HI) = IZ₁`. -/
  HI : IZ2 → IZ1
  /-- [textbook/exercise4.74/component/HO] `RNG(HO) = OZ₁`. -/
  HO : OZ2 → OZ1
  HS_surjective : Function.Surjective HS
  HI_surjective : Function.Surjective HI
  HO_surjective : Function.Surjective HO

/--
  [textbook/exercise4.74/definition/system]
  `Z₂ = (DMN(HS), DMN(HI), DMN(HO), NZ₂, RZ₂)` where `NZ₂` and `RZ₂` choose preimages of the
  corresponding values of `Z₁`.
-/
noncomputable def ElaborationData.system {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2)
    (chS : ChoiceFunction SZ2) (chO : ChoiceFunction OZ2) :
    DiscreteSystem SZ2 IZ2 OZ2 where
  sz_nonempty :=
    have : Nonempty SZ1 := Z1.sz_nonempty
    ⟨chS.pick (d.HS ⁻¹' {Classical.arbitrary SZ1})⟩
  NZ := fun x oi => chS.pick (d.HS ⁻¹' {Z1.NZ (d.HS x) (oi.map d.HI)})
  RZ := fun x => (Z1.RZ (d.HS x)).map (fun o => chO.pick (d.HO ⁻¹' {o}))

/--
  [textbook/exercise4.74/proof/homomorphism]
  `Z₁ = HIMSY(Z₂, HS, HI, HO)`.
-/
noncomputable def ElaborationData.witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2)
    (chS : ChoiceFunction SZ2) (chO : ChoiceFunction OZ2) :
    HomomorphicImageWitness Z1 (d.system chS chO) where
  HS := d.HS
  HI := d.HI
  HO := d.HO
  HS_surjective := d.HS_surjective
  HI_surjective := d.HI_surjective
  HO_surjective := d.HO_surjective
  preserves_transition := by
    intro x oi
    exact chS.apply_pick_preimage d.HS_surjective _
  preserves_readout := by
    intro x
    show Option.map d.HO ((Z1.RZ (d.HS x)).map _) = Z1.RZ (d.HS x)
    rw [Option.map_map]
    have : d.HO ∘ (fun o => chO.pick (d.HO ⁻¹' {o})) = id :=
      funext fun o => chO.apply_pick_preimage d.HO_surjective o
    rw [this, Option.map_id]
    rfl

/-- `#SZ₂ ≥ #SZ₁`: choosing a preimage of each state of `Z₁` is injective. -/
theorem ElaborationData.state_section_injective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2) :
    Function.Injective (Function.surjInv d.HS_surjective) :=
  Function.injective_surjInv d.HS_surjective

/-- `#IZ₂ ≥ #IZ₁`. -/
theorem ElaborationData.input_section_injective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2) :
    Function.Injective (Function.surjInv d.HI_surjective) :=
  Function.injective_surjInv d.HI_surjective

/-- `#OZ₂ ≥ #OZ₁`. -/
theorem ElaborationData.output_section_injective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2) :
    Function.Injective (Function.surjInv d.HO_surjective) :=
  Function.injective_surjInv d.HO_surjective

/--
  [textbook/exercise4.74/theorem/consistent_elaboration]
  Exercise 4.74: `Z₂ ∈ DSYSTEMS`, `#SZ₂ ≥ #SZ₁`, `#IZ₂ ≥ #IZ₁`, `#OZ₂ ≥ #OZ₁` and
  `Z₁ = HIMSY(Z₂, HS, HI, HO)`.
-/
theorem ex4_74_consistent_elaboration {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} (d : ElaborationData Z1 SZ2 IZ2 OZ2)
    (chS : ChoiceFunction SZ2) (chO : ChoiceFunction OZ2) :
    Function.Injective (Function.surjInv d.HS_surjective) ∧
      Function.Injective (Function.surjInv d.HI_surjective) ∧
      Function.Injective (Function.surjInv d.HO_surjective) ∧
      IsHomomorphicImage Z1 (d.system chS chO) :=
  ⟨d.state_section_injective, d.input_section_injective, d.output_section_injective,
    ⟨d.witness chS chO⟩⟩

/-! ## Exercise 4.83: mutually homomorphic finite systems are isomorphic -/

/--
  [textbook/exercise4.83/proof/isomorphism_witness]
  If two finite systems are homomorphic images of each other, the first homomorphism is already an
  isomorphism.
-/
noncomputable def mutualHomomorphism_isomorphismWitness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (hfin : IsFinite Z2) (h1 : HomomorphicImageWitness Z1 Z2)
    (h2 : HomomorphicImageWitness Z2 Z1) : IsomorphismWitness Z1 Z2 :=
  have _hS : Finite SZ2 := hfin.1
  have _hI : Finite IZ2 := hfin.2.1
  have _hO : Finite OZ2 := hfin.2.2
  { toHomomorphicImageWitness := h1
    HS_injective :=
      (Finite.injective_iff_surjective.mpr (h2.HS_surjective.comp h1.HS_surjective)).of_comp
    HI_injective :=
      (Finite.injective_iff_surjective.mpr (h2.HI_surjective.comp h1.HI_surjective)).of_comp
    HO_injective :=
      (Finite.injective_iff_surjective.mpr (h2.HO_surjective.comp h1.HO_surjective)).of_comp }

/--
  [textbook/exercise4.83/theorem/mutual_homomorphism_isomorphic]
  Exercise 4.83: if two finite systems are each a homomorphic image of the other, they are
  isomorphic.
-/
theorem ex4_83_mutual_homomorphism_isomorphic {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (_hfin1 : IsFinite Z1) (hfin2 : IsFinite Z2)
    (h1 : IsHomomorphicImage Z1 Z2) (h2 : IsHomomorphicImage Z2 Z1) :
    IsIsomorphicTo Z1 Z2 :=
  ⟨mutualHomomorphism_isomorphismWitness hfin2 h1.some h2.some⟩

end Homomorphism
