import Mbse.Homomorphism

/-!
# Chapter 4: homomorphism algebra, isomorphisms and copies

Builds on `Mbse.Homomorphism` (Def 4.3 / Def 4.10):

* Theorem 4.31 — the homomorphic-image relation is reflexive and transitive.
* Definition 4.33 / 4.35 — system isomorphisms and their parameterization `ISY`.
* Theorem 4.38 / Exercise 4.82 — `ISY` is reflexive, symmetric and transitive.
* Definition 4.27 — port-preserving homomorphisms (`SHIS` / `SHOS`).
* Exercise 4.80 / 4.81 — the parameterization `HIMPPSY` and its reflexivity/transitivity.
* Definition 4.47 / 4.53 and Exercise 4.84 — copies (`COPY`) form an equivalence.

**Port encoding.** Textbook `#IPZ₂ = #IPZ₁` is modeled by sharing the port index type, so
`IZ = (p : Port) → PortVal p`. Clause (ii) of Def 4.27 (`PJN(IZ₁,i) ∘ HI = HIᵢ ∘ PJN(IZ₂,i)`)
then says exactly that `HI` acts coordinatewise through surjections `HIᵢ`.
-/

namespace Homomorphism

universe u

/-! ## Theorem 4.31: the homomorphic-image relation is reflexive and transitive -/

/--
  [textbook/theorem4.31/proof/reflexive]
  `Z = HIMSY(Z, ID(SZ), ID(IZ), ID(OZ))`.
-/
def HomomorphicImageWitness.refl {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    HomomorphicImageWitness Z Z where
  HS := id
  HI := id
  HO := id
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by intro x oi; simp
  preserves_readout := by intro x; simp

/--
  [textbook/theorem4.31/proof/transitive]
  Composing homomorphisms: `Z1 = HIMSY(Z3, HS1 ∘ HS2, HI1 ∘ HI2, HO1 ∘ HO2)`.
-/
def HomomorphicImageWitness.comp {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : HomomorphicImageWitness Z1 Z2) (h23 : HomomorphicImageWitness Z2 Z3) :
    HomomorphicImageWitness Z1 Z3 where
  HS := h12.HS ∘ h23.HS
  HI := h12.HI ∘ h23.HI
  HO := h12.HO ∘ h23.HO
  HS_surjective := h12.HS_surjective.comp h23.HS_surjective
  HI_surjective := h12.HI_surjective.comp h23.HI_surjective
  HO_surjective := h12.HO_surjective.comp h23.HO_surjective
  preserves_transition := by
    intro x oi
    simp only [Function.comp_apply]
    rw [h23.preserves_transition, h12.preserves_transition, Option.map_map]
  preserves_readout := by
    intro x
    simp only [Function.comp_apply, ← Option.map_map]
    rw [h23.preserves_readout, h12.preserves_readout]

/--
  [textbook/theorem4.31/theorem/homomorphism_reflexive_transitive]
  Theorem 4.31: the homomorphic-image relation is reflexive and transitive.
-/
theorem isHomomorphicImage_refl {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    IsHomomorphicImage Z Z :=
  ⟨HomomorphicImageWitness.refl Z⟩

/--
  [textbook/theorem4.31/theorem/homomorphism_reflexive_transitive]
  Transitivity half of Theorem 4.31.
-/
theorem isHomomorphicImage_trans {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : IsHomomorphicImage Z1 Z2) (h23 : IsHomomorphicImage Z2 Z3) :
    IsHomomorphicImage Z1 Z3 :=
  ⟨h12.some.comp h23.some⟩

/-! ## Theorem 4.22: experiments on a system determine experiments on its homomorphic images -/

/--
  [textbook/theorem4.22/definition/experiment_image]
  The image of an experiment `(f, x, t) ∈ EXZ₂` under a homomorphism: `(HI ∘ f, HS(x), t) ∈ EXZ₁`.
-/
def HomomorphicImageWitness.expImage {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z1 Z2) (e : EXZ SZ2 IZ2) : EXZ SZ1 IZ1 :=
  ((fun τ => (e.1 τ).map h.HI), h.HS e.2.1, e.2.2)

/--
  [textbook/theorem4.22/theorem/state_value]
  `HS(STZ₂(f, x)(t)) = STZ₁(HI ∘ f, HS(x))(t)`.
-/
theorem homomorphism_experiment_state_value {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z1 Z2) (f : ITZW IZ2) (x : SZ2) (t : Time) :
    h.HS (generateStateTrajectory Z2 x f t) =
      generateStateTrajectory Z1 (h.HS x) (fun τ => (f τ).map h.HI) t :=
  homomorphicImage_preserves_state_trajectory h x f t

/--
  [textbook/theorem4.22/theorem/state_trajectory]
  `HS ∘ STZ₂(f, x) = STZ₁(HI ∘ f, HS(x))` as functions of time.
-/
theorem homomorphism_experiment_state_trajectory {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z1 Z2) (f : ITZW IZ2) (x : SZ2) :
    h.HS ∘ generateStateTrajectory Z2 x f =
      generateStateTrajectory Z1 (h.HS x) (fun τ => (f τ).map h.HI) :=
  funext fun t => homomorphicImage_preserves_state_trajectory h x f t

/--
  [textbook/theorem4.22/theorem/output_trajectory]
  `HO ∘ OTZ₂(f, x) = OTZ₁(HI ∘ f, HS(x))` as functions of time.
-/
theorem homomorphism_experiment_output_trajectory {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z1 Z2) (f : ITZW IZ2) (x : SZ2) :
    (fun t => (generateOutputTrajectory Z2 x f t).map h.HO) =
      generateOutputTrajectory Z1 (h.HS x) (fun τ => (f τ).map h.HI) :=
  funext fun t => homomorphicImage_preserves_output_trajectory h x f t

/--
  [textbook/theorem4.22/theorem/experiments_transfer]
  Theorem 4.22: an experiment on `Z₂` determines an experiment on the homomorphic image `Z₁`,
  and state and output trajectories transfer through `HS` and `HO`.
-/
theorem homomorphism_experiments_transfer {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z1 Z2) (e : EXZ SZ2 IZ2) :
    (h.expImage e).1 = (fun τ => (e.1 τ).map h.HI) ∧
      (h.expImage e).2.1 = h.HS e.2.1 ∧
      (h.expImage e).2.2 = e.2.2 ∧
      h.HS ∘ generateStateTrajectory Z2 e.2.1 e.1 =
        generateStateTrajectory Z1 (h.HS e.2.1) (fun τ => (e.1 τ).map h.HI) ∧
      (fun t => (generateOutputTrajectory Z2 e.2.1 e.1 t).map h.HO) =
        generateOutputTrajectory Z1 (h.HS e.2.1) (fun τ => (e.1 τ).map h.HI) :=
  ⟨rfl, rfl, rfl,
    homomorphism_experiment_state_trajectory h e.1 e.2.1,
    homomorphism_experiment_output_trajectory h e.1 e.2.1⟩

/-! ## Definition 4.33 / 4.35: system isomorphisms and `ISY` -/

/--
  [textbook/definition4.33/definition/system_isomorphism]
  `Z1` is isomorphic to `Z2` with respect to `HS`, `HI`, `HO` when it is a homomorphic image
  and each of the three maps is `1TO1`.
-/
structure IsomorphismWitness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2)
    extends HomomorphicImageWitness Z1 Z2 where
  /-- [textbook/definition4.33/requirement/state_injective] `HS` is `1TO1`. -/
  HS_injective : Function.Injective toHomomorphicImageWitness.HS
  /-- [textbook/definition4.33/requirement/input_injective] `HI` is `1TO1`. -/
  HI_injective : Function.Injective toHomomorphicImageWitness.HI
  /-- [textbook/definition4.33/requirement/output_injective] `HO` is `1TO1`. -/
  HO_injective : Function.Injective toHomomorphicImageWitness.HO

/--
  [textbook/definition4.35/definition/isy]
  `ISY`: `Z1` is an isomorph of `Z2` when an isomorphism witness exists.
-/
def IsIsomorphicTo {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z1 : DiscreteSystem SZ1 IZ1 OZ1) (Z2 : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  Nonempty (IsomorphismWitness Z1 Z2)

theorem IsomorphismWitness.HS_bijective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsomorphismWitness Z1 Z2) : Function.Bijective h.HS :=
  ⟨h.HS_injective, h.HS_surjective⟩

theorem IsomorphismWitness.HI_bijective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsomorphismWitness Z1 Z2) : Function.Bijective h.HI :=
  ⟨h.HI_injective, h.HI_surjective⟩

theorem IsomorphismWitness.HO_bijective {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsomorphismWitness Z1 Z2) : Function.Bijective h.HO :=
  ⟨h.HO_injective, h.HO_surjective⟩

/-! ## Theorem 4.38 / Exercise 4.82: `ISY` is reflexive, symmetric and transitive -/

/-- Reflexivity: identity maps are bijective. -/
def IsomorphismWitness.refl {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    IsomorphismWitness Z Z where
  toHomomorphicImageWitness := HomomorphicImageWitness.refl Z
  HS_injective := Function.injective_id
  HI_injective := Function.injective_id
  HO_injective := Function.injective_id

/-- Transitivity: composites of bijections are bijections. -/
def IsomorphismWitness.comp {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : IsomorphismWitness Z1 Z2) (h23 : IsomorphismWitness Z2 Z3) :
    IsomorphismWitness Z1 Z3 where
  toHomomorphicImageWitness := h12.toHomomorphicImageWitness.comp h23.toHomomorphicImageWitness
  HS_injective := h12.HS_injective.comp h23.HS_injective
  HI_injective := h12.HI_injective.comp h23.HI_injective
  HO_injective := h12.HO_injective.comp h23.HO_injective

/--
  [textbook/theorem4.38/proof/inverse_isomorphism]
  The inverse maps `HS⁻¹`, `HI⁻¹`, `HO⁻¹` witness `Z2 = ISY(Z1, HS⁻¹, HI⁻¹, HO⁻¹)`.
-/
noncomputable def IsomorphismWitness.symm {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsomorphismWitness Z1 Z2) : IsomorphismWitness Z2 Z1 :=
  let eS := Equiv.ofBijective h.HS h.HS_bijective
  let eI := Equiv.ofBijective h.HI h.HI_bijective
  let eO := Equiv.ofBijective h.HO h.HO_bijective
  have hS : ∀ z, h.HS (eS.symm z) = z := fun z => eS.apply_symm_apply z
  have hI : ∀ z, h.HI (eI.symm z) = z := fun z => eI.apply_symm_apply z
  have hO : ∀ z, eO.symm (h.HO z) = z := fun z => eO.symm_apply_apply z
  have hIm : ∀ o : Option IZ1, Option.map h.HI (Option.map eI.symm o) = o := by
    intro o; cases o with
    | none => rfl
    | some a => simp only [Option.map_some, hI]
  have hOm : ∀ o : Option OZ2, Option.map eO.symm (Option.map h.HO o) = o := by
    intro o; cases o with
    | none => rfl
    | some a => simp only [Option.map_some, hO]
  { HS := eS.symm
    HI := eI.symm
    HO := eO.symm
    HS_surjective := eS.symm.surjective
    HI_surjective := eI.symm.surjective
    HO_surjective := eO.symm.surjective
    HS_injective := eS.symm.injective
    HI_injective := eI.symm.injective
    HO_injective := eO.symm.injective
    preserves_transition := by
      intro y oj
      refine h.HS_injective ?_
      rw [hS, h.preserves_transition, hS, hIm]
    preserves_readout := by
      intro y
      have hkey := h.preserves_readout (eS.symm y)
      rw [hS] at hkey
      calc Option.map eO.symm (Z1.RZ y)
          _ = Option.map eO.symm (Option.map h.HO (Z2.RZ (eS.symm y))) := by rw [hkey]
          _ = Z2.RZ (eS.symm y) := hOm _ }

/--
  [textbook/exercise4.82/theorem/isomorphism_reflexive]
  Exercise 4.82 (i): system isomorphism is reflexive.
-/
theorem isIsomorphicTo_refl {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    IsIsomorphicTo Z Z :=
  ⟨IsomorphismWitness.refl Z⟩

/--
  [textbook/exercise4.82/theorem/isomorphism_transitive]
  Exercise 4.82 (ii): system isomorphism is transitive.
-/
theorem isIsomorphicTo_trans {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 SZ3 IZ3 OZ3 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    {Z3 : DiscreteSystem SZ3 IZ3 OZ3}
    (h12 : IsIsomorphicTo Z1 Z2) (h23 : IsIsomorphicTo Z2 Z3) :
    IsIsomorphicTo Z1 Z3 :=
  ⟨h12.some.comp h23.some⟩

/--
  [textbook/theorem4.38/theorem/isomorphism_symmetric]
  [textbook/exercise4.82/theorem/isomorphism_symmetric]
  Theorem 4.38 / Exercise 4.82 (iii): `Z1 = ISY(Z2, …)` iff `Z2 = ISY(Z1, …⁻¹)`.
-/
theorem isIsomorphicTo_symm {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsIsomorphicTo Z1 Z2) : IsIsomorphicTo Z2 Z1 :=
  ⟨h.some.symm⟩

/--
  [textbook/theorem4.38/theorem/isomorphism_symmetric]
  The symmetric form of Theorem 4.38 as a bi-implication.
-/
theorem isIsomorphicTo_comm {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2} :
    IsIsomorphicTo Z1 Z2 ↔ IsIsomorphicTo Z2 Z1 :=
  ⟨isIsomorphicTo_symm, isIsomorphicTo_symm⟩

/-- Isomorphs are in particular homomorphic images. -/
theorem IsIsomorphicTo.isHomomorphicImage {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1} {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsIsomorphicTo Z1 Z2) : IsHomomorphicImage Z1 Z2 :=
  ⟨h.some.toHomomorphicImageWitness⟩

/-! ## Definition 4.27: port-preserving homomorphisms -/

/--
  [textbook/definition4.27/definition/preserves_ports]
  `H` preserves ports with respect to the family `port` (textbook `SHIS` / `SHOS`): the port index
  types agree (clause (i)) and `PJN(·, i) ∘ H = Hᵢ ∘ PJN(·, i)` (clause (ii)), i.e. `H` acts
  coordinatewise through surjections.
-/
structure PreservesPorts {Port : Type} {Val2 Val1 : Port → Type}
    (H : ((p : Port) → Val2 p) → ((p : Port) → Val1 p)) where
  /-- [textbook/definition4.27/component/port_family] The family `SHIS = {Hᵢ}`. -/
  port : (p : Port) → Val2 p → Val1 p
  /-- Each `Hᵢ` is `ONTO`. -/
  port_surjective : ∀ p, Function.Surjective (port p)
  /-- Clause (ii): `PJN(·, i) ∘ H = Hᵢ ∘ PJN(·, i)`. -/
  proj : ∀ f p, H f p = port p (f p)

/-- The identity preserves ports coordinatewise. -/
def PreservesPorts.id {Port : Type} {Val : Port → Type} :
    PreservesPorts (id : ((p : Port) → Val p) → ((p : Port) → Val p)) where
  port := fun _ => _root_.id
  port_surjective := fun _ => Function.surjective_id
  proj := fun _ _ => rfl

/-- Port preservation is closed under composition. -/
def PreservesPorts.comp {Port : Type} {Val1 Val2 Val3 : Port → Type}
    {H12 : ((p : Port) → Val2 p) → ((p : Port) → Val1 p)}
    {H23 : ((p : Port) → Val3 p) → ((p : Port) → Val2 p)}
    (h12 : PreservesPorts H12) (h23 : PreservesPorts H23) :
    PreservesPorts (H12 ∘ H23) where
  port := fun p => h12.port p ∘ h23.port p
  port_surjective := fun p => (h12.port_surjective p).comp (h23.port_surjective p)
  proj := fun f p => by
    simp only [Function.comp_apply]
    rw [h12.proj, h23.proj]

/--
  [textbook/theorem4.45/theorem/port_maps_bijective]
  Theorem 4.45: in a port-preserving *isomorphism* the port maps are themselves `1TO1` (and
  `ONTO`), so corresponding ports are equivalent sets. Injectivity of the product map transfers to
  each factor once every port carries a value.
-/
theorem PreservesPorts.port_injective {Port : Type} {Val2 Val1 : Port → Type}
    [∀ p, Nonempty (Val2 p)]
    {H : ((p : Port) → Val2 p) → ((p : Port) → Val1 p)}
    (hp : PreservesPorts H) (hinj : Function.Injective H) (p : Port) :
    Function.Injective (hp.port p) := by
  classical
  intro a b hab
  set base : (q : Port) → Val2 q := fun q => Classical.arbitrary (Val2 q) with hbase
  have hupd : Function.update base p a = Function.update base p b := by
    refine hinj ?_
    funext q
    rw [hp.proj, hp.proj]
    by_cases hq : q = p
    · subst hq; simpa using hab
    · simp [Function.update_of_ne hq]
  simpa using congr_fun hupd p

theorem PreservesPorts.port_bijective {Port : Type} {Val2 Val1 : Port → Type}
    [∀ p, Nonempty (Val2 p)]
    {H : ((p : Port) → Val2 p) → ((p : Port) → Val1 p)}
    (hp : PreservesPorts H) (hinj : Function.Injective H) (p : Port) :
    Function.Bijective (hp.port p) :=
  ⟨hp.port_injective hinj p, hp.port_surjective p⟩

/-- The inverse of a port-preserving bijection is again port-preserving. -/
noncomputable def PreservesPorts.symm {Port : Type} {Val2 Val1 : Port → Type}
    [∀ p, Nonempty (Val2 p)]
    {H : ((p : Port) → Val2 p) → ((p : Port) → Val1 p)}
    (hp : PreservesPorts H) (hbij : Function.Bijective H) :
    PreservesPorts (Equiv.ofBijective H hbij).symm :=
  let e := Equiv.ofBijective H hbij
  let ep := fun p => Equiv.ofBijective (hp.port p) (hp.port_bijective hbij.1 p)
  { port := fun p => (ep p).symm
    port_surjective := fun p => (ep p).symm.surjective
    proj := by
      intro g p
      have hH : H (fun q => (ep q).symm (g q)) = g := by
        funext q
        rw [hp.proj]
        exact (ep q).apply_symm_apply (g q)
      have : e.symm g = fun q => (ep q).symm (g q) := by
        refine hbij.1 ?_
        rw [hH]
        exact e.apply_symm_apply g
      rw [this] }

/-! ## Exercise 4.80 / 4.81: `HIMPPSY`, the port-preserving homomorphic image parameterization -/

/--
  [textbook/exercise4.80/definition/himppsy]
  A port-preserving homomorphic image witness: a Def 4.3 homomorphism whose input and output
  homomorphisms preserve ports in the sense of Def 4.27.
-/
structure PortPreservingHomWitness {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q))
    (Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q))
    extends HomomorphicImageWitness Z1 Z2 where
  /-- [textbook/exercise4.80/requirement/preserves_input_ports] `HI` preserves input ports. -/
  inPorts : PreservesPorts toHomomorphicImageWitness.HI
  /-- [textbook/exercise4.80/requirement/preserves_output_ports] `HO` preserves output ports. -/
  outPorts : PreservesPorts toHomomorphicImageWitness.HO

/--
  [textbook/exercise4.80/definition/himppsy]
  `HIMPPSY`: `Z1` is a port-preserving homomorphic image of `Z2`.
-/
def IsPortPreservingHomImage {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q))
    (Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)) : Prop :=
  Nonempty (PortPreservingHomWitness Z1 Z2)

/-- `HIMPPSY` refines `HIMSY`: it really is a system parameterization. -/
theorem IsPortPreservingHomImage.isHomomorphicImage {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    (h : IsPortPreservingHomImage Z1 Z2) : IsHomomorphicImage Z1 Z2 :=
  ⟨h.some.toHomomorphicImageWitness⟩

/--
  [textbook/exercise4.81/proof/reflexive]
  `HIMPPSY` is reflexive: identities preserve every port.
-/
def PortPreservingHomWitness.refl {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :
    PortPreservingHomWitness Z Z where
  toHomomorphicImageWitness := HomomorphicImageWitness.refl Z
  inPorts := PreservesPorts.id
  outPorts := PreservesPorts.id

/--
  [textbook/exercise4.81/proof/transitive]
  `HIMPPSY` is transitive: coordinatewise maps compose coordinatewise.
-/
def PortPreservingHomWitness.comp {SZ1 SZ2 SZ3 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 PortVal3 : Port → Type}
    {OutPortVal1 OutPortVal2 OutPortVal3 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port) → PortVal3 p) ((q : OutPort) → OutPortVal3 q)}
    (h12 : PortPreservingHomWitness Z1 Z2) (h23 : PortPreservingHomWitness Z2 Z3) :
    PortPreservingHomWitness Z1 Z3 where
  toHomomorphicImageWitness := h12.toHomomorphicImageWitness.comp h23.toHomomorphicImageWitness
  inPorts := h12.inPorts.comp h23.inPorts
  outPorts := h12.outPorts.comp h23.outPorts

/--
  [textbook/exercise4.81/theorem/himppsy_reflexive_transitive]
  Exercise 4.81: `HIMPPSY` is reflexive and transitive.
-/
theorem isPortPreservingHomImage_refl {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :
    IsPortPreservingHomImage Z Z :=
  ⟨PortPreservingHomWitness.refl Z⟩

/--
  [textbook/exercise4.81/theorem/himppsy_reflexive_transitive]
  Transitivity half of Exercise 4.81.
-/
theorem isPortPreservingHomImage_trans {SZ1 SZ2 SZ3 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 PortVal3 : Port → Type}
    {OutPortVal1 OutPortVal2 OutPortVal3 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port) → PortVal3 p) ((q : OutPort) → OutPortVal3 q)}
    (h12 : IsPortPreservingHomImage Z1 Z2) (h23 : IsPortPreservingHomImage Z2 Z3) :
    IsPortPreservingHomImage Z1 Z3 :=
  ⟨h12.some.comp h23.some⟩

/-! ## Definition 4.47 / 4.53 and Exercise 4.84: copies (`COPY`) -/

/--
  [textbook/definition4.47/definition/copy]
  `Z1` is a copy of `Z2` when it is isomorphic to `Z2` and the input/output isomorphisms preserve
  ports with respect to `SHIS` / `SHOS`.
-/
structure CopyWitness {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q))
    (Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q))
    extends IsomorphismWitness Z1 Z2 where
  /-- [textbook/definition4.47/requirement/preserves_input_ports] `HI` preserves input ports. -/
  inPorts : PreservesPorts toIsomorphismWitness.HI
  /-- [textbook/definition4.47/requirement/preserves_output_ports] `HO` preserves output ports. -/
  outPorts : PreservesPorts toIsomorphismWitness.HO

/--
  [textbook/definition4.53/definition/copy]
  `COPY`: `Z1` is a copy of `Z2` when a copy witness exists.
-/
def IsCopyOf {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    (Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q))
    (Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)) : Prop :=
  Nonempty (CopyWitness Z1 Z2)

/-- Copies are isomorphs. -/
theorem IsCopyOf.isIsomorphicTo {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    (h : IsCopyOf Z1 Z2) : IsIsomorphicTo Z1 Z2 :=
  ⟨h.some.toIsomorphismWitness⟩

/-- [textbook/exercise4.84/proof/reflexive] Reflexivity of the copy relation. -/
def CopyWitness.refl {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :
    CopyWitness Z Z where
  toIsomorphismWitness := IsomorphismWitness.refl Z
  inPorts := PreservesPorts.id
  outPorts := PreservesPorts.id

/-- [textbook/exercise4.84/proof/transitive] Transitivity of the copy relation. -/
def CopyWitness.comp {SZ1 SZ2 SZ3 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 PortVal3 : Port → Type}
    {OutPortVal1 OutPortVal2 OutPortVal3 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port) → PortVal3 p) ((q : OutPort) → OutPortVal3 q)}
    (h12 : CopyWitness Z1 Z2) (h23 : CopyWitness Z2 Z3) : CopyWitness Z1 Z3 where
  toIsomorphismWitness := h12.toIsomorphismWitness.comp h23.toIsomorphismWitness
  inPorts := h12.inPorts.comp h23.inPorts
  outPorts := h12.outPorts.comp h23.outPorts

/--
  [textbook/exercise4.84/proof/symmetric]
  Symmetry of the copy relation: by Theorem 4.45 each port map is bijective, so the inverse
  isomorphism is again port-preserving.
-/
noncomputable def CopyWitness.symm {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    [∀ p, Nonempty (PortVal2 p)] [∀ q, Nonempty (OutPortVal2 q)]
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    (h : CopyWitness Z1 Z2) : CopyWitness Z2 Z1 where
  toIsomorphismWitness := h.toIsomorphismWitness.symm
  inPorts := h.inPorts.symm h.HI_bijective
  outPorts := h.outPorts.symm h.HO_bijective

/--
  [textbook/exercise4.84/theorem/copy_reflexive]
  Exercise 4.84: the copy relation is reflexive.
-/
theorem isCopyOf_refl {SZ : Type} {Port OutPort : Type}
    {PortVal : Port → Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((q : OutPort) → OutPortVal q)) :
    IsCopyOf Z Z :=
  ⟨CopyWitness.refl Z⟩

/--
  [textbook/exercise4.84/theorem/copy_transitive]
  Exercise 4.84: the copy relation is transitive.
-/
theorem isCopyOf_trans {SZ1 SZ2 SZ3 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 PortVal3 : Port → Type}
    {OutPortVal1 OutPortVal2 OutPortVal3 : OutPort → Type}
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    {Z3 : DiscreteSystem SZ3 ((p : Port) → PortVal3 p) ((q : OutPort) → OutPortVal3 q)}
    (h12 : IsCopyOf Z1 Z2) (h23 : IsCopyOf Z2 Z3) : IsCopyOf Z1 Z3 :=
  ⟨h12.some.comp h23.some⟩

/--
  [textbook/exercise4.84/theorem/copy_symmetric]
  Exercise 4.84: the copy relation is symmetric.
-/
theorem isCopyOf_symm {SZ1 SZ2 : Type} {Port OutPort : Type}
    {PortVal1 PortVal2 : Port → Type} {OutPortVal1 OutPortVal2 : OutPort → Type}
    [∀ p, Nonempty (PortVal2 p)] [∀ q, Nonempty (OutPortVal2 q)]
    {Z1 : DiscreteSystem SZ1 ((p : Port) → PortVal1 p) ((q : OutPort) → OutPortVal1 q)}
    {Z2 : DiscreteSystem SZ2 ((p : Port) → PortVal2 p) ((q : OutPort) → OutPortVal2 q)}
    (h : IsCopyOf Z1 Z2) : IsCopyOf Z2 Z1 :=
  ⟨h.some.symm⟩

end Homomorphism
