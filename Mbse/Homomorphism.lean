import Mbse.Wymore

/-!
# Chapter 4: System Homomorphisms

**Naming convention (textbook ↔ Lean):**

| Textbook | Lean |
|---|---|
| Z₁ homomorphic *image* (simpler) | `Z_img` / first argument of `IsHomomorphicImage` |
| Z₂ *elaboration* (more complex) | `Z_elab` / second argument |
| HS : SZ₂ → ONTO(SZ₁) | `IsHomomorphicImage.HS` |
| HI : IZ₂ → ONTO(IZ₁) | `IsHomomorphicImage.HI` |
| HO : OZ₂ → ONTO(OZ₁) | `IsHomomorphicImage.HO` |

Lean `SystemMorphism Z₁ Z₂` uses φS : SZ₁ → SZ₂ (first system → second).
Textbook HS maps elaboration → image. A `SystemMorphism Z_elab Z_img` with surjective
φS, φI, φO yields `IsHomomorphicImage Z_img Z_elab` via `homomorphicImage_of_morphism`.

**RNG encoding:** textbook `SZ₁ = RNG(HS)` is modeled by fixing codomain type `SZ₁` and
requiring `Surjective HS`; the declared type is the homomorphic image state space.

Tags: [textbook/definition4.3], [textbook/definition4.10], [textbook/theorem4.8],
[textbook/theorem4.13], [textbook/theorem4.15].
-/

namespace Homomorphism

/-! ## Definition 4.3: Homomorphic image -/

/--
  [textbook/definition4.3/definition/homomorphic_image]
  Z₁ is a homomorphic image of Z₂ with respect to HS, HI, HO (textbook notation).
  Here `Z_img` is Z₁ and `Z_elab` is Z₂.
-/
structure HomomorphicImageWitness
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_img : DiscreteSystem SZ1 IZ1 OZ1)
    (Z_elab : DiscreteSystem SZ2 IZ2 OZ2) where
  /-- [textbook/definition4.3/component/state_homomorphism] HS : SZ₂ → ONTO(SZ₁). -/
  HS : SZ2 → SZ1
  /-- [textbook/definition4.3/component/input_homomorphism] HI : IZ₂ → ONTO(IZ₁). -/
  HI : IZ2 → IZ1
  /-- [textbook/definition4.3/component/output_homomorphism] HO : OZ₂ → ONTO(OZ₁). -/
  HO : OZ2 → OZ1
  HS_surjective : Function.Surjective HS
  HI_surjective : Function.Surjective HI
  HO_surjective : Function.Surjective HO
  /-- [textbook/definition4.3/requirement/next_state_consistency] Condition (iv). -/
  preserves_transition :
    ∀ x oi, HS (Z_elab.NZ x oi) = Z_img.NZ (HS x) (oi.map HI)
  /-- [textbook/definition4.3/requirement/readout_consistency] Condition (v). -/
  preserves_readout : ∀ x, (Z_elab.RZ x).map HO = Z_img.RZ (HS x)

/--
  [textbook/definition4.3/definition/homomorphic_image]
  Prop-level packaging: a homomorphic image witness exists.
-/
def IsHomomorphicImage {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_img : DiscreteSystem SZ1 IZ1 OZ1) (Z_elab : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  Nonempty (HomomorphicImageWitness Z_img Z_elab)

theorem homomorphicImage_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) (s0 : SZ2) (f : ITZW IZ2) :
    ∀ t, h.HS (generateStateTrajectory Z_elab s0 f t) =
         generateStateTrajectory Z_img (h.HS s0) (fun τ => (f τ).map h.HI) t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ]
    rw [h.preserves_transition, ih]

theorem homomorphicImage_preserves_output_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) (s0 : SZ2) (f : ITZW IZ2) :
    ∀ t, (generateOutputTrajectory Z_elab s0 f t).map h.HO =
         generateOutputTrajectory Z_img (h.HS s0) (fun τ => (f τ).map h.HI) t := by
  intro t
  have hst := homomorphicImage_preserves_state_trajectory h s0 f t
  unfold generateOutputTrajectory
  rw [h.preserves_readout, hst]

/--
  [textbook/definition4.3/implication/functional_capability]
  Elaboration trajectories project to image trajectories (functional capability).
-/
theorem homomorphic_image_functional_capability
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    h.HS (generateStateTrajectory Z_elab s0 f t) =
      generateStateTrajectory Z_img (h.HS s0) (fun τ => (f τ).map h.HI) t :=
  homomorphicImage_preserves_state_trajectory h s0 f t

/--
  [textbook/definition4.3/implication/consistent_simplification]
  Image-side output trajectories are obtained by projecting elaboration trajectories through HO.
-/
theorem homomorphic_image_consistent_simplification
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    (generateOutputTrajectory Z_elab s0 f t).map h.HO =
      generateOutputTrajectory Z_img (h.HS s0) (fun τ => (f τ).map h.HI) t :=
  homomorphicImage_preserves_output_trajectory h s0 f t

/-! ## Definition 4.10: HIMSY well-definedness and construction -/

/--
  [textbook/definition4.10/definition/himsy]
  Side conditions ensuring NZ₁ and RZ₁ are well-defined on equivalence classes of preimages.
-/
def HimsyWellDefined {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) : Prop :=
  ∀ x1 x2 oi1 oi2, HS x1 = HS x2 → oi1.map HI = oi2.map HI →
    HS (Z2.NZ x1 oi1) = HS (Z2.NZ x2 oi2) ∧
    (Z2.RZ x1).map HO = (Z2.RZ x2).map HO

theorem himsyWellDefined_of_homomorphicImage
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) :
    HimsyWellDefined Z_elab h.HS h.HI h.HO := by
  intro x1 x2 oi1 oi2 hS hI
  constructor
  · calc
      h.HS (Z_elab.NZ x1 oi1) = Z_img.NZ (h.HS x1) (oi1.map h.HI) := h.preserves_transition x1 oi1
      _ = Z_img.NZ (h.HS x2) (oi2.map h.HI) := by rw [hS, hI]
      _ = h.HS (Z_elab.NZ x2 oi2) := (h.preserves_transition x2 oi2).symm
  · rw [h.preserves_readout x1, h.preserves_readout x2, hS]

private theorem himsy_nz_well_defined {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (s : SZ1) (oi : Option IZ1) (x1 x2 : SZ2) (oi1 oi2 : Option IZ2)
    (hx1 : HS x1 = s) (hx2 : HS x2 = s) (hp1 : oi1.map HI = oi) (hp2 : oi2.map HI = oi) :
    HS (Z2.NZ x1 oi1) = HS (Z2.NZ x2 oi2) :=
  hwd x1 x2 oi1 oi2 (hx1.trans hx2.symm) (hp1.trans hp2.symm) |>.1

private theorem himsy_rz_well_defined {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [Inhabited IZ2]
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (x1 x2 : SZ2) (hx : HS x1 = HS x2) :
    (Z2.RZ x1).map HO = (Z2.RZ x2).map HO :=
  (hwd x1 x2 (some default) (some default) hx (by simp)).2

/--
  [textbook/definition4.10/definition/himsy]
  [textbook/definition4.10/component/sz1]
  [textbook/definition4.10/component/iz1]
  [textbook/definition4.10/component/oz1]
  [textbook/definition4.10/component/nz1]
  [textbook/definition4.10/component/rz1]
  Construct Z₁ = HIMSY(Z₂, HS, HI, HO). State, input, and output spaces are the
  codomains SZ₁, IZ₁, OZ₁ of the homomorphisms (RNG = codomain when HS, HI, HO onto).
-/
noncomputable def himsy {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (hS : Function.Surjective HS) (hI : Function.Surjective HI) (_hO : Function.Surjective HO) :
    DiscreteSystem SZ1 IZ1 OZ1 where
  sz_nonempty := ⟨HS (Classical.choice Z2.sz_nonempty)⟩
  NZ := fun s oi =>
    HS (Z2.NZ (Classical.choose (hS s)) (oi.map (fun i => Classical.choose (hI i))))
  RZ := fun s => (Z2.RZ (Classical.choose (hS s))).map HO

private theorem himsy_nz_independent {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (hS : Function.Surjective HS) (hI : Function.Surjective HI)
    (s : SZ1) (oi : Option IZ1) (x : SZ2) (oi2 : Option IZ2)
    (hx : HS x = s) (hp : oi2.map HI = oi) :
    HS (Z2.NZ (Classical.choose (hS s)) (oi.map (fun i => Classical.choose (hI i)))) =
      HS (Z2.NZ x oi2) := by
  have hx' : HS (Classical.choose (hS s)) = s := Classical.choose_spec (hS s)
  have hmap : (oi.map (fun i => Classical.choose (hI i))).map HI = oi := by
    ext i'
    simp only [Option.map_map]
    cases oi with
    | none => simp
    | some i =>
      simp [Classical.choose_spec (hI i)]
  exact himsy_nz_well_defined Z2 HS HI HO hwd s oi (Classical.choose (hS s)) x
    (oi.map (fun i => Classical.choose (hI i))) oi2 hx' hx hmap hp

private theorem himsy_rz_independent {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [Inhabited IZ2]
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (hS : Function.Surjective HS) (s : SZ1) (x : SZ2) (hx : HS x = s) :
    (Z2.RZ (Classical.choose (hS s))).map HO = (Z2.RZ x).map HO := by
  have hx' : HS (Classical.choose (hS s)) = s := Classical.choose_spec (hS s)
  exact himsy_rz_well_defined Z2 HS HI HO hwd (Classical.choose (hS s)) x (by rw [hx', hx])

/-! ## Theorem 4.15: Fundamental theorem (forward) -/

/--
  [textbook/theorem4.15/proof/forward]
  If Z₁ is a homomorphic image of Z₂, then Z₁ equals HIMSY(Z₂, HS, HI, HO) on transitions and readouts.
-/
theorem homomorphic_image_eq_himsy {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [Inhabited IZ2]
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) :
    (∀ s oi, Z_img.NZ s oi = (himsy Z_elab h.HS h.HI h.HO
      (himsyWellDefined_of_homomorphicImage h) h.HS_surjective h.HI_surjective h.HO_surjective).NZ s oi) ∧
    (∀ s, Z_img.RZ s = (himsy Z_elab h.HS h.HI h.HO
      (himsyWellDefined_of_homomorphicImage h) h.HS_surjective h.HI_surjective h.HO_surjective).RZ s) := by
  constructor
  · intro s oi
    dsimp [himsy]
    have hx : h.HS (Classical.choose (h.HS_surjective s)) = s :=
      Classical.choose_spec (h.HS_surjective s)
    match oi with
    | none =>
      calc
        Z_img.NZ s none = Z_img.NZ (h.HS (Classical.choose (h.HS_surjective s))) none := by rw [hx]
        _ = h.HS (Z_elab.NZ (Classical.choose (h.HS_surjective s)) none) :=
          (h.preserves_transition (Classical.choose (h.HS_surjective s)) none).symm
        _ = (himsy Z_elab h.HS h.HI h.HO (himsyWellDefined_of_homomorphicImage h)
            h.HS_surjective h.HI_surjective h.HO_surjective).NZ s none := rfl
    | some i =>
      have hpre : h.HI (Classical.choose (h.HI_surjective i)) = i :=
        Classical.choose_spec (h.HI_surjective i)
      have hoi : (some (Classical.choose (h.HI_surjective i))).map h.HI = some i := by simp [hpre]
      calc
        Z_img.NZ s (some i) = Z_img.NZ (h.HS (Classical.choose (h.HS_surjective s))) (some i) := by rw [hx]
        _ = Z_img.NZ (h.HS (Classical.choose (h.HS_surjective s)))
            ((some (Classical.choose (h.HI_surjective i))).map h.HI) := by rw [hoi]
        _ = h.HS (Z_elab.NZ (Classical.choose (h.HS_surjective s))
            (some (Classical.choose (h.HI_surjective i)))) :=
          (h.preserves_transition (Classical.choose (h.HS_surjective s))
            (some (Classical.choose (h.HI_surjective i)))).symm
        _ = (himsy Z_elab h.HS h.HI h.HO (himsyWellDefined_of_homomorphicImage h)
            h.HS_surjective h.HI_surjective h.HO_surjective).NZ s (some i) := rfl
  · intro s
    dsimp [himsy]
    have hx : h.HS (Classical.choose (h.HS_surjective s)) = s :=
      Classical.choose_spec (h.HS_surjective s)
    calc
      Z_img.RZ s = Z_img.RZ (h.HS (Classical.choose (h.HS_surjective s))) := by rw [hx]
      _ = (Z_elab.RZ (Classical.choose (h.HS_surjective s))).map h.HO := (h.preserves_readout _).symm
      _ = (himsy Z_elab h.HS h.HI h.HO (himsyWellDefined_of_homomorphicImage h)
          h.HS_surjective h.HI_surjective h.HO_surjective).RZ s := rfl

/--
  [textbook/theorem4.15/theorem/fundamental_iff]
  Fundamental theorem: homomorphic image ↔ HIMSY equality on NZ/RZ.
-/
theorem fundamental_theorem_homomorphism_iff {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [Inhabited IZ2]
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_img Z_elab) :
    (∀ s oi, Z_img.NZ s oi = (himsy Z_elab h.HS h.HI h.HO
      (himsyWellDefined_of_homomorphicImage h) h.HS_surjective h.HI_surjective h.HO_surjective).NZ s oi) ∧
    (∀ s, Z_img.RZ s = (himsy Z_elab h.HS h.HI h.HO
      (himsyWellDefined_of_homomorphicImage h) h.HS_surjective h.HI_surjective h.HO_surjective).RZ s) :=
  homomorphic_image_eq_himsy h

/--
  [textbook/theorem4.15/proof/reverse]
  If Z₁ = HIMSY(Z₂, HS, HI, HO), then Z₁ is a homomorphic image of Z₂.
-/
theorem himsy_is_homomorphic_image {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [Inhabited IZ2]
    (Z2 : DiscreteSystem SZ2 IZ2 OZ2) (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hwd : HimsyWellDefined Z2 HS HI HO)
    (hS : Function.Surjective HS) (hI : Function.Surjective HI) (hO : Function.Surjective HO) :
    IsHomomorphicImage (himsy Z2 HS HI HO hwd hS hI hO) Z2 :=
  ⟨{
    HS := HS
    HI := HI
    HO := HO
    HS_surjective := hS
    HI_surjective := hI
    HO_surjective := hO
    preserves_transition := fun x oi => by
      dsimp [himsy]
      exact (himsy_nz_independent Z2 HS HI HO hwd hS hI (HS x) (oi.map HI) x oi rfl rfl).symm
    preserves_readout := fun x => by
      dsimp [himsy]
      exact (himsy_rz_independent Z2 HS HI HO hwd hS (HS x) x rfl).symm
  }⟩

/-! ## Theorem 4.8: CSY component is homomorphic image -/

/-- [textbook/theorem4.8/proof/state_homomorphism] HS = PJN on conjunctive state. -/
def csy_state_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n) :
    ((j : Fin n) → VSCR.SZ j) → VSCR.SZ i :=
  _root_.PJN i

/-- [textbook/theorem4.8/proof/input_homomorphism] HI = PJN on conjunctive input ports. -/
def csy_input_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n) :
    ((ip : Σ j, VSCR.Port j) → VSCR.PortVal ip.1 ip.2) →
    ((p : VSCR.Port i) → VSCR.PortVal i p) :=
  fun po p => po ⟨i, p⟩

/-- [textbook/theorem4.8/proof/output_homomorphism] HO = PJN on conjunctive output ports. -/
def csy_output_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n) :
    ((op : Σ j, VSCR.OutPort j) → VSCR.OutPortVal op.1 op.2) →
    ((p : VSCR.OutPort i) → VSCR.OutPortVal i p) :=
  fun ro op => ro ⟨i, op⟩

noncomputable def csy_fill_state {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (s : VSCR.SZ i) : (j : Fin n) → VSCR.SZ j :=
  fun j => if h : j = i then h ▸ s else Classical.choice (VSCR.Z j).sz_nonempty

theorem csy_fill_state_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (s : VSCR.SZ i) : csy_state_proj VSCR i (csy_fill_state VSCR i s) = s := by
  simp [csy_state_proj, csy_fill_state, _root_.PJN]

noncomputable def csy_fill_input {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (hPort : ∀ j (p : VSCR.Port j), Nonempty (VSCR.PortVal j p))
    (ci : (p : VSCR.Port i) → VSCR.PortVal i p) :
    ((ip : Σ j, VSCR.Port j) → VSCR.PortVal ip.1 ip.2) :=
  fun ⟨j, p⟩ =>
    if h : j = i then by subst h; exact ci p
    else Classical.choice (hPort j p)

theorem csy_fill_input_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (hPort : ∀ j (p : VSCR.Port j), Nonempty (VSCR.PortVal j p))
    (ci : (p : VSCR.Port i) → VSCR.PortVal i p) :
    csy_input_proj VSCR i (csy_fill_input VSCR i hPort ci) = ci := by
  funext p
  simp [csy_input_proj, csy_fill_input]

noncomputable def csy_fill_output {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (hOut : ∀ j (p : VSCR.OutPort j), Nonempty (VSCR.OutPortVal j p))
    (co : (p : VSCR.OutPort i) → VSCR.OutPortVal i p) :
    ((op : Σ j, VSCR.OutPort j) → VSCR.OutPortVal op.1 op.2) :=
  fun ⟨j, p⟩ =>
    if h : j = i then by subst h; exact co p
    else Classical.choice (hOut j p)

theorem csy_fill_output_proj {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (hOut : ∀ j (p : VSCR.OutPort j), Nonempty (VSCR.OutPortVal j p))
    (co : (p : VSCR.OutPort i) → VSCR.OutPortVal i p) :
    csy_output_proj VSCR i (csy_fill_output VSCR i hOut co) = co := by
  funext p
  simp [csy_output_proj, csy_fill_output]

theorem csy_input_map_eq {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (oi : Option ((ip : Σ j, VSCR.Port j) → VSCR.PortVal ip.1 ip.2)) :
    Option.map (fun full port => full ⟨i, port⟩) oi =
      Option.map (csy_input_proj VSCR i) oi := by
  cases oi <;> rfl

private theorem csyOut_at_component {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ j, AlwaysOutputs (VSCR.Z j)) (x : (j : Fin n) → VSCR.SZ j) (i : Fin n)
    (op : VSCR.OutPort i) :
    csyOut VSCR hOut x ⟨i, op⟩ = Classical.choose (hOut i (x i)) op := rfl

/--
  [textbook/theorem4.8/theorem/csy_component_homomorphic]
  [textbook/theorem4.8/proof/next_state_consistency]
  [textbook/theorem4.8/proof/readout_consistency]
  Component Zᵢ is a homomorphic image of CSY(VSCR).
-/
theorem csy_component_homomorphic_image {n : Nat} (VSCR : PortSystemVector n)
    (hAlways : ∀ j, AlwaysOutputs (VSCR.Z j))
    (hPort : ∀ j (p : VSCR.Port j), Nonempty (VSCR.PortVal j p))
    (hOutVal : ∀ j (p : VSCR.OutPort j), Nonempty (VSCR.OutPortVal j p)) (i : Fin n) :
    IsHomomorphicImage (VSCR.Z i) (csy VSCR hAlways) :=
  ⟨{
    HS := csy_state_proj VSCR i
    HI := csy_input_proj VSCR i
    HO := csy_output_proj VSCR i
    HS_surjective := fun s =>
      ⟨csy_fill_state VSCR i s, csy_fill_state_proj VSCR i s⟩
    HI_surjective := fun ci =>
      ⟨csy_fill_input VSCR i hPort ci, csy_fill_input_proj VSCR i hPort ci⟩
    HO_surjective := fun co =>
      ⟨csy_fill_output VSCR i hOutVal co, csy_fill_output_proj VSCR i hOutVal co⟩
    preserves_transition := fun x oi => by
      simp only [csy_state_proj, csy, _root_.PJN, csy_input_map_eq]
    preserves_readout := fun x => by
      obtain ⟨o, ho⟩ := hAlways i (x i)
      show (some (fun op => csyOut VSCR hAlways x op)).map (csy_output_proj VSCR i) =
        (VSCR.Z i).RZ (x i)
      simp only [Option.map_some, csy_output_proj, csy_state_proj, _root_.PJN]
      rw [ho]
      apply Option.some_inj.mpr
      have hfn : Classical.choose (hAlways i (x i)) = o :=
        Option.some_injective _ ((Classical.choose_spec (hAlways i (x i))).symm.trans ho)
      funext op
      dsimp [csyOut]
      exact congrArg (fun f => f op) hfn
  }⟩

/--
  Corollary packaging `Nonempty` port-value witnesses (e.g. Unit ports in the swarm).
-/
theorem csy_component_homomorphic_image_unit {n : Nat}
    (VSCR : PortSystemVector n) (i : Fin n)
    (hAlways : ∀ j, AlwaysOutputs (VSCR.Z j))
    (hPort : ∀ j (p : VSCR.Port j), Nonempty (VSCR.PortVal j p))
    (hOutVal : ∀ j (p : VSCR.OutPort j), Nonempty (VSCR.OutPortVal j p)) :
    IsHomomorphicImage (VSCR.Z i) (csy VSCR hAlways) :=
  csy_component_homomorphic_image VSCR hAlways hPort hOutVal i

/-! ## Theorem 4.13: HIMSY parameterization -/

/--
  [textbook/theorem4.13/theorem/himsy_parameterization]
  Bundled parameters for HIMSY: elaboration system plus homomorphisms and side conditions.
-/
structure HimsyParam (SZ1 IZ1 OZ1 : Type) where
  SZ2 : Type
  IZ2 : Type
  OZ2 : Type
  Z2 : DiscreteSystem SZ2 IZ2 OZ2
  HS : SZ2 → SZ1
  HI : IZ2 → IZ1
  HO : OZ2 → OZ1
  well_defined : HimsyWellDefined Z2 HS HI HO
  HS_surj : Function.Surjective HS
  HI_surj : Function.Surjective HI
  HO_surj : Function.Surjective HO

/--
  [textbook/theorem4.13/theorem/himsy_parameterization]
  HIMSY is a system parameterization.
-/
noncomputable def himsy_parameterization (SZ1 : Type) (IZ1 : Type) (OZ1 : Type) :
    DiscreteSystemParameterization (HimsyParam SZ1 IZ1 OZ1)
      (fun _ => SZ1) (fun _ => IZ1) (fun _ => OZ1) :=
  fun p => himsy p.Z2 p.HS p.HI p.HO p.well_defined p.HS_surj p.HI_surj p.HO_surj

/-! ## Link to SystemMorphism (direction convention) -/

/--
  A surjective `SystemMorphism Z_elab Z_img` yields textbook homomorphic image Z_img of Z_elab.
-/
theorem homomorphicImage_of_morphism
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_img : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z_elab Z_img) (hS : Function.Surjective m.φS)
    (hI : Function.Surjective m.φI) (hO : Function.Surjective m.φO) :
    IsHomomorphicImage Z_img Z_elab :=
  ⟨{
    HS := m.φS
    HI := m.φI
    HO := m.φO
    HS_surjective := hS
    HI_surjective := hI
    HO_surjective := hO
    preserves_transition := fun x oi => m.preserves_transition x oi
    preserves_readout := fun x => m.preserves_readout x
  }⟩

end Homomorphism

export Homomorphism (HomomorphicImageWitness IsHomomorphicImage himsy HimsyWellDefined
  homomorphic_image_eq_himsy himsy_is_homomorphic_image csy_component_homomorphic_image
  himsy_parameterization homomorphicImage_preserves_state_trajectory
  homomorphicImage_preserves_output_trajectory homomorphicImage_of_morphism)