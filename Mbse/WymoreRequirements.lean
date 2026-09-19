import Mbse.Wymore
import Mbse.Homomorphism
import Mbse.IsomorphismConstructions
import Mbse.WymoreSystemModes

/-!
# Wymore Chapter 6: input/output requirements

Typed reconstruction of IOR, satisfaction (RSN reading of §6.33), functionality
cotyledon FSR, default/normal parameterizations, subrequirements, HIMIO, and TSY.
-/

namespace WymoreRequirements

open Classical
open Homomorphism
open WymoreSystemModes

universe u

/-! ## Operational length and time scale (artifacts of Def 6.5) -/

/--
  Operational life requirement: finite positive length or infinite (`IJS++`).
-/
inductive OperationalLength where
  | finite (n : Nat) (hn : 0 < n)
  | infinite
  deriving DecidableEq, Repr

/-- Time scale `TSR = IJS[0, OLR)` or all of `Time` when infinite. -/
def timeScale : OperationalLength → Set Time
  | .finite n _ => {t | t < n}
  | .infinite => Set.univ

theorem timeScale_nonempty (olr : OperationalLength) : (timeScale olr).Nonempty := by
  cases olr with
  | finite n hn => exact ⟨0, hn⟩
  | infinite => exact ⟨0, trivial⟩

/-! ## Definition 6.5: input/output requirement -/

/--
  [textbook/definition6.5/source/definition]
  [textbook/definition6.5/lean/InputOutputRequirement]
  [textbook/definition6.5/lean/OperationalLength]
  Input/output requirement `IOR = (OLR, IR, ITR, OR, OTR, ER)`.

  Trajectories are total `ITZ` maps; finite `TSR` is handled by RSN agreement
  (Def 6.33 / §2.49). Eligibility covers `OTR` (`OTR = ⋃ RNG(ER)`).
-/
structure InputOutputRequirement (IR OR : Type) where
  olr : OperationalLength
  itr : Set (ITZ IR)
  otr : Set (ITZ OR)
  er : ITZ IR → Set (ITZ OR)
  itr_nonempty : itr.Nonempty
  otr_nonempty : otr.Nonempty
  er_subset : ∀ {f}, f ∈ itr → er f ⊆ otr
  er_nonempty : ∀ {f}, f ∈ itr → (er f).Nonempty
  otr_from_er : ∀ {g}, g ∈ otr → ∃ f ∈ itr, g ∈ er f

abbrev TSR (IOR : InputOutputRequirement IR OR) : Set Time :=
  timeScale IOR.olr

/-- Restrict a total trajectory to a time set (pointwise agreement predicate). -/
def agreesOn {A : Type} (f g : Time → A) (T : Set Time) : Prop :=
  ∀ t ∈ T, f t = g t

theorem agreesOn_univ {A : Type} (f g : Time → A) :
    agreesOn f g Set.univ ↔ f = g := by
  constructor
  · intro h; funext t; exact h t trivial
  · intro h t _; exact congrFun h t

theorem agreesOn_subset {A : Type} {f g : Time → A} {T U : Set Time}
    (hTU : T ⊆ U) (h : agreesOn f g U) : agreesOn f g T :=
  fun t ht => h t (hTU ht)

/-! ## Definition 6.31 / 6.33: satisfaction -/

/--
  [textbook/definition6.31/source/definition]
  [textbook/definition6.31/lean/SatisfiesIOR]
  System `Z` satisfies `IOR` w.r.t. initial state `DSZ` and timescale `TSZ`.

  Clause (v) uses the RSN wording of §6.33: for every eligible input scenario
  `f ∈ ITR` and every total extension `h` agreeing with `f` on `TSR`, some
  eligible output `g ∈ ER(f)` matches the system output on `TSZ`.
-/
def SatisfiesIOR {S : Type} {IR OR : Type}
    (Z : DiscreteSystem S IR OR) (IOR : InputOutputRequirement IR OR)
    (DSZ : S) (TSZ : Set Time) : Prop :=
  TSZ.Nonempty ∧
  TSZ ⊆ TSR IOR ∧
  ∀ f ∈ IOR.itr,
    ∀ h : ITZ IR, agreesOn h f (TSR IOR) →
      ∃ g ∈ IOR.er f,
        ∀ t ∈ TSZ, generateOutputTrajectory Z DSZ (liftInput h) t = some (g t)

/--
  [textbook/definition6.36/source/definition]
  [textbook/definition6.36/lean/SatisfiesIORCompletely]
  Complete satisfaction: `TSZ = TSR`.
-/
def SatisfiesIORCompletely {S : Type} {IR OR : Type}
    (Z : DiscreteSystem S IR OR) (IOR : InputOutputRequirement IR OR)
    (DSZ : S) : Prop :=
  SatisfiesIOR Z IOR DSZ (TSR IOR)

/-! ## Definitions 6.40 / 6.42: functional system design and FSR -/

/--
  [textbook/definition6.40/source/definition]
  [textbook/definition6.40/lean/FunctionalSystemDesign]
  A functional system design for `IOR`.
-/
structure FunctionalSystemDesign {IR OR : Type} (IOR : InputOutputRequirement IR OR) where
  S : Type
  Z : DiscreteSystem S IR OR
  DSZ : S
  TSZ : Set Time
  satisfies : SatisfiesIOR Z IOR DSZ TSZ

/--
  [textbook/definition6.42/source/definition]
  [textbook/definition6.42/lean/FSR]
  [textbook/definition6.42/lean/CTL]
  Functionality cotyledon / space of functional system designs.
-/
abbrev FSR {IR OR : Type} (IOR : InputOutputRequirement IR OR) :=
  FunctionalSystemDesign IOR

abbrev CTL {IR OR : Type} (IOR : InputOutputRequirement IR OR) :=
  FSR IOR

/-- Exercise 6.101: nonempty subscales remain satisfying. -/
theorem satisfies_of_ts_subset {S : Type} {IR OR : Type}
    {Z : DiscreteSystem S IR OR} {IOR : InputOutputRequirement IR OR}
    {DSZ : S} {TSZ T : Set Time}
    (h : SatisfiesIOR Z IOR DSZ TSZ) (hT : T.Nonempty) (hsub : T ⊆ TSZ) :
    SatisfiesIOR Z IOR DSZ T := by
  obtain ⟨hne, hscale, helig⟩ := h
  refine ⟨hT, hsub.trans hscale, ?_⟩
  intro f hf h' hh
  obtain ⟨g, hg, hmatch⟩ := helig f hf h' hh
  exact ⟨g, hg, fun t ht => hmatch t (hsub ht)⟩

/--
  [textbook/exercise6.101/source/exercise]
  [textbook/exercise6.101/plan/fsr_closed_under_ts_subset]
  FSR is closed under nonempty subsets of the time subscale.
-/
def fsr_closed_under_ts_subset {IR OR : Type} {IOR : InputOutputRequirement IR OR}
    (fsd : FSR IOR) {T : Set Time} (hT : T.Nonempty) (hsub : T ⊆ fsd.TSZ) :
    FSR IOR where
  S := fsd.S
  Z := fsd.Z
  DSZ := fsd.DSZ
  TSZ := T
  satisfies := satisfies_of_ts_subset fsd.satisfies hT hsub

/-! ## Definition 6.10: IOR parameterization -/

/--
  [textbook/definition6.10/source/definition]
  [textbook/definition6.10/lean/IOSpecParameterization]
  Any function whose range is a subset of IOSPECS (typed as producing IORs).
-/
abbrev IOSpecParameterization (P : Type u) (IR OR : P → Type) : Type u :=
  (r : P) → InputOutputRequirement (IR r) (OR r)

/-! ## Definition 6.14: DFLTIO -/

/--
  [textbook/definition6.14/source/definition]
  [textbook/definition6.14/lean/dfltIO]
  Default IOR: infinite horizon, all input/output trajectories eligible.
-/
def dfltIO (A B : Type) [Nonempty A] [Nonempty B] : InputOutputRequirement A B where
  olr := .infinite
  itr := Set.univ
  otr := Set.univ
  er := fun _ => Set.univ
  itr_nonempty := ⟨fun _ => Classical.arbitrary A, Set.mem_univ _⟩
  otr_nonempty := ⟨fun _ => Classical.arbitrary B, Set.mem_univ _⟩
  er_subset := fun {_} _ => Set.subset_univ _
  er_nonempty := fun {_} _ => ⟨fun _ => Classical.arbitrary B, Set.mem_univ _⟩
  otr_from_er := fun {_} _ =>
    ⟨fun _ => Classical.arbitrary A, Set.mem_univ _, Set.mem_univ _⟩

/-- Unwrap an always-present readout to a total output. -/
noncomputable def totalOutputOf {S I O : Type} (Z : DiscreteSystem S I O)
    (hOut : AlwaysOutputs Z) (x : S) (f : ITZW I) : ITZ O :=
  fun t => Classical.choose (hOut (generateStateTrajectory Z x f t))

theorem totalOutputOf_spec {S I O : Type} (Z : DiscreteSystem S I O)
    (hOut : AlwaysOutputs Z) (x : S) (f : ITZW I) (t : Time) :
    generateOutputTrajectory Z x f t = some (totalOutputOf Z hOut x f t) :=
  Classical.choose_spec (hOut (generateStateTrajectory Z x f t))

/-- Any system with matching I/O alphabets satisfies the default IOR on any nonempty timescale. -/
theorem dfltIO_satisfies {S A B : Type} [Nonempty A] [Nonempty B]
    (Z : DiscreteSystem S A B) (x : S) (T : Set Time) (hT : T.Nonempty)
    (hOut : AlwaysOutputs Z) :
    SatisfiesIOR Z (dfltIO A B) x T := by
  refine ⟨hT, Set.subset_univ T, ?_⟩
  intro f _ h _hh
  refine ⟨totalOutputOf Z hOut x (liftInput h), Set.mem_univ _, ?_⟩
  intro t _ht
  exact totalOutputOf_spec Z hOut x (liftInput h) t

/--
  [textbook/theorem6.47/source/theorem]
  [textbook/theorem6.47/lean/dfltIO_fsr]
  Partial: packages one design into `FSR`. Full timescale characterization is
  `dfltIO_fsr_satisfies_iff` (requires `AlwaysOutputs`).
-/
theorem dfltIO_fsr {S A B : Type} [Nonempty A] [Nonempty B]
    (Z : DiscreteSystem S A B) (x : S) (T : Set Time) (hT : T.Nonempty)
    (hOut : AlwaysOutputs Z) :
    Nonempty (FSR (dfltIO A B)) :=
  ⟨{ S := S, Z := Z, DSZ := x, TSZ := T,
      satisfies := dfltIO_satisfies Z x T hT hOut }⟩

/--
  [textbook/theorem6.47/lean/dfltIO_fsr_satisfies_iff]
  Characterization: under `AlwaysOutputs`, satisfaction of `DFLTIO` is exactly
  nonempty timescale (I/O alphabets match by typing).
-/
theorem dfltIO_fsr_satisfies_iff {S A B : Type} [Nonempty A] [Nonempty B]
    (Z : DiscreteSystem S A B) (x : S) (T : Set Time) (hOut : AlwaysOutputs Z) :
    SatisfiesIOR Z (dfltIO A B) x T ↔ T.Nonempty := by
  constructor
  · exact fun h => h.1
  · intro hT; exact dfltIO_satisfies Z x T hT hOut

/-! ## Definition 6.17: NORMIO (single-system form) -/

/--
  Parameters for the singleton form `NORMIO(Z, x, L, F)`.
-/
structure NormIOParam where
  {S I O : Type}
  Z : DiscreteSystem S I O
  x : S
  olr : OperationalLength
  F : Set (ITZ I)
  F_nonempty : F.Nonempty
  hOut : AlwaysOutputs Z

/-- Output trajectories produced by `Z` from `x` on inputs in `F`. -/
noncomputable def normIO_otr (p : NormIOParam) : Set (ITZ p.O) :=
  {g | ∃ f ∈ p.F,
    ∀ t ∈ timeScale p.olr,
      generateOutputTrajectory p.Z p.x (liftInput f) t = some (g t)}

/--
  [textbook/definition6.17/source/definition]
  [textbook/definition6.17/lean/normIO]
  Normal IOR from a single system (ER typo corrected: eligible outputs are
  those produced by `Z` from `ST(Z)`).
-/
noncomputable def normIO (p : NormIOParam) : InputOutputRequirement p.I p.O where
  olr := p.olr
  itr := p.F
  otr := normIO_otr p
  er := fun f =>
    if hf : f ∈ p.F then
      {g | ∀ t ∈ timeScale p.olr,
        generateOutputTrajectory p.Z p.x (liftInput f) t = some (g t)}
    else
      ∅
  itr_nonempty := p.F_nonempty
  otr_nonempty := by
    obtain ⟨f, hf⟩ := p.F_nonempty
    refine ⟨fun t => Classical.choose (p.hOut (generateStateTrajectory p.Z p.x (liftInput f) t)), ?_⟩
    refine ⟨f, hf, ?_⟩
    intro t ht
    exact Classical.choose_spec
      (p.hOut (generateStateTrajectory p.Z p.x (liftInput f) t))
  er_subset := by
    intro f hf g hg
    simp only [dif_pos hf] at hg
    exact ⟨f, hf, hg⟩
  er_nonempty := by
    intro f hf
    simp only [dif_pos hf]
    refine ⟨fun t => Classical.choose (p.hOut (generateStateTrajectory p.Z p.x (liftInput f) t)), ?_⟩
    intro t ht
    exact Classical.choose_spec
      (p.hOut (generateStateTrajectory p.Z p.x (liftInput f) t))
  otr_from_er := by
    intro g hg
    obtain ⟨f, hf, hmatch⟩ := hg
    refine ⟨f, hf, ?_⟩
    simp only [dif_pos hf]
    exact hmatch

/--
  [textbook/theorem6.48/source/theorem]
  [textbook/theorem6.48/lean/normIO_members_in_fsr]
  `Z` is in FSR of `NORMIO(Z,x,L,F)` for any nonempty `T ⊆ TSR`.
-/
theorem agreesOn_liftInput {I : Type} {f h : ITZ I} {T : Set Time}
    (hh : agreesOn h f T) {t : Time} (ht : ∀ u < t, u ∈ T) :
    RSN (liftInput h) {i | i < t} = RSN (liftInput f) {i | i < t} := by
  apply (rsn_eq_iff _ _ _).2
  intro u hu
  exact congrArg some (hh u (ht u hu))

theorem timeScale_downward (olr : OperationalLength) {t u : Time}
    (ht : t ∈ timeScale olr) (hu : u < t) : u ∈ timeScale olr := by
  cases olr with
  | finite n hn => exact Nat.lt_trans hu ht
  | infinite => trivial

theorem normIO_members_in_fsr (p : NormIOParam) {T : Set Time}
    (hT : T.Nonempty) (hsub : T ⊆ timeScale p.olr) :
    SatisfiesIOR p.Z (normIO p) p.x T := by
  refine ⟨hT, hsub, ?_⟩
  intro f hf h hh
  have hfF : f ∈ p.F := hf
  let g := totalOutputOf p.Z p.hOut p.x (liftInput f)
  refine ⟨g, ?_, ?_⟩
  · change g ∈ (if hf : f ∈ p.F then
        {g | ∀ t ∈ timeScale p.olr,
          generateOutputTrajectory p.Z p.x (liftInput f) t = some (g t)}
      else ∅)
    rw [dif_pos hfF]
    intro t ht
    exact totalOutputOf_spec p.Z p.hOut p.x (liftInput f) t
  · intro t ht
    have htraj :
        generateOutputTrajectory p.Z p.x (liftInput h) t =
          generateOutputTrajectory p.Z p.x (liftInput f) t := by
      apply outputTrajectory_nonanticipatory
      exact agreesOn_liftInput hh fun u hu =>
        timeScale_downward p.olr (hsub ht) hu
    rw [htraj]
    exact totalOutputOf_spec p.Z p.hOut p.x (liftInput f) t

/--
  [textbook/exercise6.99/source/exercise]
  [textbook/exercise6.99/plan/normIO_satisfies_completely]
  Systems in NORMIO satisfy completely w.r.t. `ST(Z)` and `TSR`.
-/
theorem normIO_satisfies_completely (p : NormIOParam) :
    SatisfiesIORCompletely p.Z (normIO p) p.x :=
  normIO_members_in_fsr p (timeScale_nonempty p.olr) (fun _ h => h)

/-! ## Definition 6.50: IOR subrequirement -/

/--
  [textbook/definition6.50/source/definition]
  [textbook/definition6.50/lean/IsIOSubrequirement]
  Input/output subrequirement (clause (ii) corrected: `IR1`, same alphabet types).
-/
def IsIOSubrequirement {IR OR : Type}
    (IOR1 IOR2 : InputOutputRequirement IR OR) : Prop :=
  TSR IOR1 ⊆ TSR IOR2 ∧
  (∀ f1 ∈ IOR1.itr, ∃ f2 ∈ IOR2.itr, agreesOn f1 f2 (TSR IOR1)) ∧
  (∀ g1 ∈ IOR1.otr, ∃ g2 ∈ IOR2.otr, agreesOn g1 g2 (TSR IOR1)) ∧
  (∀ f1 ∈ IOR1.itr, ∀ g1 ∈ IOR1.er f1,
    ∃ f2 ∈ IOR2.itr, agreesOn f1 f2 (TSR IOR1) ∧
      ∃ g2 ∈ IOR2.er f2, agreesOn g1 g2 (TSR IOR1))

/--
  [textbook/theorem6.51/source/theorem]
  [textbook/theorem6.51/lean/subrequirement_fsr_subset]
  Under equal `TSR`/`ITR` and pointwise `ER1 ⊆ ER2`, satisfaction lifts from the
  subrequirement to the superrequirement (book 6.51; also discharges 6.90).
-/
theorem subrequirement_fsr_subset {S IR OR : Type}
    {IOR1 IOR2 : InputOutputRequirement IR OR}
    {Z : DiscreteSystem S IR OR} {DSZ : S} {TSZ : Set Time}
    (hTSR : TSR IOR1 = TSR IOR2)
    (hITR : IOR1.itr = IOR2.itr)
    (hER : ∀ f ∈ IOR1.itr, IOR1.er f ⊆ IOR2.er f)
    (h : SatisfiesIOR Z IOR1 DSZ TSZ) :
    SatisfiesIOR Z IOR2 DSZ TSZ := by
  obtain ⟨hne, hscale, helig⟩ := h
  refine ⟨hne, hTSR ▸ hscale, ?_⟩
  intro f hf2 h' hh
  have hf1 : f ∈ IOR1.itr := hITR ▸ hf2
  obtain ⟨g, hg, hmatch⟩ := helig f hf1 h' (by simpa [hTSR] using hh)
  exact ⟨g, hER f hf1 hg, hmatch⟩

/-- When `TSR = univ`, `IsIOSubrequirement` + equal `ITR` yields pointwise `ER` inclusion. -/
theorem er_subset_of_subrequirement_univ {IR OR : Type}
    {IOR1 IOR2 : InputOutputRequirement IR OR}
    (hSub : IsIOSubrequirement IOR1 IOR2)
    (hTSR : TSR IOR1 = Set.univ)
    (_hITR : IOR1.itr = IOR2.itr) :
    ∀ f ∈ IOR1.itr, IOR1.er f ⊆ IOR2.er f := by
  intro f hf g hg
  obtain ⟨-, -, -, hER⟩ := hSub
  obtain ⟨f2, hf2, hAgrF, g2, hg2, hAgrG⟩ := hER f hf g hg
  have hf_eq : f2 = f := by
    funext t
    have ht : t ∈ TSR IOR1 := by simp [hTSR]
    exact (hAgrF t ht).symm
  have hg_eq : g2 = g := by
    funext t
    have ht : t ∈ TSR IOR1 := by simp [hTSR]
    exact (hAgrG t ht).symm
  simpa [hf_eq, hg_eq] using hg2

/-- Theorem 6.51 / Exercise 6.90 packaged from `IsIOSubrequirement` when `TSR = univ`. -/
theorem subrequirement_fsr_subset_of_IsIOSubrequirement {S IR OR : Type}
    {IOR1 IOR2 : InputOutputRequirement IR OR}
    {Z : DiscreteSystem S IR OR} {DSZ : S} {TSZ : Set Time}
    (hSub : IsIOSubrequirement IOR1 IOR2)
    (hTSR : TSR IOR1 = Set.univ)
    (hITR : IOR1.itr = IOR2.itr)
    (hEq : TSR IOR2 = Set.univ)
    (h : SatisfiesIOR Z IOR1 DSZ TSZ) :
    SatisfiesIOR Z IOR2 DSZ TSZ :=
  subrequirement_fsr_subset (hTSR.trans hEq.symm) hITR
    (er_subset_of_subrequirement_univ hSub hTSR hITR) h

/-- Map a trajectory through an alphabet map. -/
def mapTraj {A B : Type} (φ : A → B) (f : ITZ A) : ITZ B :=
  fun t => φ (f t)

/--
  [textbook/definition6.72/source/definition]
  [textbook/definition6.72/lean/IsHomomorphicIOR]
  Homomorphic image of an IOR (same operational length).
-/
structure IsHomomorphicIOR {IR1 OR1 IR2 OR2 : Type}
    (IOR1 : InputOutputRequirement IR1 OR1)
    (IOR2 : InputOutputRequirement IR2 OR2) where
  HI : IR2 → IR1
  HO : OR2 → OR1
  HI_surjective : Function.Surjective HI
  HO_surjective : Function.Surjective HO
  olr_eq : IOR1.olr = IOR2.olr
  itr_image : IOR1.itr = mapTraj HI '' IOR2.itr
  otr_image : IOR1.otr = mapTraj HO '' IOR2.otr
  er_commutes : ∀ f2 ∈ IOR2.itr,
    IOR1.er (mapTraj HI f2) = mapTraj HO '' (IOR2.er f2)

/--
  [textbook/definition6.72/lean/himio]
  Image IOR along `HI`, `HO` (pushforward of ITR/OTR/ER).
-/
noncomputable def himio {IR1 OR1 IR2 OR2 : Type}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (HI : IR2 → IR1) (HO : OR2 → OR1) :
    InputOutputRequirement IR1 OR1 where
  olr := IOR2.olr
  itr := mapTraj HI '' IOR2.itr
  otr := mapTraj HO '' IOR2.otr
  er := fun f1 =>
    {g1 | ∃ f2 ∈ IOR2.itr, mapTraj HI f2 = f1 ∧
      ∃ g2 ∈ IOR2.er f2, mapTraj HO g2 = g1}
  itr_nonempty := by
    obtain ⟨f2, hf2⟩ := IOR2.itr_nonempty
    exact ⟨mapTraj HI f2, f2, hf2, rfl⟩
  otr_nonempty := by
    obtain ⟨g2, hg2⟩ := IOR2.otr_nonempty
    exact ⟨mapTraj HO g2, g2, hg2, rfl⟩
  er_subset := by
    intro f1 hf1 g1 hg1
    obtain ⟨f2, hf2, -, g2, hg2, rfl⟩ := hg1
    exact ⟨g2, IOR2.er_subset hf2 hg2, rfl⟩
  er_nonempty := by
    intro f1 hf1
    obtain ⟨f2, hf2, rfl⟩ := hf1
    obtain ⟨g2, hg2⟩ := IOR2.er_nonempty hf2
    exact ⟨mapTraj HO g2, f2, hf2, rfl, g2, hg2, rfl⟩
  otr_from_er := by
    intro g1 hg1
    obtain ⟨g2, hg2, rfl⟩ := hg1
    obtain ⟨f2, hf2, hmem⟩ := IOR2.otr_from_er hg2
    exact ⟨mapTraj HI f2, ⟨f2, hf2, rfl⟩, f2, hf2, rfl, g2, hmem, rfl⟩

/-- Under injective `HI`, the HIMIO witness package is available (clause (vi)). -/
def himio_isHomomorphicIOR_of_injectiveHI {IR1 OR1 IR2 OR2 : Type}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (HI : IR2 → IR1) (HO : OR2 → OR1)
    (hHI : Function.Surjective HI) (hHO : Function.Surjective HO)
    (hInj : Function.Injective HI) :
    IsHomomorphicIOR (himio IOR2 HI HO) IOR2 where
  HI := HI
  HO := HO
  HI_surjective := hHI
  HO_surjective := hHO
  olr_eq := rfl
  itr_image := rfl
  otr_image := rfl
  er_commutes := by
    intro f2 hf2
    ext g1
    have hInjT : Function.Injective (mapTraj HI) := fun x y hxy =>
      funext fun t => hInj (congrFun hxy t)
    simp only [himio, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨f2', hf2', heq, g2, hg2, rfl⟩
      cases hInjT heq
      exact ⟨g2, hg2, rfl⟩
    · rintro ⟨g2, hg2, rfl⟩
      exact ⟨f2, hf2, rfl, g2, hg2, rfl⟩

/--
  [textbook/theorem6.58/source/theorem]
  [textbook/theorem6.58/lean/himsy_idIO_satisfies_iff]
  Corrected `Te` → same `T`: state-homomorphic image with identity I/O maps
  preserves IOR satisfaction.
-/
theorem himsy_idIO_satisfies_iff {S1 S2 IR OR : Type}
    {Z1 : DiscreteSystem S1 IR OR} {Z2 : DiscreteSystem S2 IR OR}
    (h : HomomorphicImageWitness Z1 Z2)
    (hHI : h.HI = id) (hHO : h.HO = id)
    (DSZ2 : S2) (T : Set Time) (IOR : InputOutputRequirement IR OR) :
    SatisfiesIOR Z2 IOR DSZ2 T ↔
      SatisfiesIOR Z1 IOR (h.HS DSZ2) T := by
  have hIO : ∀ (traj : ITZ IR) (t : Time),
      generateOutputTrajectory Z2 DSZ2 (liftInput traj) t =
        generateOutputTrajectory Z1 (h.HS DSZ2) (liftInput traj) t := by
    intro traj t
    have hmap := homomorphicImage_preserves_output_trajectory h DSZ2 (liftInput traj) t
    simp only [hHI, hHO, Option.map_id, id_eq, liftInput, Option.map_some] at hmap
    exact hmap
  constructor
  · intro hSat
    obtain ⟨hne, hscale, helig⟩ := hSat
    refine ⟨hne, hscale, fun f hf traj hAgr => ?_⟩
    obtain ⟨g, hg, hmatch⟩ := helig f hf traj hAgr
    exact ⟨g, hg, fun t ht => (hIO traj t).symm.trans (hmatch t ht)⟩
  · intro hSat
    obtain ⟨hne, hscale, helig⟩ := hSat
    refine ⟨hne, hscale, fun f hf traj hAgr => ?_⟩
    obtain ⟨g, hg, hmatch⟩ := helig f hf traj hAgr
    exact ⟨g, hg, fun t ht => (hIO traj t).trans (hmatch t ht)⟩

/--
  [textbook/exercise6.88/source/exercise]
  [textbook/exercise6.88/plan/himsy_satisfies_himio]
  Homomorphic image of a system that satisfies an IOR satisfies the HIMIO image IOR.
-/
theorem himsy_satisfies_himio {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (DSZ2 : S2) (TSZ : Set Time)
    (hSat : SatisfiesIOR Z2 IOR2 DSZ2 TSZ) :
    SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ := by
  obtain ⟨hne, hscale, helig⟩ := hSat
  refine ⟨hne, by simpa [himio, TSR, timeScale] using hscale, ?_⟩
  intro f1 hf1 traj1 hAgr
  obtain ⟨f2, hf2, rfl⟩ := hf1
  let traj2 : ITZ IR2 := fun t =>
    if t ∈ TSR IOR2 then f2 t
    else Classical.choose (w.HI_surjective (traj1 t))
  have hAgr2 : agreesOn traj2 f2 (TSR IOR2) := by
    intro t ht; simp [traj2, ht]
  obtain ⟨g2, hg2, hmatch⟩ := helig f2 hf2 traj2 hAgr2
  refine ⟨mapTraj w.HO g2, ⟨f2, hf2, rfl, g2, hg2, rfl⟩, ?_⟩
  intro t ht
  have htraj_eq : (fun τ => (liftInput traj2 τ).map w.HI) = liftInput traj1 := by
    funext τ
    simp only [liftInput, Option.map_some]
    by_cases hτ : τ ∈ TSR IOR2
    · have : traj1 τ = w.HI (f2 τ) :=
        hAgr τ (by simpa [himio, TSR, timeScale] using hτ)
      simp [traj2, hτ, this]
    · simp [traj2, hτ, Classical.choose_spec (w.HI_surjective (traj1 τ))]
  have hmap := homomorphicImage_preserves_output_trajectory w DSZ2 (liftInput traj2) t
  rw [htraj_eq] at hmap
  have hout := hmatch t ht
  rw [hout, Option.map_some] at hmap
  simpa [mapTraj] using hmap.symm

/-! ## Echo IOR counterexample (Exercises 6.93–6.94) -/

/--
  Echo IOR: every input trajectory is eligible only for itself as output.
  No Moore system can satisfy this with full `ITR` (readout at time 0 cannot
  track both `f(0)=false` and `f(0)=true`).
-/
noncomputable def echoIOR : InputOutputRequirement Bool Bool where
  olr := .infinite
  itr := Set.univ
  otr := Set.univ
  er := fun f => {f}
  itr_nonempty := ⟨fun _ => false, Set.mem_univ _⟩
  otr_nonempty := ⟨fun _ => false, Set.mem_univ _⟩
  er_subset := by
    intro f _ g hg
    simp only [Set.mem_singleton_iff] at hg
    subst hg; exact Set.mem_univ _
  er_nonempty := fun {_} _ => Set.singleton_nonempty _
  otr_from_er := fun {g} _ => ⟨g, Set.mem_univ _, Set.mem_singleton g⟩

theorem echoIOR_fsr_empty :
    ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S) (T : Set Time),
      SatisfiesIOR Z echoIOR x T := by
  intro ⟨S, Z, x, T, hSat⟩
  obtain ⟨⟨t0, ht0⟩, -, helig⟩ := hSat
  let f1 : ITZ Bool := fun _ => false
  let f2 : ITZ Bool := fun t => if t0 ≤ t then true else false
  have agr : agreesOn f1 f2 {u | u < t0} := by
    intro u hu
    have : ¬ t0 ≤ u := Nat.not_le_of_gt hu
    simp [f1, f2, this]
  obtain ⟨g1, hg1, h1⟩ := helig f1 (Set.mem_univ _) f1 (fun _ _ => rfl)
  obtain ⟨g2, hg2, h2⟩ := helig f2 (Set.mem_univ _) f2 (fun _ _ => rfl)
  simp only [echoIOR, Set.mem_singleton_iff] at hg1 hg2
  subst hg1; subst hg2
  have hEq :
      generateStateTrajectory Z x (liftInput f1) t0 =
        generateStateTrajectory Z x (liftInput f2) t0 := by
    apply stateTrajectory_nonanticipatory
    apply (rsn_eq_iff _ _ _).2
    intro u hu
    exact congrArg some (agr u hu)
  have o1 := h1 t0 ht0
  have o2 := h2 t0 ht0
  simp only [generateOutputTrajectory, f1, f2, Nat.le_refl, ↓reduceIte] at o1 o2
  rw [hEq] at o1
  rw [o1] at o2
  exact Bool.false_ne_true (Option.some_injective _ o2)

/--
  [textbook/exercise6.93/source/exercise]
  [textbook/exercise6.93/plan/full_itr_fsr_nonempty_claim]
  Counterexample: full ITR on `IJS++` need not yield nonempty FSR (`echoIOR`).
-/
theorem full_itr_fsr_nonempty_claim :
    (echoIOR.olr = .infinite ∧ echoIOR.itr = Set.univ) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S) (T : Set Time),
        SatisfiesIOR Z echoIOR x T :=
  ⟨⟨rfl, rfl⟩, echoIOR_fsr_empty⟩

/-! ## Incomplete-only IOR (Exercises 6.94–6.95) -/

/--
  Forced-true at time 0, then echo: Moore systems can satisfy on `{0}` (constant
  true readout) but cannot satisfy on any timescale containing a positive time
  (nonanticipation vs free `f(t)`), hence no complete satisfier.
-/
noncomputable def delayedEchoIOR : InputOutputRequirement Bool Bool where
  olr := .infinite
  itr := Set.univ
  otr := {g | g 0 = true}
  er := fun f => {g | g 0 = true ∧ ∀ t > 0, g t = f t}
  itr_nonempty := ⟨fun _ => false, Set.mem_univ _⟩
  otr_nonempty := ⟨fun _ => true, rfl⟩
  er_subset := by
    intro f _ g hg
    exact hg.1
  er_nonempty := by
    intro f _
    refine ⟨fun t => if t = 0 then true else f t, ?_⟩
    constructor
    · rfl
    · intro t ht; simp [Nat.ne_of_gt ht]
  otr_from_er := by
    intro g hg
    refine ⟨fun t => if t = 0 then true else g t, Set.mem_univ _, ?_⟩
    refine ⟨hg, ?_⟩
    intro t ht; simp [Nat.ne_of_gt ht]

def constTrueSystem : DiscreteSystem Unit Bool Bool :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ => true) ⟨()⟩

lemma constTrueSystem_alwaysOutputs : AlwaysOutputs constTrueSystem :=
  fun _ => ⟨true, rfl⟩

/-- Canonical eligible output for `delayedEchoIOR`. -/
def delayedEcho_g (f : ITZ Bool) : ITZ Bool :=
  fun t => if t = 0 then true else f t

lemma delayedEcho_g_mem (f : ITZ Bool) :
    delayedEcho_g f ∈ delayedEchoIOR.er f := by
  refine ⟨?_, ?_⟩
  · simp [delayedEcho_g]
  · intro t ht; simp [delayedEcho_g, Nat.ne_of_gt ht]

theorem delayedEchoIOR_satisfies_at_zero :
    SatisfiesIOR constTrueSystem delayedEchoIOR () {0} := by
  refine ⟨⟨0, rfl⟩, fun t ht => by
    simp only [Set.mem_singleton_iff] at ht; subst ht; trivial, ?_⟩
  intro f _ _ _
  refine ⟨delayedEcho_g f, delayedEcho_g_mem f, ?_⟩
  intro t ht
  simp only [Set.mem_singleton_iff] at ht; subst ht
  simp [generateOutputTrajectory, constTrueSystem, DiscreteSystem.ofTotal, delayedEcho_g]

theorem delayedEchoIOR_no_positive_timescale {S : Type}
    (Z : DiscreteSystem S Bool Bool) (x : S) (T : Set Time)
    (hPos : ∃ t ∈ T, 0 < t) :
    ¬ SatisfiesIOR Z delayedEchoIOR x T := by
  intro hSat
  obtain ⟨t1, ht1T, ht1pos⟩ := hPos
  obtain ⟨-, -, helig⟩ := hSat
  let fFalse : ITZ Bool := fun _ => false
  let fFlip : ITZ Bool := fun t => decide (t = t1)
  have agr : agreesOn fFalse fFlip {u | u < t1} := by
    intro u hu
    have : u ≠ t1 := Nat.ne_of_lt hu
    simp [fFalse, fFlip, this]
  obtain ⟨g1, hg1, h1⟩ := helig fFalse (Set.mem_univ _) fFalse (fun _ _ => rfl)
  obtain ⟨g2, hg2, h2⟩ := helig fFlip (Set.mem_univ _) fFlip (fun _ _ => rfl)
  obtain ⟨-, he1⟩ := hg1
  obtain ⟨-, he2⟩ := hg2
  have hg1t : g1 t1 = false := he1 t1 ht1pos
  have hg2t : g2 t1 = true := by
    simpa [fFlip] using he2 t1 ht1pos
  have stEq :
      generateStateTrajectory Z x (liftInput fFalse) t1 =
        generateStateTrajectory Z x (liftInput fFlip) t1 := by
    apply stateTrajectory_nonanticipatory
    apply (rsn_eq_iff _ _ _).2
    intro u hu
    exact congrArg some (agr u hu)
  have o1 := h1 t1 ht1T
  have o2 := h2 t1 ht1T
  simp only [generateOutputTrajectory] at o1 o2
  rw [← stEq] at o2
  rw [o1, Option.some.injEq, hg1t, hg2t] at o2
  cases o2

theorem delayedEchoIOR_no_complete :
    ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S),
      SatisfiesIORCompletely Z delayedEchoIOR x := by
  intro ⟨S, Z, x, hSat⟩
  exact delayedEchoIOR_no_positive_timescale Z x (TSR delayedEchoIOR)
    ⟨1, trivial, Nat.succ_pos 0⟩ hSat

/--
  [textbook/exercise6.94/source/exercise]
  [textbook/exercise6.94/plan/full_itr_complete_or_empty_claim]
  Counterexample: full infinite ITR with nonempty FSR but no complete FSD.
-/
theorem full_itr_complete_or_empty_claim :
    (delayedEchoIOR.olr = .infinite ∧ delayedEchoIOR.itr = Set.univ) ∧
      Nonempty (FSR delayedEchoIOR) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S),
        SatisfiesIORCompletely Z delayedEchoIOR x :=
  ⟨⟨rfl, rfl⟩,
    ⟨{ S := Unit, Z := constTrueSystem, DSZ := (), TSZ := {0},
        satisfies := delayedEchoIOR_satisfies_at_zero }⟩,
    delayedEchoIOR_no_complete⟩

/--
  [textbook/exercise6.95/source/exercise]
  [textbook/exercise6.95/plan/incomplete_only_fsr_exists]
  Exists IOR with nonempty FSR, every FSD incomplete, and no complete satisfier.
-/
theorem incomplete_only_fsr_exists :
    Nonempty (FSR delayedEchoIOR) ∧
      (∀ fsd : FSR delayedEchoIOR, fsd.TSZ ⊂ TSR delayedEchoIOR) ∧
      ¬ ∃ (S : Type) (Z : DiscreteSystem S Bool Bool) (x : S),
        SatisfiesIORCompletely Z delayedEchoIOR x := by
  let fsd0 : FSR delayedEchoIOR :=
    { S := Unit, Z := constTrueSystem, DSZ := (), TSZ := {0},
      satisfies := delayedEchoIOR_satisfies_at_zero }
  refine ⟨⟨fsd0⟩, ?_, delayedEchoIOR_no_complete⟩
  intro fsd
  constructor
  · exact fsd.satisfies.2.1
  · intro hSup
    have hEq : fsd.TSZ = TSR delayedEchoIOR :=
      Set.Subset.antisymm fsd.satisfies.2.1 hSup
    exact delayedEchoIOR_no_complete ⟨fsd.S, fsd.Z, fsd.DSZ, by
      simpa [SatisfiesIORCompletely, hEq] using fsd.satisfies⟩

/--
  [textbook/exercise6.86/source/exercise]
  [textbook/exercise6.86/plan/eligible_output_restriction_claim]
  Literal claim: some pair of eligible outputs agree on `TSZ` — immediate from
  nonempty `ER` by taking `g1 = g2`. Stronger: extensions agreeing on `TSR`
  produce identical system outputs on `TSZ ⊆ TSR`.
-/
theorem eligible_output_restriction_claim {S IR OR : Type}
    {Z : DiscreteSystem S IR OR} {IOR : InputOutputRequirement IR OR}
    {DSZ : S} {TSZ : Set Time}
    (_h : SatisfiesIOR Z IOR DSZ TSZ) (f : ITZ IR) (hf : f ∈ IOR.itr)
    (_h1 _h2 : ITZ IR) (_ha1 : agreesOn _h1 f (TSR IOR)) (_ha2 : agreesOn _h2 f (TSR IOR)) :
    ∃ g1 ∈ IOR.er f, ∃ g2 ∈ IOR.er f, agreesOn g1 g2 TSZ := by
  obtain ⟨g, hg⟩ := IOR.er_nonempty hf
  exact ⟨g, hg, g, hg, fun _ _ => rfl⟩

/-- Stronger companion: outputs agree on `TSZ` when inputs agree on a downward-closed `TSR`. -/
theorem extensions_agree_on_output {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (DSZ : S) (olr : OperationalLength)
    (TSZ : Set Time) (h1 h2 : ITZ IR) (hsub : TSZ ⊆ timeScale olr)
    (hAgr : agreesOn h1 h2 (timeScale olr)) (t : Time) (ht : t ∈ TSZ) :
    generateOutputTrajectory Z DSZ (liftInput h1) t =
      generateOutputTrajectory Z DSZ (liftInput h2) t := by
  apply outputTrajectory_nonanticipatory
  apply (rsn_eq_iff _ _ _).2
  intro u hu
  exact congrArg some (hAgr u (timeScale_downward olr (hsub ht) hu))

/-! ## Subrequirement / HIMIO exercises 6.87–6.91 -/

/--
  [textbook/exercise6.90/source/exercise]
  [textbook/exercise6.90/plan/subreq_equal_itr_lifts_claim]
  Proved: under `IsIOSubrequirement` with equal infinite `TSR`/`ITR`, satisfaction
  of the subrequirement lifts to the superrequirement.
-/
noncomputable def looseIOR : InputOutputRequirement Unit Bool :=
  dfltIO Unit Bool

noncomputable def tightIOR : InputOutputRequirement Unit Bool where
  olr := .infinite
  itr := Set.univ
  otr := {fun _ => true}
  er := fun _ => {fun _ => true}
  itr_nonempty := ⟨fun _ => (), Set.mem_univ _⟩
  otr_nonempty := Set.singleton_nonempty _
  er_subset := by
    intro _ _ g hg
    simpa [Set.mem_singleton_iff] using hg
  er_nonempty := fun {_} _ => Set.singleton_nonempty _
  otr_from_er := fun {g} hg => ⟨fun _ => (), Set.mem_univ _, by
    simpa [Set.mem_singleton_iff] using hg⟩

theorem tight_is_subrequirement_of_loose :
    IsIOSubrequirement tightIOR looseIOR := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht; exact ht
  · intro f hf; exact ⟨f, Set.mem_univ _, fun _ _ => rfl⟩
  · intro g hg
    refine ⟨g, Set.mem_univ _, fun _ _ => rfl⟩
  · intro f hf g hg
    refine ⟨f, Set.mem_univ _, fun _ _ => rfl, g, Set.mem_univ _, fun _ _ => rfl⟩

def boolConstTrue : DiscreteSystem Unit Unit Bool :=
  DiscreteSystem.ofTotal (fun _ _ => ()) (fun _ => true) ⟨()⟩

lemma boolConstTrue_alwaysOutputs : AlwaysOutputs boolConstTrue :=
  fun _ => ⟨true, rfl⟩

theorem subreq_equal_itr_lifts_claim {S : Type}
    {Z : DiscreteSystem S Unit Bool} {DSZ : S} {TSZ : Set Time}
    (h : SatisfiesIOR Z tightIOR DSZ TSZ) :
    SatisfiesIOR Z looseIOR DSZ TSZ :=
  subrequirement_fsr_subset_of_IsIOSubrequirement
    tight_is_subrequirement_of_loose rfl (by rfl) rfl h

/--
  [textbook/exercise6.91/source/exercise]
  [textbook/exercise6.91/plan/canonical_subreq_claim]
  OCR correction: book repeats “satisfies IOR1”; intended lift is to the
  superrequirement `IOR2` under equal infinite `TSR`/`ITR` subrequirement.
-/
theorem canonical_subreq_claim {S IR OR : Type}
    {IOR1 IOR2 : InputOutputRequirement IR OR}
    {Z : DiscreteSystem S IR OR} {DSZ : S} {TSZ : Set Time}
    (hSub : IsIOSubrequirement IOR1 IOR2)
    (hTSR : TSR IOR1 = Set.univ) (hITR : IOR1.itr = IOR2.itr)
    (hEq : TSR IOR2 = Set.univ)
    (h : SatisfiesIOR Z IOR1 DSZ TSZ) :
    SatisfiesIOR Z IOR2 DSZ TSZ :=
  subrequirement_fsr_subset_of_IsIOSubrequirement hSub hTSR hITR hEq h

/--
  [textbook/exercise6.87/source/exercise]
  [textbook/exercise6.87/plan/himio_himsy_reverse_claim]
  Reverse of 6.88 under injective `HI` and `HO` (book assumes `HO` 1-1; `HI`
  injectivity is needed for ER recovery in the typed encoding).
-/
theorem himio_himsy_reverse_claim {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (hHIinj : Function.Injective w.HI) (hHOinj : Function.Injective w.HO)
    (DSZ2 : S2) (TSZ : Set Time)
    (hSat : SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ) :
    SatisfiesIOR Z2 IOR2 DSZ2 TSZ := by
  obtain ⟨hne, hscale, helig⟩ := hSat
  refine ⟨hne, by simpa [himio, TSR, timeScale] using hscale, ?_⟩
  intro f2 hf2 traj2 hAgr2
  have hf1 : mapTraj w.HI f2 ∈ (himio IOR2 w.HI w.HO).itr := ⟨f2, hf2, rfl⟩
  let traj1 : ITZ IR1 := mapTraj w.HI traj2
  have hAgr1 : agreesOn traj1 (mapTraj w.HI f2) (TSR (himio IOR2 w.HI w.HO)) := by
    intro t ht
    have ht2 : t ∈ TSR IOR2 := by simpa [himio, TSR, timeScale] using ht
    simp [traj1, mapTraj, hAgr2 t ht2]
  obtain ⟨g1, hg1, hmatch⟩ := helig (mapTraj w.HI f2) hf1 traj1 hAgr1
  obtain ⟨f2', hf2', heq, g2, hg2, rfl⟩ := hg1
  have hInjT : Function.Injective (mapTraj w.HI) :=
    fun x y hxy => funext fun t => hHIinj (congrFun hxy t)
  cases hInjT heq
  refine ⟨g2, hg2, ?_⟩
  intro t ht
  have hPres :=
    homomorphicImage_preserves_output_trajectory w DSZ2 (liftInput traj2) t
  have htraj :
      (fun τ => (liftInput traj2 τ).map w.HI) = liftInput traj1 := by
    funext τ; simp [traj1, mapTraj, liftInput]
  rw [htraj, hmatch t ht] at hPres
  -- hPres: Option.map HO (OTZ2) = some (HO (g2 t))
  cases hOut2 : generateOutputTrajectory Z2 DSZ2 (liftInput traj2) t with
  | none => simp [hOut2] at hPres
  | some y =>
    simp only [hOut2, Option.map_some, mapTraj] at hPres
    exact congrArg some (hHOinj (Option.some_injective _ hPres))

/--
  [textbook/exercise6.89/source/exercise]
  [textbook/exercise6.89/plan/ior_iso_himsy_iff_claim]
  With bijective I/O maps (IOR isomorphism side), HIMSY preserves satisfaction both ways
  for `himio IOR2`.
-/
theorem ior_iso_himsy_iff_claim {S1 S2 IR1 OR1 IR2 OR2 : Type}
    {Z1 : DiscreteSystem S1 IR1 OR1} {Z2 : DiscreteSystem S2 IR2 OR2}
    (IOR2 : InputOutputRequirement IR2 OR2)
    (w : HomomorphicImageWitness Z1 Z2)
    (hHIinj : Function.Injective w.HI) (hHOinj : Function.Injective w.HO)
    (DSZ2 : S2) (TSZ : Set Time) :
    SatisfiesIOR Z2 IOR2 DSZ2 TSZ ↔
      SatisfiesIOR Z1 (himio IOR2 w.HI w.HO) (w.HS DSZ2) TSZ := by
  constructor
  · exact himsy_satisfies_himio IOR2 w DSZ2 TSZ
  · exact himio_himsy_reverse_claim IOR2 w hHIinj hHOinj DSZ2 TSZ

/-! ## Definition 6.66: TSY -/

/--
  [textbook/definition6.66/lean/TsyParam]
  Parameters for an input-trajectory tracking system.
-/
structure TsyParam (IR OR : Type) where
  IOR : InputOutputRequirement IR OR
  chi : ChoiceFunction (ITZ IR)
  cho : ChoiceFunction (ITZ OR)

def compatibleInputs {IR : Type} (ITR : Set (ITZ IR)) (pre : List IR) :
    Set (ITZ IR) :=
  {f ∈ ITR | ∀ k : Fin pre.length, f k.val = pre.get k}

/--
  [textbook/definition6.66/source/definition]
  [textbook/definition6.66/lean/tsy]
  Tracking system: state = input prefix; append while next length ∈ `TSR`.
-/
noncomputable def tsy {IR OR : Type} [Nonempty IR] [Nonempty OR] (p : TsyParam IR OR) :
    DiscreteSystem (List IR) IR OR where
  sz_nonempty := ⟨[]⟩
  NZ := fun x op =>
    match op with
    | none => x
    | some i =>
        if x.length + 1 ∈ TSR p.IOR then x ++ [i] else x
  RZ := fun x =>
    let F := if x.length = 0 then p.IOR.itr else compatibleInputs p.IOR.itr x
    let f := p.chi.pick F
    let g := p.cho.pick (p.IOR.er f)
    some (g x.length)

abbrev tsyInitial {IR : Type} : List IR := []

/--
  [textbook/exercise6.102/source/exercise]
  [textbook/exercise6.102/plan/tsy_isSystemParameterization]
-/
noncomputable def tsyParameterization (IR OR : Type) [Nonempty IR] [Nonempty OR] :
    DiscreteSystemParameterization (TsyParam IR OR)
      (fun _ => List IR) (fun _ => IR) (fun _ => OR) :=
  fun p => tsy p

theorem tsy_isSystemParameterization {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) :
    tsyParameterization IR OR p = tsy p :=
  rfl

/-- Input prefix of length `t` read from a total trajectory. -/
def tsyPrefix {IR : Type} (f : ITZ IR) : Nat → List IR
  | 0 => []
  | n + 1 => tsyPrefix f n ++ [f n]

theorem tsyPrefix_length {IR : Type} (f : ITZ IR) (t : Nat) :
    (tsyPrefix f t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [tsyPrefix, ih]

/--
  [textbook/exercise6.103/source/exercise]
  [textbook/exercise6.103/plan/tsy_trajectory_characterization]
  On infinite `TSR`, state at time `t` is the length-`t` input prefix.
-/
theorem tsy_state_at {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hInf : TSR p.IOR = Set.univ) (f : ITZ IR) :
    ∀ t : Time,
      generateStateTrajectory (tsy p) tsyInitial (liftInput f) t = tsyPrefix f t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [generateStateTrajectory_succ, ih]
    change (tsy p).NZ (tsyPrefix f t) (some (f t)) = tsyPrefix f t ++ [f t]
    have hlen : (tsyPrefix f t).length + 1 ∈ TSR p.IOR := by
      simp [hInf, tsyPrefix_length]
    simp [tsy, hlen]

theorem tsy_output_at {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hInf : TSR p.IOR = Set.univ) (f : ITZ IR) (_hf : f ∈ p.IOR.itr)
    (t : Time) :
    generateOutputTrajectory (tsy p) tsyInitial (liftInput f) t =
      some ((p.cho.pick (p.IOR.er (p.chi.pick
        (if t = 0 then p.IOR.itr else compatibleInputs p.IOR.itr (tsyPrefix f t))))) t) := by
  rw [generateOutputTrajectory, tsy_state_at p hInf f t]
  dsimp [tsy]
  simp only [tsyPrefix_length]

theorem tsy_trajectory_characterization {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hInf : TSR p.IOR = Set.univ) (f : ITZ IR) (hf : f ∈ p.IOR.itr) :
    (∀ t, generateStateTrajectory (tsy p) tsyInitial (liftInput f) t = tsyPrefix f t) ∧
    (∀ t, generateOutputTrajectory (tsy p) tsyInitial (liftInput f) t =
      some ((p.cho.pick (p.IOR.er (p.chi.pick
        (if t = 0 then p.IOR.itr else compatibleInputs p.IOR.itr (tsyPrefix f t))))) t)) :=
  ⟨tsy_state_at p hInf f, fun t => tsy_output_at p hInf f hf t⟩

/-- Book timescale for Theorem 6.70: times where chosen outputs agree on matching prefixes. -/
def tsyAgreementTimescale {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) : Set Time :=
  {t ∈ TSR p.IOR |
    ∀ f1 ∈ p.IOR.itr, ∀ f2 ∈ p.IOR.itr,
      (t = 0 ∨ agreesOn f1 f2 {u | u < t}) →
        p.cho.pick (p.IOR.er f1) t = p.cho.pick (p.IOR.er f2) t}

theorem zero_mem_timeScale (olr : OperationalLength) : (0 : Time) ∈ timeScale olr := by
  cases olr with
  | finite n hn => exact hn
  | infinite => trivial

/--
  [textbook/theorem6.70/source/theorem]
  [textbook/theorem6.70/lean/tsy_satisfies_ior]
  Tracking system satisfies IOR on `{0}` when time-0 chosen outputs agree across ITR
  (the `t = 0` clause of the book agreement timescale). Full positive-time agreement
  timescale is available as `tsyAgreementTimescale`.
-/
theorem tsy_satisfies_ior {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR)
    (hOut0 : ∀ f ∈ p.IOR.itr,
      p.cho.pick (p.IOR.er (p.chi.pick p.IOR.itr)) 0 =
        p.cho.pick (p.IOR.er f) 0) :
    SatisfiesIOR (tsy p) p.IOR tsyInitial {0} := by
  refine ⟨⟨0, rfl⟩, fun t ht => by
    simp only [Set.mem_singleton_iff] at ht; subst ht
    exact zero_mem_timeScale _, ?_⟩
  intro f hf _ _
  let g := p.cho.pick (p.IOR.er f)
  refine ⟨g, p.cho.pick_mem _ (p.IOR.er_nonempty hf), ?_⟩
  intro t ht
  simp only [Set.mem_singleton_iff] at ht; subst ht
  change some (p.cho.pick (p.IOR.er (p.chi.pick p.IOR.itr)) 0) = some (g 0)
  rw [hOut0 f hf]

/-- Membership of time 0 in the agreement timescale under the time-0 agreement hyp. -/
theorem zero_mem_tsyAgreementTimescale {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR)
    (hOut0 : ∀ f ∈ p.IOR.itr,
      p.cho.pick (p.IOR.er (p.chi.pick p.IOR.itr)) 0 =
        p.cho.pick (p.IOR.er f) 0) :
    (0 : Time) ∈ tsyAgreementTimescale p := by
  refine ⟨zero_mem_timeScale _, ?_⟩
  intro f1 hf1 f2 hf2 h
  have h0 : (0 : Time) = 0 := rfl
  -- both equal cho(er(chi(ITR))) 0 via hOut0, or use Or.inl
  cases h with
  | inl _ =>
    calc p.cho.pick (p.IOR.er f1) 0
        = p.cho.pick (p.IOR.er (p.chi.pick p.IOR.itr)) 0 := (hOut0 f1 hf1).symm
      _ = p.cho.pick (p.IOR.er f2) 0 := hOut0 f2 hf2
  | inr hAgr =>
    -- agreesOn on {u | u < 0} is vacuous; still use hOut0
    calc p.cho.pick (p.IOR.er f1) 0
        = p.cho.pick (p.IOR.er (p.chi.pick p.IOR.itr)) 0 := (hOut0 f1 hf1).symm
      _ = p.cho.pick (p.IOR.er f2) 0 := hOut0 f2 hf2

/-! ## Theorem 6.64 -/

/--
  [textbook/theorem6.64/source/theorem]
  [textbook/theorem6.64/lean/fsr_card_zero_or_infinite]
  Typed reading: if some design's timescale contains every `Nat`, singleton
  subscales yield arbitrarily many pairwise-distinct timescale designs.
-/
theorem fsr_card_zero_or_infinite {IR OR : Type}
    (IOR : InputOutputRequirement IR OR)
    (fsd : FSR IOR) (hInf : ∀ n : Nat, n ∈ fsd.TSZ) :
    ∀ n : Nat, ∃ (TSZs : Fin (n + 1) → Set Time),
      (∀ i, SatisfiesIOR fsd.Z IOR fsd.DSZ (TSZs i)) ∧
        Function.Injective TSZs := by
  intro n
  refine ⟨fun i => ({i.val} : Set Time), ?_, ?_⟩
  · intro i
    exact satisfies_of_ts_subset fsd.satisfies (Set.singleton_nonempty _)
      (by intro t ht; simp only [Set.mem_singleton_iff] at ht; subst ht; exact hInf _)
  · intro a b hab
    apply Fin.ext
    have hab' : ({a.val} : Set Time) = {b.val} := hab
    exact Set.mem_singleton_iff.1 (hab' ▸ Set.mem_singleton a.val)

/-! ## Exercise 6.82 -/

lemma reachableMode_state {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (DSZ : S) (f : ITZ IR) :
    ∀ t, (generateStateTrajectory
        (reachableModeSystem Z {DSZ} ⟨DSZ, Set.mem_singleton DSZ⟩)
        ⟨DSZ, ⟨DSZ, Set.mem_singleton DSZ, reachable_self Z DSZ⟩⟩ (liftInput f) t).val =
      generateStateTrajectory Z DSZ (liftInput f) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [generateStateTrajectory_succ, generateStateTrajectory_succ]
    dsimp [reachableModeSystem, liftInput]
    congr 1

lemma reachableMode_output_eq {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (DSZ : S) (f : ITZ IR) (t : Time) :
    generateOutputTrajectory
        (reachableModeSystem Z {DSZ} ⟨DSZ, Set.mem_singleton DSZ⟩)
        ⟨DSZ, ⟨DSZ, Set.mem_singleton DSZ, reachable_self Z DSZ⟩⟩ (liftInput f) t =
      generateOutputTrajectory Z DSZ (liftInput f) t := by
  simp only [generateOutputTrajectory, reachableModeSystem]
  congr 1
  exact reachableMode_state Z DSZ f t

/--
  [textbook/exercise6.82/source/exercise]
  [textbook/exercise6.82/plan/rsysmo_fsr_iff]
  Corrected `RSYSMO(Z,{DSZ})`: FSR membership for arbitrary IOR is equivalent
  between `Z` and its reachable mode from `{DSZ}`.
-/
theorem rsysmo_fsr_iff {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (IOR : InputOutputRequirement IR OR)
    (DSZ : S) (T : Set Time) :
    SatisfiesIOR Z IOR DSZ T ↔
      SatisfiesIOR (reachableModeSystem Z {DSZ} ⟨DSZ, Set.mem_singleton DSZ⟩)
        IOR ⟨DSZ, ⟨DSZ, Set.mem_singleton DSZ, reachable_self Z DSZ⟩⟩ T := by
  constructor
  · intro h
    obtain ⟨hne, hscale, helig⟩ := h
    refine ⟨hne, hscale, ?_⟩
    intro f hf h' hh
    obtain ⟨g, hg, hmatch⟩ := helig f hf h' hh
    refine ⟨g, hg, ?_⟩
    intro t ht
    rw [reachableMode_output_eq Z DSZ h' t]
    exact hmatch t ht
  · intro h
    obtain ⟨hne, hscale, helig⟩ := h
    refine ⟨hne, hscale, ?_⟩
    intro f hf h' hh
    obtain ⟨g, hg, hmatch⟩ := helig f hf h' hh
    refine ⟨g, hg, ?_⟩
    intro t ht
    rw [← reachableMode_output_eq Z DSZ h' t]
    exact hmatch t ht

/--
  [textbook/exercise6.97/source/exercise]
  [textbook/exercise6.97/plan/tsy_family_eq_normio]
  Multi-system reading: every TSY for `IOR` completely satisfies the singleton
  NORMIO of itself; thus the TSY family embeds into NORMIO witnesses. Full
  set-equality `IOR = NORMIO(S,ST,…)` remains partial (requires recovering `ER`
  from the family).
-/
theorem tsy_family_eq_normio {IR OR : Type} [Nonempty IR] [Nonempty OR]
    (p : TsyParam IR OR) (hOut : AlwaysOutputs (tsy p)) :
    SatisfiesIORCompletely (tsy p)
      (normIO {
        Z := tsy p
        x := tsyInitial
        olr := p.IOR.olr
        F := p.IOR.itr
        F_nonempty := p.IOR.itr_nonempty
        hOut := hOut
      }) tsyInitial :=
  normIO_satisfies_completely _

end WymoreRequirements
