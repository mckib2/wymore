import Mbse.WymoreSystemModes
import Mbse.Homomorphism
import Mbse.Isomorphism

/-!
# Wymore Chapter 5: implementation

This module gives witness-carrying readings of Definitions 5.71,
5.77, 5.80, 5.82, and 5.89 and Theorems 5.92, 5.93, 5.95, 5.97, and 5.99.

The source's inverse notation is read as a nonempty fiber.  A lifted mode input
uses the supplied input itself at time zero and chosen preimages thereafter.

`DiscreteSystem` admits autonomous (`none`) transitions.  Definition 5.6
constrains only mode inputs (`some p`).  For the important class of systems
that also take autonomous steps, `ModePreservesAutonomous` is the charitable
enrichment that extends the mode embedding to `none`.  It is retained
intentionally, not as a textbook error to erase.
-/

namespace WymoreImplementation

open WymoreSystemModes
open Homomorphism

universe u

/-! ## Definitions 5.71, 5.77, 5.80, and 5.82 -/

/--
  [textbook/definition5.71/source/definition]
  [textbook/definition5.71/lean/System_Implements]
  An implementation explicitly carries both stages in Definition 5.71: a
  concrete system mode of the implementing system and a homomorphic-image
  witness from that mode to the implemented system.
-/
structure Implements {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    (Z₁ : DiscreteSystem S₁ I₁ O₁) (Z₂ : DiscreteSystem S₂ I₂ O₂) where
  ModeState : Type
  ModeInput : Type
  ModeOutput : Type
  modeSystem : DiscreteSystem ModeState ModeInput ModeOutput
  mode : SystemMode modeSystem Z₂
  hom : HomomorphicImageWitness Z₁ modeSystem

/--
  [textbook/definition5.77/source/definition]
  [textbook/definition5.77/lean/implementedSystems]
  Parameters for `IMPSY`, retaining the complete implementation witness.
-/
structure ImplementedSystemParameter (S I O : Type) where
  ImplState : Type
  ImplInput : Type
  ImplOutput : Type
  implemented : DiscreteSystem S I O
  implementing : DiscreteSystem ImplState ImplInput ImplOutput
  witness : Implements implemented implementing

/--
  [textbook/definition5.77/lean/implementedSystems]
  `IMPSY` is a system parameterization: it returns the explicitly named
  implemented system from an implementation parameter.
-/
def implementedSystems (S I O : Type) :
    DiscreteSystemParameterization (ImplementedSystemParameter S I O)
      (fun _ => S) (fun _ => I) (fun _ => O) :=
  fun p => p.implemented

/--
  [textbook/definition5.80/source/definition]
  [textbook/definition5.80/lean/System_IsomorphicallyImplements]
  Definition 5.80 using the very same homomorphism maps carried by `Implements`.
-/
structure IsomorphicallyImplements {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    (Z₁ : DiscreteSystem S₁ I₁ O₁) (Z₂ : DiscreteSystem S₂ I₂ O₂)
    extends Implements Z₁ Z₂ where
  HS_injective : Function.Injective toImplements.hom.HS
  HI_injective : Function.Injective toImplements.hom.HI
  HO_injective : Function.Injective toImplements.hom.HO

/-- The isomorphic stage of an isomorphic implementation, with identical maps. -/
def IsomorphicallyImplements.isomorphism
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : IsomorphicallyImplements Z₁ Z₂) :
    IsomorphismWitness Z₁ w.modeSystem where
  toHomomorphicImageWitness := w.hom
  HS_injective := w.HS_injective
  HI_injective := w.HI_injective
  HO_injective := w.HO_injective

/--
  [textbook/definition5.82/source/definition]
  [textbook/definition5.82/lean/System_ExactlyImplements]
  Definition 5.82, specialized to the port-indexed systems required by `COPY`.
  The mode, homomorphism, and copy are all explicit, and the copy uses the same
  homomorphism witness as the implementation.
-/
structure ExactlyImplements
    {S₁ S₂ SM Port₁ PortM OutPort₁ OutPortM : Type}
    {PV₁ : Port₁ → Type} {PVM : PortM → Type}
    {OV₁ : OutPort₁ → Type} {OVM : OutPortM → Type}
    {I₂ O₂ : Type}
    (Z₁ : DiscreteSystem S₁ ((p : Port₁) → PV₁ p) ((q : OutPort₁) → OV₁ q))
    (Z₂ : DiscreteSystem S₂ I₂ O₂) where
  modeSystem :
    DiscreteSystem SM ((p : PortM) → PVM p) ((q : OutPortM) → OVM q)
  mode : SystemMode modeSystem Z₂
  copy : CopyWitness Z₁ modeSystem

/-- Exact implementation is, in particular, an implementation. -/
def ExactlyImplements.toImplements
    {S₁ S₂ SM Port₁ PortM OutPort₁ OutPortM : Type}
    {PV₁ : Port₁ → Type} {PVM : PortM → Type}
    {OV₁ : OutPort₁ → Type} {OVM : OutPortM → Type}
    {I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ ((p : Port₁) → PV₁ p) ((q : OutPort₁) → OV₁ q)}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : @ExactlyImplements S₁ S₂ SM Port₁ PortM OutPort₁ OutPortM
      PV₁ PVM OV₁ OVM I₂ O₂ Z₁ Z₂) : Implements Z₁ Z₂ where
  ModeState := SM
  ModeInput := (p : PortM) → PVM p
  ModeOutput := (q : OutPortM) → OVM q
  modeSystem := w.modeSystem
  mode := w.mode
  hom := w.copy.toHomomorphicImageWitness

/-! ## Definition 5.89: homomorphic inverse-image modes -/

/--
  [textbook/definition5.89/source/definition]
  [textbook/definition5.89/lean/homomorphicInverseImageMode]
  Autonomous enrichment of a system mode: the state embedding preserves
  `none`-input steps.  Systems that stutter on autonomous steps
  (`DiscreteSystem.ofTotal`) satisfy it automatically.

  This is the mode-side counterpart of
  `Homomorphism.StepPreservingMaps.preserves_autonomous`.
-/
def ModePreservesAutonomous
    {SM IM OM S₁ I₁ O₁ : Type}
    {ZM : DiscreteSystem SM IM OM} {Z₁ : DiscreteSystem S₁ I₁ O₁}
    (M : SystemMode ZM Z₁) : Prop :=
  ∀ x, M.stateMap (ZM.NZ x none) = Z₁.NZ (M.stateMap x) none

/-- Autonomous stutter on both sides yields the enrichment for free. -/
theorem ModePreservesAutonomous.of_autonomous_stutter
    {SM IM OM S₁ I₁ O₁ : Type}
    {ZM : DiscreteSystem SM IM OM} {Z₁ : DiscreteSystem S₁ I₁ O₁}
    (M : SystemMode ZM Z₁)
    (hM : ∀ x, ZM.NZ x none = x) (h1 : ∀ y, Z₁.NZ y none = y) :
    ModePreservesAutonomous M := by
  intro x
  rw [hM, h1]

/--
  Explicit parameters for the corrected `HIISYSMO` construction.
-/
structure InverseImageModeData
    {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    (ZM : DiscreteSystem SM IM OM)
    (Z₁ : DiscreteSystem S₁ I₁ O₁)
    (Z₂ : DiscreteSystem S₂ I₂ O₂) where
  hom : HomomorphicImageWitness Z₁ Z₂
  mode : SystemMode ZM Z₁
  autonomous : ModePreservesAutonomous mode

namespace InverseImageModeData

variable {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
variable {ZM : DiscreteSystem SM IM OM}
  {Z₁ : DiscreteSystem S₁ I₁ O₁}
  {Z₂ : DiscreteSystem S₂ I₂ O₂}
  (D : InverseImageModeData ZM Z₁ Z₂)

/-- `HS⁻¹(SM)`, represented as a typed nonempty fiber. -/
abbrev State := {x : S₂ // ∃ s : SM, D.hom.HS x = D.mode.stateMap s}

/-- `HI⁻¹(IM)`, represented as a typed nonempty fiber. -/
abbrev Input := {p : I₂ // ∃ i : IM, D.hom.HI p = D.mode.inputMap i}

/-- `HO⁻¹(OM)`, represented as a typed nonempty fiber. -/
abbrev Output := {q : O₂ // ∃ o : OM, D.hom.HO q = D.mode.outputMap o}

noncomputable def stateProjection (x : D.State) : SM :=
  Classical.choose x.property

theorem stateProjection_spec (x : D.State) :
    D.hom.HS x.val = D.mode.stateMap (D.stateProjection x) :=
  Classical.choose_spec x.property

noncomputable def inputProjection (p : D.Input) : IM :=
  Classical.choose p.property

theorem inputProjection_spec (p : D.Input) :
    D.hom.HI p.val = D.mode.inputMap (D.inputProjection p) :=
  Classical.choose_spec p.property

noncomputable def outputProjection (q : D.Output) : OM :=
  Classical.choose q.property

theorem outputProjection_spec (q : D.Output) :
    D.hom.HO q.val = D.mode.outputMap (D.outputProjection q) :=
  Classical.choose_spec q.property

/--
Chosen lift of a mode-input trajectory.  The distinguished supplied preimage
is used at zero; surjectivity chooses a fiber representative at later times.
-/
noncomputable def liftedInput (p : D.Input) : ITZ I₁ → ITZ I₂ :=
  fun f t =>
    if t = 0 then p.val else Classical.choose (D.hom.HI_surjective (f t))

theorem liftedInput_zero (p : D.Input) (f : ITZ I₁) :
    D.liftedInput p f 0 = p.val := by
  simp [liftedInput]

theorem liftedInput_maps (p : D.Input) (f : ITZ I₁)
    (hzero : f 0 = D.hom.HI p.val) :
    ∀ t, D.hom.HI (D.liftedInput p f t) = f t := by
  intro t
  by_cases ht : t = 0
  · subst ht
    simp [liftedInput, hzero]
  · simp [liftedInput, ht, Classical.choose_spec (D.hom.HI_surjective (f t))]

noncomputable def behaviorInput (x : D.State) (p : D.Input) : ITZ I₂ :=
  D.liftedInput p
    (D.mode.inputIndex (D.stateProjection x) (D.inputProjection p))

theorem behaviorInput_maps (x : D.State) (p : D.Input) :
    ∀ t, D.hom.HI (D.behaviorInput x p t) =
      D.mode.inputIndex (D.stateProjection x) (D.inputProjection p) t := by
  apply D.liftedInput_maps
  change D.mode.behavior.input (D.stateProjection x) (D.inputProjection p) 0 =
    D.hom.HI p.val
  rw [D.mode.behavior_initial, ← D.inputProjection_spec]

noncomputable def nextState (x : D.State) (p : D.Input) : D.State := by
  let y := generateStateTrajectory Z₂ x.val (liftInput (D.behaviorInput x p))
    (D.mode.timeIndex (D.stateProjection x) (D.inputProjection p))
  refine ⟨y, ?_⟩
  refine ⟨ZM.NZ (D.stateProjection x) (some (D.inputProjection p)), ?_⟩
  change D.hom.HS y =
    D.mode.stateMap (ZM.NZ (D.stateProjection x) (some (D.inputProjection p)))
  rw [D.mode.transition]
  rw [homomorphicImage_preserves_state_trajectory D.hom x.val
    (liftInput (D.behaviorInput x p))]
  rw [D.stateProjection_spec]
  congr 1
  funext t
  simp only [liftInput]
  simpa using congrArg some (D.behaviorInput_maps x p t)

theorem nextState_maps (x : D.State) (p : D.Input) :
    D.hom.HS (D.nextState x p).val =
      D.mode.stateMap
        (ZM.NZ (D.stateProjection x) (some (D.inputProjection p))) := by
  unfold nextState
  dsimp only
  rw [D.mode.transition]
  rw [homomorphicImage_preserves_state_trajectory D.hom x.val
    (liftInput (D.behaviorInput x p))]
  rw [D.stateProjection_spec]
  congr 1
  funext t
  simp only [liftInput]
  simpa using congrArg some (D.behaviorInput_maps x p t)

noncomputable def autonomousNext (x : D.State) : D.State := by
  refine ⟨Z₂.NZ x.val none, ?_⟩
  refine ⟨ZM.NZ (D.stateProjection x) none, ?_⟩
  rw [D.hom.preserves_transition]
  simp only [Option.map_none]
  rw [D.stateProjection_spec, D.autonomous]

theorem autonomousNext_maps (x : D.State) :
    D.hom.HS (D.autonomousNext x).val =
      D.mode.stateMap (ZM.NZ (D.stateProjection x) none) := by
  unfold autonomousNext
  dsimp only
  rw [D.hom.preserves_transition]
  simp only [Option.map_none]
  rw [D.stateProjection_spec, D.autonomous]

private theorem output_mem (x : D.State) (q : O₂)
    (hq : Z₂.RZ x.val = some q) :
    ∃ o : OM, D.hom.HO q = D.mode.outputMap o := by
  have hh := D.hom.preserves_readout x.val
  have hm := D.mode.readout (D.stateProjection x)
  rw [hq, Option.map_some, D.stateProjection_spec] at hh
  rw [← hm] at hh
  cases hz : ZM.RZ (D.stateProjection x) with
  | none =>
      rw [hz] at hh
      contradiction
  | some o =>
      rw [hz] at hh
      exact ⟨o, Option.some_injective _ hh⟩

noncomputable def readout (x : D.State) : Option D.Output :=
  match hq : Z₂.RZ x.val with
  | none => none
  | some q => some ⟨q, D.output_mem x q hq⟩

theorem readout_map_val (x : D.State) :
    (D.readout x).map Subtype.val = Z₂.RZ x.val := by
  unfold readout
  split <;> simp_all

/--
  [textbook/definition5.89/lean/homomorphicInverseImageMode]
  The homomorphic inverse-image system with chosen input fibers.
-/
noncomputable def homomorphicInverseImageMode :
    DiscreteSystem D.State D.Input D.Output where
  sz_nonempty := by
    obtain ⟨s⟩ := ZM.sz_nonempty
    obtain ⟨x, hx⟩ := D.hom.HS_surjective (D.mode.stateMap s)
    exact ⟨⟨x, s, hx⟩⟩
  NZ := fun x op =>
    match op with
    | none => D.autonomousNext x
    | some p => D.nextState x p
  RZ := D.readout

/--
  [textbook/definition5.89/lean/hiisysmo]
  The lifted SMBF witnesses that the inverse-image system is a mode of `Z₂`.
-/
noncomputable def inverseImageSystemMode :
    SystemMode D.homomorphicInverseImageMode Z₂ where
  stateMap := Subtype.val
  inputMap := Subtype.val
  outputMap := Subtype.val
  stateMap_injective := Subtype.val_injective
  inputMap_injective := Subtype.val_injective
  outputMap_injective := Subtype.val_injective
  behavior :=
    { input := D.behaviorInput
      duration := fun x p =>
        D.mode.timeIndex (D.stateProjection x) (D.inputProjection p)
      duration_pos := fun x p =>
        D.mode.behavior.duration_pos (D.stateProjection x) (D.inputProjection p) }
  behavior_initial := fun x p => by
    simp [behaviorInput, liftedInput]
  transition := by
    intro x p
    change (D.nextState x p).val =
      generateStateTrajectory Z₂ x.val (liftInput (D.behaviorInput x p))
        (D.mode.timeIndex (D.stateProjection x) (D.inputProjection p))
    simp [nextState]
  readout := D.readout_map_val

theorem stateProjection_next (x : D.State) (p : D.Input) :
    D.stateProjection (D.nextState x p) =
      ZM.NZ (D.stateProjection x) (some (D.inputProjection p)) := by
  apply D.mode.stateMap_injective
  rw [← D.stateProjection_spec]
  exact D.nextState_maps x p

theorem stateProjection_autonomous (x : D.State) :
    D.stateProjection (D.autonomousNext x) =
      ZM.NZ (D.stateProjection x) none := by
  apply D.mode.stateMap_injective
  rw [← D.stateProjection_spec]
  exact D.autonomousNext_maps x

/--
  [textbook/theorem5.95/lean/mode_isHomomorphicImage_of_inverseImage]
  Restricted `HS`, `HI`, and `HO` make the original mode a homomorphic image.
-/
noncomputable def inverseImageHom :
    HomomorphicImageWitness ZM D.homomorphicInverseImageMode where
  HS := D.stateProjection
  HI := D.inputProjection
  HO := D.outputProjection
  HS_surjective := by
    intro s
    obtain ⟨x, hx⟩ := D.hom.HS_surjective (D.mode.stateMap s)
    let xs : D.State := ⟨x, s, hx⟩
    refine ⟨xs, D.mode.stateMap_injective ?_⟩
    rw [← D.stateProjection_spec xs]
    exact hx
  HI_surjective := by
    intro i
    obtain ⟨p, hp⟩ := D.hom.HI_surjective (D.mode.inputMap i)
    let ps : D.Input := ⟨p, i, hp⟩
    refine ⟨ps, D.mode.inputMap_injective ?_⟩
    rw [← D.inputProjection_spec ps]
    exact hp
  HO_surjective := by
    intro o
    obtain ⟨q, hq⟩ := D.hom.HO_surjective (D.mode.outputMap o)
    let qs : D.Output := ⟨q, o, hq⟩
    refine ⟨qs, D.mode.outputMap_injective ?_⟩
    rw [← D.outputProjection_spec qs]
    exact hq
  preserves_transition := by
    intro x op
    cases op with
    | none => exact D.stateProjection_autonomous x
    | some p => exact D.stateProjection_next x p
  preserves_readout := by
    intro x
    have hh := D.hom.preserves_readout x.val
    have hm := D.mode.readout (D.stateProjection x)
    rw [D.stateProjection_spec] at hh
    rw [← hm] at hh
    change (D.readout x).map D.outputProjection =
      ZM.RZ (D.stateProjection x)
    unfold readout
    split
    · rename_i hnone
      cases hz : ZM.RZ (D.stateProjection x) with
      | none => rfl
      | some o =>
          rw [hnone, hz] at hh
          simp at hh
    · rename_i q hq
      cases hz : ZM.RZ (D.stateProjection x) with
      | none =>
          rw [hq, hz] at hh
          simp at hh
      | some o =>
          simp only [Option.map_some]
          apply congrArg some
          apply D.mode.outputMap_injective
          rw [← D.outputProjection_spec]
          rw [hq, hz] at hh
          exact Option.some_injective _ hh

end InverseImageModeData

/--
  [textbook/theorem5.92/source/theorem]
  [textbook/theorem5.92/lean/hiisysmo_isSystemParameterization]
  `HIISYSMO` is a well-typed system parameterization over explicit data.
-/
noncomputable def hiisysmo
    {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {ZM : DiscreteSystem SM IM OM}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂} :
    DiscreteSystemParameterization (InverseImageModeData ZM Z₁ Z₂)
      (fun D => D.State) (fun D => D.Input) (fun D => D.Output) :=
  fun D => D.homomorphicInverseImageMode

theorem hiisysmo_isSystemParameterization
    {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {ZM : DiscreteSystem SM IM OM}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (D : InverseImageModeData ZM Z₁ Z₂) :
    hiisysmo D = D.homomorphicInverseImageMode :=
  rfl

/--
  [textbook/theorem5.93/source/theorem]
  [textbook/theorem5.93/lean/homomorphicInverseImage_isSystemMode]
  The inverse image is a mode of the elaborating system.
-/
theorem homomorphicInverseImage_isSystemMode
    {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {ZM : DiscreteSystem SM IM OM}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (D : InverseImageModeData ZM Z₁ Z₂) :
    IsSystemMode D.homomorphicInverseImageMode Z₂ :=
  ⟨D.inverseImageSystemMode⟩

/--
  [textbook/theorem5.95/source/theorem]
  [textbook/theorem5.95/lean/mode_isHomomorphicImage_of_inverseImage]
-/
theorem mode_isHomomorphicImage_of_inverseImage
    {SM IM OM S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {ZM : DiscreteSystem SM IM OM}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (D : InverseImageModeData ZM Z₁ Z₂) :
    IsHomomorphicImage ZM D.homomorphicInverseImageMode :=
  ⟨D.inverseImageHom⟩

/-! ## Theorem 5.97: transitivity of implementation -/

/--
  [textbook/theorem5.97/source/theorem]
  [textbook/theorem5.97/lean/implements_trans]
  Transitivity through the explicit inverse-image mode.  The additional
  autonomous hypothesis is exactly the autonomous enrichment for `none` steps described
  above.
-/
noncomputable def Implements.trans
    {S₁ I₁ O₁ S₂ I₂ O₂ S₃ I₃ O₃ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    {Z₃ : DiscreteSystem S₃ I₃ O₃}
    (w₁₂ : Implements Z₁ Z₂) (w₂₃ : Implements Z₂ Z₃)
    (hauto : ModePreservesAutonomous w₁₂.mode) :
    Implements Z₁ Z₃ := by
  let D : InverseImageModeData w₁₂.modeSystem Z₂ w₂₃.modeSystem :=
    { hom := w₂₃.hom, mode := w₁₂.mode, autonomous := hauto }
  exact
    { ModeState := D.State
      ModeInput := D.Input
      ModeOutput := D.Output
      modeSystem := D.homomorphicInverseImageMode
      mode := D.inverseImageSystemMode.trans w₂₃.mode
      hom := w₁₂.hom.comp D.inverseImageHom }

noncomputable def implements_trans
    {S₁ I₁ O₁ S₂ I₂ O₂ S₃ I₃ O₃ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁}
    {Z₂ : DiscreteSystem S₂ I₂ O₂}
    {Z₃ : DiscreteSystem S₃ I₃ O₃}
    (w₁₂ : Implements Z₁ Z₂) (w₂₃ : Implements Z₂ Z₃)
    (hauto : ModePreservesAutonomous w₁₂.mode) :
    Implements Z₁ Z₃ :=
  w₁₂.trans w₂₃ hauto

/-! ## Theorem 5.99: lifting implemented experiments -/

/-- A pointwise chosen lift of an implemented-system input trajectory. -/
noncomputable def implementedInputLift
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (f : ITZ I₁) : ITZ w.ModeInput :=
  fun t => Classical.choose (w.hom.HI_surjective (f t))

theorem implementedInputLift_maps
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (f : ITZ I₁) :
    ∀ t, w.hom.HI (implementedInputLift w f t) = f t :=
  fun t => Classical.choose_spec (w.hom.HI_surjective (f t))

/-- A chosen mode-state preimage of an implemented-system state. -/
noncomputable def implementedStateLift
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (x : S₁) : w.ModeState :=
  Classical.choose (w.hom.HS_surjective x)

theorem implementedStateLift_maps
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (x : S₁) :
    w.hom.HS (implementedStateLift w x) = x :=
  Classical.choose_spec (w.hom.HS_surjective x)

/--
  [textbook/theorem5.99/source/theorem]
  [textbook/theorem5.99/lean/implementedExperiment_lift]
  Explicit lifted mode and exhibitor experiments, with chosen state/input
  fibers and segment concatenation inherited from Theorem 5.62.
-/
noncomputable def implementedExperiment_lift
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (f : ITZ I₁) (x : S₁) (t : Time) :
    EXZ S₂ I₂ :=
  let g := implementedInputLift w f
  let xs := implementedStateLift w x
  (liftInput (compiledInput w.mode xs g t), w.mode.stateMap xs,
    compiledElapsed w.mode xs g t)

/--
  [textbook/theorem5.99/lean/implementedExperiment_state]
  The mode endpoint both expands to the exhibitor endpoint and projects to the
  implemented endpoint.  The source writes `HS` directly on an exhibitor
  state, which is ill-typed when the mode embedding is not an identity.
-/
theorem implementedExperiment_state
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (f : ITZ I₁) (x : S₁) (t : Time) :
    generateStateTrajectory Z₂ (implementedExperiment_lift w f x t).2.1
          (implementedExperiment_lift w f x t).1
          (implementedExperiment_lift w f x t).2.2 =
        w.mode.stateMap
          (generateStateTrajectory w.modeSystem (implementedStateLift w x)
            (liftInput (implementedInputLift w f)) t) ∧
      w.hom.HS
          (generateStateTrajectory w.modeSystem (implementedStateLift w x)
            (liftInput (implementedInputLift w f)) t) =
        generateStateTrajectory Z₁ x (liftInput f) t := by
  let g := implementedInputLift w f
  let xs := implementedStateLift w x
  constructor
  · change generateStateTrajectory Z₂ (w.mode.stateMap xs)
        (liftInput (compiledInput w.mode xs g t))
        (compiledElapsed w.mode xs g t) =
      w.mode.stateMap
        (generateStateTrajectory w.modeSystem xs (liftInput g) t)
    exact compiled_state w.mode xs g t
  · rw [homomorphicImage_preserves_state_trajectory w.hom xs (liftInput g) t]
    rw [implementedStateLift_maps]
    congr 1
    funext n
    simp only [liftInput]
    simpa using congrArg some (implementedInputLift_maps w f n)

/--
  [textbook/theorem5.99/lean/implementedExperiment_output]
  Corresponding mode output maps to both the exhibitor output and the
  implemented output.  This is the strongest typed form of the source claim.
-/
theorem implementedExperiment_output
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (w : Implements Z₁ Z₂) (f : ITZ I₁) (x : S₁) (t : Time) :
    (generateOutputTrajectory w.modeSystem (implementedStateLift w x)
        (liftInput (implementedInputLift w f)) t).map w.mode.outputMap =
      generateOutputTrajectory Z₂ (implementedExperiment_lift w f x t).2.1
        (implementedExperiment_lift w f x t).1
        (implementedExperiment_lift w f x t).2.2 ∧
      (generateOutputTrajectory w.modeSystem (implementedStateLift w x)
        (liftInput (implementedInputLift w f)) t).map w.hom.HO =
      generateOutputTrajectory Z₁ x (liftInput f) t := by
  let g := implementedInputLift w f
  let xs := implementedStateLift w x
  constructor
  · change (generateOutputTrajectory w.modeSystem xs (liftInput g) t).map
        w.mode.outputMap =
      generateOutputTrajectory Z₂ (w.mode.stateMap xs)
        (liftInput (compiledInput w.mode xs g t))
        (compiledElapsed w.mode xs g t)
    exact compiled_output w.mode xs g t
  · rw [homomorphicImage_preserves_output_trajectory w.hom xs (liftInput g) t]
    rw [implementedStateLift_maps]
    congr 1
    funext n
    simp only [liftInput]
    simpa using congrArg some (implementedInputLift_maps w f n)

/-! ## Implements from mode / HIMSY / iso / copy (Exercise 5.177) -/

/-- A system mode yields an implementation of the mode system by the exhibitor. -/
def Implements.ofSystemMode
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (M : SystemMode Z₁ Z₂) : Implements Z₁ Z₂ where
  ModeState := S₁
  ModeInput := I₁
  ModeOutput := O₁
  modeSystem := Z₁
  mode := M
  hom := HomomorphicImageWitness.refl Z₁

/-- A homomorphic image witness yields an implementation via the exhibitor self-mode. -/
def Implements.ofHomomorphicImage
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (h : HomomorphicImageWitness Z₁ Z₂) : Implements Z₁ Z₂ where
  ModeState := S₂
  ModeInput := I₂
  ModeOutput := O₂
  modeSystem := Z₂
  mode := primarySelfMode Z₂
  hom := h

/-- An isomorphism yields an implementation. -/
def Implements.ofIsomorphism
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂}
    (h : IsomorphismWitness Z₁ Z₂) : Implements Z₁ Z₂ :=
  Implements.ofHomomorphicImage h.toHomomorphicImageWitness

/-- A copy yields an implementation. -/
def Implements.ofCopy
    {S₁ S₂ : Type} {Port₁ Port₂ OutPort₁ OutPort₂ : Type}
    {PV₁ : Port₁ → Type} {PV₂ : Port₂ → Type}
    {OV₁ : OutPort₁ → Type} {OV₂ : OutPort₂ → Type}
    {Z₁ : DiscreteSystem S₁ ((p : Port₁) → PV₁ p) ((q : OutPort₁) → OV₁ q)}
    {Z₂ : DiscreteSystem S₂ ((p : Port₂) → PV₂ p) ((q : OutPort₂) → OV₂ q)}
    (h : CopyWitness Z₁ Z₂) : Implements Z₁ Z₂ :=
  Implements.ofIsomorphism h.toIsomorphismWitness

/--
  [textbook/exercise5.177/plan/implements_of_mode_hom_iso_exercise]
  Mode, homomorphic image, isomorphism, or copy each yields `Implements`.
-/
theorem implements_of_mode_hom_iso_copy
    {S₁ I₁ O₁ S₂ I₂ O₂ : Type}
    {Z₁ : DiscreteSystem S₁ I₁ O₁} {Z₂ : DiscreteSystem S₂ I₂ O₂} :
    (Nonempty (SystemMode Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) ∧
    (Nonempty (HomomorphicImageWitness Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) ∧
    (Nonempty (IsomorphismWitness Z₁ Z₂) → Nonempty (Implements Z₁ Z₂)) :=
  ⟨fun ⟨M⟩ => ⟨Implements.ofSystemMode M⟩,
    fun ⟨h⟩ => ⟨Implements.ofHomomorphicImage h⟩,
    fun ⟨h⟩ => ⟨Implements.ofIsomorphism h⟩⟩

/-! ## Time-elaboration implements (Exercise 5.174) -/

theorem timeElaborateModeSystem_NZ_eq
    {S I O : Type} (Z : DiscreteSystem S I O) (n : Nat) (hn : 1 < n)
    (x : S) (p : I) :
    (timeElaborateModeSystem Z n hn).NZ x (some p) = Z.NZ x (some p) := by
  change (generateStateTrajectory (timeElaborate Z n hn)
      (timeElaborateSliceEmbed Z n hn x) (liftInput (fun _ => p)) n).1 = Z.NZ x (some p)
  rw [timeElaborate_full_cycle]
  rfl

/-- The original system is implemented by its time elaboration via the phase-0 mode. -/
def timeElaborateImplements
    {S I O : Type} (Z : DiscreteSystem S I O) (n : Nat) (hn : 1 < n) :
    Implements Z (timeElaborate Z n hn) where
  ModeState := S
  ModeInput := I
  ModeOutput := O
  modeSystem := timeElaborateModeSystem Z n hn
  mode := timeElaborateMode Z n hn
  hom := {
    HS := id
    HI := id
    HO := id
    HS_surjective := Function.surjective_id
    HI_surjective := Function.surjective_id
    HO_surjective := Function.surjective_id
    preserves_transition := by
      intro x oi
      cases oi with
      | none => rfl
      | some p =>
        change (timeElaborateModeSystem Z n hn).NZ x (some p) = Z.NZ x (some p)
        exact timeElaborateModeSystem_NZ_eq Z n hn x p
    preserves_readout := fun _ => by simp [timeElaborateModeSystem]
  }

/-! ## IIMPSY / EIMPSY parameterizations (Exercises 5.178–5.179) -/

/-- Parameters for isomorphic implementation systems `IIMPSY`. -/
structure IimpsysParam (S I O : Type) where
  ImplState : Type
  ImplInput : Type
  ImplOutput : Type
  implemented : DiscreteSystem S I O
  implementing : DiscreteSystem ImplState ImplInput ImplOutput
  witness : IsomorphicallyImplements implemented implementing

/--
  [textbook/exercise5.178/plan/iimpsys_isSystemParameterization]
  `IIMPSY` returns the implemented system from an isomorphic-implementation parameter.
-/
def iimpsys (S I O : Type) :
    DiscreteSystemParameterization (IimpsysParam S I O)
      (fun _ => S) (fun _ => I) (fun _ => O) :=
  fun p => p.implemented

theorem iimpsys_eq {S I O : Type} (p : IimpsysParam S I O) :
    iimpsys S I O p = p.implemented :=
  rfl

theorem iimpsys_iff_isomorphicallyImplements
    {S I O S₂ I₂ O₂ : Type}
    (Z₁ : DiscreteSystem S I O) (Z₂ : DiscreteSystem S₂ I₂ O₂) :
    (∃ p : IimpsysParam S I O, p.implemented = Z₁ ∧ HEq p.implementing Z₂ ∧
      Nonempty (IsomorphicallyImplements Z₁ Z₂)) ↔
      Nonempty (IsomorphicallyImplements Z₁ Z₂) := by
  constructor
  · intro ⟨_, _, _, ⟨w⟩⟩
    exact ⟨w⟩
  · intro ⟨w⟩
    refine ⟨⟨S₂, I₂, O₂, Z₁, Z₂, w⟩, rfl, HEq.rfl, ⟨w⟩⟩

/--
Parameters for exact implementation systems `EIMPSY`.
Textbook 5.179 once says “isomorphically”; the charitable reading is **exactly**.
-/
structure EimpsysParam
    (S : Type) (Port OutPort : Type)
    (PV : Port → Type) (OV : OutPort → Type) where
  ImplState : Type
  ImplInput : Type
  ImplOutput : Type
  ModeState : Type
  ModePort : Type
  ModeOutPort : Type
  ModePV : ModePort → Type
  ModeOV : ModeOutPort → Type
  implemented : DiscreteSystem S ((p : Port) → PV p) ((q : OutPort) → OV q)
  implementing : DiscreteSystem ImplState ImplInput ImplOutput
  witness : @ExactlyImplements S ImplState ModeState Port ModePort OutPort ModeOutPort
    PV ModePV OV ModeOV ImplInput ImplOutput implemented implementing

/--
  [textbook/exercise5.179/plan/eimpsys_isSystemParameterization]
  `EIMPSY` returns the implemented system from an exact-implementation parameter.
-/
def eimpsys (S : Type) (Port OutPort : Type)
    (PV : Port → Type) (OV : OutPort → Type) :
    DiscreteSystemParameterization (EimpsysParam S Port OutPort PV OV)
      (fun _ => S) (fun _ => (p : Port) → PV p) (fun _ => (q : OutPort) → OV q) :=
  fun p => p.implemented

theorem eimpsys_eq {S : Type} {Port OutPort : Type}
    {PV : Port → Type} {OV : OutPort → Type}
    (p : EimpsysParam S Port OutPort PV OV) :
    eimpsys S Port OutPort PV OV p = p.implemented :=
  rfl

end WymoreImplementation
