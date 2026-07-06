import Mbse.FOLTL

/-!
# Compiling Wymore `DiscreteSystem` to FO-LTL

Maps a discrete system and initial state to a formula whose satisfaction matches
Wymore execution semantics (`generateStateTrajectory`, `IsValidStateTrajectory`).

FO assertional layers:
- **Execution FO** (`compileSystemFO`): Link A vehicle; full iff with `IsWymoreExecution`.
- **Assertional FO** (`compileAssertionalFO`): execution FO plus spec-relative `stateLaw`
  bundles for pointwise `RZ`/`NZ` agreement (`compileExtensionalLaws`).

The compiler and `SatisfiesFO` interpreter are **separate**; equivalence is proved below.
-/

namespace SystemToFormula

open FOLTL

/-- Parametric Wymore execution: initial state, valid recurrence, valid readout. -/
def IsWymoreExecution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) : Prop :=
  g 0 = s0 ∧
  IsValidStateTrajectory Z f g ∧
  IsValidOutputTrajectory Z g y

/-- Initial-state constraint. -/
def compileInit {SZ IZ OZ : Type} (s0 : SZ) : FOLFormula SZ IZ OZ :=
  .init s0

/-- Tick-wise next-state recurrence (`NZ`). -/
def compileStep {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .step Z

/-- Tick-wise readout (`RZ`). -/
def compileReadout {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .readout Z

/-- Full execution formula for fixed initial state `s0`. -/
def compileSystemFO {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) :
    FOLFormula SZ IZ OZ :=
  .and (.init s0) (.and (.step Z) (.readout Z))

/-- Spec-relative extensional laws as state-space `stateLaw` bundles. -/
def compileExtensionalLaws {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .and
    (.stateLaw fun s => Z_impl.RZ s = Z_spec.RZ s)
    (.stateLaw fun s => ∀ oi, Z_impl.NZ s oi = Z_spec.NZ s oi)

/-- Assertional readout/dynamics invariants relative to a reference system. -/
abbrev compileReadoutInv {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  compileExtensionalLaws Z_spec Z_impl

/-- Execution FO plus spec-relative extensional state laws. -/
def compileAssertionalFO {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) (s0 : SZ) : FOLFormula SZ IZ OZ :=
  .and (compileSystemFO Z_spec s0) (compileExtensionalLaws Z_spec Z_impl)

/-- Open readout clause: spec `some o` implies impl `some o`. -/
def compilePartialReadoutOpenLaw {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .stateLaw fun s => ∀ o, Z_spec.RZ s = some o → Z_impl.RZ s = some o

/-- Closed readout clause: spec `none` implies impl `none`. -/
def compilePartialReadoutClosedLaw {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .stateLaw fun s => Z_spec.RZ s = none → Z_impl.RZ s = none

/-- Autonomous input clause: agreement at `NZ s none`. -/
def compilePartialAutonomousLaw {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .stateLaw fun s => Z_impl.NZ s none = Z_spec.NZ s none

/-- Transition clause: agreement at `NZ s (some i)` for all inputs `i`. -/
def compilePartialTransitionLaw {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .stateLaw fun s => ∀ i, Z_impl.NZ s (some i) = Z_spec.NZ s (some i)

/-- Four-clause partial-open laws (includes transition when inputs are nonempty). -/
def compilePartialAssertionalLawsCore {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .and (compilePartialReadoutOpenLaw Z_spec Z_impl)
    (.and (compilePartialReadoutClosedLaw Z_spec Z_impl)
      (.and (compilePartialAutonomousLaw Z_spec Z_impl)
        (compilePartialTransitionLaw Z_spec Z_impl)))

/-- Readout + autonomous laws only (empty input alphabet). -/
def compilePartialAssertionalLawsNoTransition {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ :=
  .and (compilePartialReadoutOpenLaw Z_spec Z_impl)
    (.and (compilePartialReadoutClosedLaw Z_spec Z_impl)
      (compilePartialAutonomousLaw Z_spec Z_impl))

/-- Spec-relative partial-open laws as four guarded `stateLaw` bundles.

Implication-shaped readout and split `NZ` laws mirror [`PartialDynamicsOpenCompile`]
clause shapes in `WymorePropertyFragment`. When `IZ` is empty, the transition bundle
is omitted (matching compiled LTL satisfaction). -/
noncomputable def compilePartialAssertionalLaws {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) : FOLFormula SZ IZ OZ := by
  classical
  by_cases _h : Nonempty IZ
  · exact compilePartialAssertionalLawsCore Z_spec Z_impl
  · exact compilePartialAssertionalLawsNoTransition Z_spec Z_impl

/-- Partial-open assertional FO: execution plus guarded readout and dynamics laws. -/
noncomputable def compilePartialAssertionalFO {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) (s0 : SZ) : FOLFormula SZ IZ OZ :=
  .and (compileSystemFO Z_spec s0) (compilePartialAssertionalLaws Z_spec Z_impl)

/-- Impl satisfies spec-side partial assertional FO at `(s0, f)`. -/
def SystemSatisfiesSpecPartialAssertionalFOAt {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : Prop :=
  SatisfiesFO (compilePartialAssertionalFO Z_spec Z_impl s0) Z_impl s0 f
    (generateStateTrajectory Z_impl s0 f)
    (generateOutputTrajectory Z_impl s0 f)

/-- Existential formula: some initial state and input trajectory satisfy execution constraints. -/
def compileAnyExecution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    FOLFormula SZ IZ OZ :=
  .existsState fun s0 => .existsInput fun _f => compileSystemFO Z s0

@[simp]
theorem satisfiesFO_compileInit {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 s0' : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileInit s0') Z s0 f g y ↔ g 0 = s0' := by
  simp [compileInit, SatisfiesFO]

@[simp]
theorem satisfiesFO_compileStep {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileStep Z) Z s0 f g y ↔ IsValidStateTrajectory Z f g := by
  simp [compileStep, SatisfiesFO]

@[simp]
theorem satisfiesFO_compileReadout {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileReadout Z) Z s0 f g y ↔ IsValidOutputTrajectory Z g y := by
  simp [compileReadout, SatisfiesFO]

@[simp]
theorem satisfiesFO_compileSystemFO {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileSystemFO Z s0) Z s0 f g y ↔ IsWymoreExecution Z s0 f g y := by
  simp [compileSystemFO, IsWymoreExecution, SatisfiesFO]

@[simp]
theorem satisfiesFO_compileExtensionalLaws {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileExtensionalLaws Z_spec Z_impl) Z_impl s0 f g y ↔
      (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧
        (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  simp only [compileExtensionalLaws, SatisfiesFO]

@[simp]
theorem satisfiesFO_compileAssertionalFO {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileAssertionalFO Z_spec Z_impl s0) Z_impl s0 f g y ↔
      IsWymoreExecution Z_spec s0 f g y ∧
        (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧
          (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  simp only [compileAssertionalFO, SatisfiesFO, IsWymoreExecution, satisfiesFO_compileExtensionalLaws]
  constructor
  · rintro ⟨hExec, hLaws⟩
    exact ⟨(satisfiesFO_compileSystemFO Z_spec s0 f g y).mp hExec, hLaws⟩
  · rintro ⟨hExec, hLaws⟩
    exact ⟨(satisfiesFO_compileSystemFO Z_spec s0 f g y).mpr hExec, hLaws⟩

/-- Open + closed readout implication bundles ↔ pointwise `RZ` agreement. -/
theorem partialReadoutGuardedPair_iff {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    (∀ s o, Z_spec.RZ s = some o → Z_impl.RZ s = some o) ∧
      (∀ s, Z_spec.RZ s = none → Z_impl.RZ s = none) ↔
      (∀ s, Z_impl.RZ s = Z_spec.RZ s) := by
  constructor
  · intro ⟨hOpen, hClosed⟩ s
    cases eq : Z_spec.RZ s with
    | none => exact eq ▸ hClosed s eq
    | some o => exact eq ▸ hOpen s o eq
  · intro h
    refine ⟨fun s o heq => (h s).trans heq, fun s heq => (h s).trans heq⟩

/-- Autonomous + transition `NZ` bundles ↔ pointwise `NZ` agreement on all `Option IZ`. -/
theorem partialNZGuardedPair_iff {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    (∀ s, Z_impl.NZ s none = Z_spec.NZ s none) ∧
      (∀ s i, Z_impl.NZ s (some i) = Z_spec.NZ s (some i)) ↔
      (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  constructor
  · intro ⟨hAuto, hTrans⟩ s oi
    cases oi with
    | none => exact hAuto s
    | some i => exact hTrans s i
  · intro h
    refine ⟨fun s => h s none, fun s i => h s (some i)⟩

theorem partialAssertionalLawsCore_iff {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compilePartialAssertionalLawsCore Z_spec Z_impl) Z_impl s0 f g y ↔
      (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧
        (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  simp only [compilePartialAssertionalLawsCore, compilePartialReadoutOpenLaw,
    compilePartialReadoutClosedLaw, compilePartialAutonomousLaw, compilePartialTransitionLaw,
    SatisfiesFO]
  constructor
  · intro ⟨hOpen, hClosed, hAuto, hTrans⟩
    exact ⟨partialReadoutGuardedPair_iff.mp ⟨hOpen, hClosed⟩, partialNZGuardedPair_iff.mp ⟨hAuto, hTrans⟩⟩
  · intro ⟨hR, hN⟩
    rcases partialReadoutGuardedPair_iff.mpr hR with ⟨hOpen, hClosed⟩
    rcases partialNZGuardedPair_iff.mpr hN with ⟨hAuto, hTrans⟩
    exact ⟨hOpen, hClosed, hAuto, hTrans⟩

theorem partialAssertionalLawsNoTransition_iff {SZ IZ OZ : Type} [IsEmpty IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compilePartialAssertionalLawsNoTransition Z_spec Z_impl) Z_impl s0 f g y ↔
      (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧
        (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  simp only [compilePartialAssertionalLawsNoTransition, compilePartialReadoutOpenLaw,
    compilePartialReadoutClosedLaw, compilePartialAutonomousLaw, SatisfiesFO]
  constructor
  · intro ⟨hOpen, hClosed, hAuto⟩
    refine ⟨partialReadoutGuardedPair_iff.mp ⟨hOpen, hClosed⟩, fun s oi => ?_⟩
    cases oi with
    | none => exact hAuto s
    | some i => exact False.elim (IsEmpty.false i)
  · intro ⟨hR, hN⟩
    rcases partialReadoutGuardedPair_iff.mpr hR with ⟨hOpen, hClosed⟩
    exact ⟨hOpen, hClosed, fun s => hN s none⟩

theorem partialAssertionalLaws_iff {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compilePartialAssertionalLaws Z_spec Z_impl) Z_impl s0 f g y ↔
      (∀ s, Z_impl.RZ s = Z_spec.RZ s) ∧
        (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi) := by
  classical
  unfold compilePartialAssertionalLaws
  split_ifs with hne
  · exact partialAssertionalLawsCore_iff (Z_spec := Z_spec) (Z_impl := Z_impl) s0 f g y
  · haveI : IsEmpty IZ := ⟨fun x => hne ⟨x⟩⟩
    exact partialAssertionalLawsNoTransition_iff (Z_spec := Z_spec) (Z_impl := Z_impl) s0 f g y

/-- Impl satisfies spec-side assertional FO at `(s0, f)` on canonical impl trajectories. -/
def SystemSatisfiesSpecAssertionalFOAt {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) : Prop :=
  SatisfiesFO (compileAssertionalFO Z_spec Z_impl s0) Z_impl s0 f
    (generateStateTrajectory Z_impl s0 f)
    (generateOutputTrajectory Z_impl s0 f)

/-- Canonical trajectories satisfy the compiled formula. -/
theorem canonical_execution_satisfies {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) :
    SatisfiesFO (compileSystemFO Z s0) Z s0 f
      (generateStateTrajectory Z s0 f)
      (generateOutputTrajectory Z s0 f) := by
  simp [satisfiesFO_compileSystemFO, IsWymoreExecution,
    generateStateTrajectory_zero, generateStateTrajectory_valid,
    generateOutputTrajectory_valid]

/-- Valid execution trajectories satisfy the compiled formula. -/
theorem wymore_execution_satisfies {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ)
    (h : IsWymoreExecution Z s0 f g y) :
    SatisfiesFO (compileSystemFO Z s0) Z s0 f g y :=
  (satisfiesFO_compileSystemFO Z s0 f g y).mpr h

/-- If trajectories satisfy the compiled formula, they are Wymore executions. -/
theorem satisfies_wymore_execution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ)
    (h : SatisfiesFO (compileSystemFO Z s0) Z s0 f g y) :
    IsWymoreExecution Z s0 f g y :=
  (satisfiesFO_compileSystemFO Z s0 f g y).mp h

/-- Bi-implication: Wymore execution ↔ satisfaction of compiled FO-LTL formula. -/
theorem execution_iff_satisfies {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    IsWymoreExecution Z s0 f g y ↔
      SatisfiesFO (compileSystemFO Z s0) Z s0 f g y :=
  satisfiesFO_compileSystemFO Z s0 f g y

/-- Valid execution implies agreement with canonical state trajectory. -/
theorem wymore_execution_state_eq_canonical {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ)
    (h : IsWymoreExecution Z s0 f g y) :
    ∀ t, g t = generateStateTrajectory Z s0 f t :=
  stateTrajectory_unique Z f g s0 h.1 h.2.1

/-- Valid execution implies agreement with canonical output trajectory. -/
theorem wymore_execution_output_eq_canonical {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ)
    (h : IsWymoreExecution Z s0 f g y) :
    ∀ t, y t = generateOutputTrajectory Z s0 f t := by
  intro t
  rw [generateOutputTrajectory_val, h.2.2 t, wymore_execution_state_eq_canonical Z s0 f g y h t]

/-- Canonical trajectories form a Wymore execution. -/
theorem canonical_is_wymore_execution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) :
    IsWymoreExecution Z s0 f
      (generateStateTrajectory Z s0 f)
      (generateOutputTrajectory Z s0 f) := by
  simp [IsWymoreExecution, generateStateTrajectory_zero,
    generateStateTrajectory_valid, generateOutputTrajectory_valid]

/-- Some execution exists iff the existential compiled formula is satisfiable. -/
theorem exists_execution_iff_satisfiesAny {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    (∃ s0 f g y, IsWymoreExecution Z s0 f g y) ↔
      ∃ s0 f,
        SatisfiesFO (compileSystemFO Z s0) Z s0 f
          (generateStateTrajectory Z s0 f)
          (generateOutputTrajectory Z s0 f) := by
  constructor
  · rintro ⟨s0, f, _, _, _⟩
    exact ⟨s0, f, canonical_execution_satisfies Z s0 f⟩
  · rintro ⟨s0, f, _⟩
    refine ⟨s0, f, generateStateTrajectory Z s0 f, generateOutputTrajectory Z s0 f, ?_⟩
    exact canonical_is_wymore_execution Z s0 f

theorem exists_execution_satisfiesAny {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    [Nonempty SZ] :
    ∃ s0 f,
      SatisfiesFO (compileSystemFO Z s0) Z s0 f
        (generateStateTrajectory Z s0 f)
        (generateOutputTrajectory Z s0 f) := by
  refine ⟨Classical.arbitrary SZ, fun _ => none, ?_⟩
  exact canonical_execution_satisfies Z _ _

theorem satisfiesFO_compileAnyExecution {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) :
    SatisfiesFO (compileAnyExecution Z) Z s0 f g y ↔
      ∃ s0' f', SatisfiesFO (compileSystemFO Z s0') Z s0' f' g y := by
  simp [compileAnyExecution, SatisfiesFO]

theorem exists_execution_iff_compileAny {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    (∃ s0 f g y, IsWymoreExecution Z s0 f g y) ↔
      ∃ s0 f g y, SatisfiesFO (compileAnyExecution Z) Z s0 f g y := by
  constructor
  · rintro ⟨s0, f, g, y, h⟩
    refine ⟨s0, f, g, y, ?_⟩
    simp only [compileAnyExecution, SatisfiesFO]
    refine ⟨s0, ⟨f, (satisfiesFO_compileSystemFO Z s0 f g y).mpr h⟩⟩
  · rintro ⟨s0, f, g, y, h⟩
    simp only [compileAnyExecution, SatisfiesFO] at h
    rcases h with ⟨s0', ⟨f', h'⟩⟩
    refine ⟨s0', f', g, y, (satisfiesFO_compileSystemFO Z s0' f' g y).mp h'⟩

/-! ### `ofTotal` / toggle example -/

theorem toggle_canonical_satisfies (s0 : Bool) (f : ITZW Empty) :
    SatisfiesFO (compileSystemFO toggleSystem s0) toggleSystem s0 f
      (generateStateTrajectory toggleSystem s0 f)
      (generateOutputTrajectory toggleSystem s0 f) :=
  canonical_execution_satisfies toggleSystem s0 f

end SystemToFormula
