import Mbse.FOLTL

/-!
# Compiling Wymore `DiscreteSystem` to FO-LTL

Maps a discrete system and initial state to a formula whose satisfaction matches
Wymore execution semantics (`generateStateTrajectory`, `IsValidStateTrajectory`).

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
