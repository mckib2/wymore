import Mbse.Wymore

/-!
# FO-LTL over Wymore trajectories (minimal fragment)

Formulas talk about state trajectory `g`, input trajectory `f`, and output trajectory `y`
at discrete ticks. This is **not** a full first-order theorem prover — only a syntax tree and
a proof-relevant interpreter `SatisfiesFO`.

The interpreter is separate from execution predicates in [`Wymore`](Wymore.lean); equivalence
is proved in [`SystemToFormula`](SystemToFormula.lean).
-/

namespace FOLTL

/-- Minimal FO-LTL fragment for Wymore execution constraints. -/
inductive FOLFormula (SZ IZ OZ : Type) where
  | init (s0 : SZ)
  | step (Z : DiscreteSystem SZ IZ OZ)
  | readout (Z : DiscreteSystem SZ IZ OZ)
  | and (φ ψ : FOLFormula SZ IZ OZ)
  | existsState (φ : SZ → FOLFormula SZ IZ OZ)
  | existsInput (φ : ITZW IZ → FOLFormula SZ IZ OZ)

/--
  Interpret a formula under concrete trajectories. Existential quantifiers range over
  initial states and input trajectories; `g` and `y` remain parameters (as in paper §3.2).
-/
def SatisfiesFO {SZ IZ OZ : Type} :
    FOLFormula SZ IZ OZ → DiscreteSystem SZ IZ OZ → SZ → ITZW IZ → STZ SZ → OTZ OZ → Prop
  | .init s0', _, _, _, g, _ =>
      g 0 = s0'
  | .step Z, _, _, f, g, _ =>
      IsValidStateTrajectory Z f g
  | .readout Z, _, _, _, g, y =>
      IsValidOutputTrajectory Z g y
  | .and φ ψ, Z, s0, f, g, y =>
      SatisfiesFO φ Z s0 f g y ∧ SatisfiesFO ψ Z s0 f g y
  | .existsState φ, Z, _, f, g, y =>
      ∃ s0' : SZ, SatisfiesFO (φ s0') Z s0' f g y
  | .existsInput φ, Z, s0, _, g, y =>
      ∃ f' : ITZW IZ, SatisfiesFO (φ f') Z s0 f' g y

/-! ### Negative tests -/

theorem init_not_satisfied_wrong_state {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 s0' : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ)
    (hne : s0 ≠ s0') (hinit : g 0 = s0) :
    ¬ SatisfiesFO (.init s0') Z s0 f g y := by
  intro h
  simp only [SatisfiesFO] at h
  rw [hinit] at h
  exact hne h

theorem step_not_satisfied_invalid_g {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (g : STZ SZ) (y : OTZ OZ) (t : Time)
    (hstep : g (t + 1) ≠ Z.NZ (g t) (f t)) :
    ¬ SatisfiesFO (.step Z) Z s0 f g y := by
  intro h
  have hvalid := h
  simp only [SatisfiesFO] at hvalid
  exact hstep (hvalid t)

end FOLTL
