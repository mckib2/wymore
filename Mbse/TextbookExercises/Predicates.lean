import Mbse.FiniteWymore
import Mbse.Wymore

/-!
# Textbook exercise predicates

Shared predicates for curated Wymore textbook exercise solutions, linking
`RNG(NZ)` and `RNG(RZ)` to finite state/output spaces via `FSM.RNG`, and
general `DiscreteSystem` exercise properties.
-/

namespace Mbse.TextbookExercises

open FSM

variable {SZ IZ OZ : Type} [DecidableEq SZ] [DecidableEq OZ]

/-- Every input-driven step changes state: `NZ(x, p) ≠ x` for all `x` and `p`. -/
def alwaysActiveTransition (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (x : SZ) (p : IZ), Z.NZ x (some p) ≠ x

/--
  Intended reading of Exercise 2.118: for every *distinct* states and every input,
  the next state depends on the current state (`NZ(x1, p) ≠ NZ(x2, p)`).
  Links to Def 2.14 (i) but strengthened from existence to all distinct pairs.
-/
def pairwiseStateDependentTransition (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (x1 x2 : SZ) (p : IZ), x1 ≠ x2 → Z.NZ x1 (some p) ≠ Z.NZ x2 (some p)

/--
  Literal unpinned textbook quantification (∀ `x1`, `x2`, `p` without `x1 ≠ x2`).
  No discrete system can satisfy this: when `x1 = x2`, it requires `NZ(x,p) ≠ NZ(x,p)`.
-/
def literalUniversalNzDistinct (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ∀ (x1 x2 : SZ) (p : IZ), Z.NZ x1 (some p) ≠ Z.NZ x2 (some p)

omit [DecidableEq SZ] [DecidableEq OZ] in
theorem literalUniversalNzDistinct_impossible [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) :
    ¬ literalUniversalNzDistinct Z := by
  intro h
  rcases Z.sz_nonempty with ⟨x⟩
  have ⟨p⟩ : Nonempty IZ := inferInstance
  exact h x x p rfl

/-- The system state, input, and output spaces are not all finite (Def 2.11 negation). -/
def notFiniteSystem (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  ¬ IsFinite Z

/--
  [textbook/definition_a1.218/definition/range]
  Range of the next-state function `NZ` as a finset of states: `RNG(NZ) ⊆ SZ`.
-/
def transitionRange (Z : FSMSystem SZ IZ OZ) : Finset SZ :=
  have : Fintype SZ := Z.sz_finite
  have : Fintype IZ := Z.iz_finite
  FSM.RNG (fun p : SZ × IZ => Z.NZ p.1 p.2)

/--
  [textbook/definition_a1.218/definition/range]
  Range of the readout function `RZ` as a finset of outputs: `RNG(RZ) ⊆ OZ`.
-/
def readoutRange (Z : FSMSystem SZ IZ OZ) : Finset OZ :=
  have : Fintype SZ := Z.sz_finite
  FSM.RNG Z.RZ

/-- `RNG(NZ) = SZ` on finite `SZ` (encoded as `transitionRange Z = Finset.univ`). -/
def rngNzEqSz (Z : FSMSystem SZ IZ OZ) : Prop :=
  have : Fintype SZ := Z.sz_finite
  transitionRange Z = Finset.univ

/-- `RNG(NZ) ≠ SZ`. -/
def rngNzNeSz (Z : FSMSystem SZ IZ OZ) : Prop :=
  have : Fintype SZ := Z.sz_finite
  transitionRange Z ≠ Finset.univ

/-- `RNG(RZ) = OZ` on finite `OZ` (encoded as `readoutRange Z = Finset.univ`). -/
def rngRzEqOz (Z : FSMSystem SZ IZ OZ) : Prop :=
  have : Fintype OZ := Z.oz_finite
  readoutRange Z = Finset.univ

/-- `RNG(RZ) ≠ OZ`. -/
def rngRzNeOz (Z : FSMSystem SZ IZ OZ) : Prop :=
  have : Fintype OZ := Z.oz_finite
  readoutRange Z ≠ Finset.univ

end Mbse.TextbookExercises
