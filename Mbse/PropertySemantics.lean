import Mbse.Homomorphism
import Mbse.TemporalLogic

/-!
# Property semantics for Wymore systems

Links temporal-logic property sets to Wymore `DiscreteSystem` satisfaction and
homomorphic-image verification. Assertional properties are evaluated on **homomorphism-visible**
trajectory data (state/input/output exposed by `HS`, `HI`, `HO`).

Execution dynamics are handled separately in [`SystemToFormula`](SystemToFormula.lean).
-/

namespace PropertySemantics

open TemporalLogic

variable {SZ IZ OZ AP : Type}

/-- A finite property set in a chosen temporal-logic fragment. -/
structure PropertySet (φ : Type) where
  formulas : List φ

/-- Default admissible input class: all input trajectories. -/
def AllInputs : ITZW IZ → Prop :=
  fun _ => True

/-- Homomorphism-visible observation at one tick. -/
structure VisibleObs (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (t : Time) where
  state : SZ := generateStateTrajectory Z s0 f t
  input : Option IZ := f t
  output : Option OZ := generateOutputTrajectory Z s0 f t

/-- Project an implementation-side observation through a homomorphic-image witness. -/
def projectObs {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    VisibleObs Z_spec (h.HS s0) (fun τ => (f τ).map h.HI) t where
  state := h.HS (generateStateTrajectory Z_impl s0 f t)
  input := (f t).map h.HI
  output := (generateOutputTrajectory Z_impl s0 f t).map h.HO

theorem projectObs_state {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    (projectObs h s0 f t).state = h.HS (generateStateTrajectory Z_impl s0 f t) := rfl

theorem projectObs_output {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) (t : Time) :
    (projectObs h s0 f t).output = (generateOutputTrajectory Z_impl s0 f t).map h.HO :=
  rfl

/-- `Z` satisfies every formula in `Phi` for initial state `s0` and admissible inputs. -/
def SystemSatisfiesLTL (Z : DiscreteSystem SZ IZ OZ) (Phi : PropertySet (LTL AP))
    (s0 : SZ) (traceOf : ITZW IZ → Trace AP)
    (Adm : ITZW IZ → Prop := AllInputs) : Prop :=
  ∀ (f : ITZW IZ), Adm f → ∀ φ, φ ∈ Phi.formulas → (traceOf f).models φ

/-- Every initial state and admissible input satisfies all formulas. -/
def SystemSatisfiesLTLAll (Z : DiscreteSystem SZ IZ OZ) (Phi : PropertySet (LTL AP))
    (traceOf : SZ → ITZW IZ → Trace AP)
    (Adm : ITZW IZ → Prop := AllInputs) : Prop :=
  ∀ (s0 : SZ) (f : ITZW IZ), Adm f → ∀ φ, φ ∈ Phi.formulas → (traceOf s0 f).models φ

abbrev HasHomomorphism {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  Homomorphism.IsHomomorphicImage Z_spec Z_impl

/-- `Z_spec` is Φ-adequate when it satisfies Φ and matches canonical synthesis. -/
def PhiAdequateSpec (satisfies : Prop) (canonical : Prop) : Prop :=
  satisfies ∧ canonical

end PropertySemantics
