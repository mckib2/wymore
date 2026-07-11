import Mbse.WymorePropertyFragment
import Mbse.PartialDynamicsHomFragment
import Mbse.TemporalLogic
import Mbse.Homomorphism
import Mbse.Wymore
import Mathlib.Data.Real.Basic

/-!
# Bounded-horizon unrolling of Φ_dyn

Finite-prefix obligations for dynamics-encoding clauses. A violation on a bounded
unrolling is a sound counterexample to full semantic Φ_dyn satisfaction.
Completeness holds only under an explicit horizon bound (not claimed in general).
-/

namespace BoundedUnrolling

open TemporalLogic WymorePropertyFragment Homomorphism

variable {SZ IZ OZ : Type}

/-- State/readout agreement of `Z_impl` with `Z_spec` on a finite time horizon. -/
def PrefixedPartialExtEqual (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (N : Time) : Prop :=
  ∀ t : Time, t ≤ N →
    _root_.generateStateTrajectory Z_impl s0 f t =
      _root_.generateStateTrajectory Z_spec s0 f t ∧
      Z_impl.RZ (_root_.generateStateTrajectory Z_impl s0 f t) =
        Z_spec.RZ (_root_.generateStateTrajectory Z_spec s0 f t)

/-- Full pointwise dynamics agreement implies every finite prefix agrees. -/
theorem partialExtEqual_implies_prefixed {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : PartialExtEqual Z_spec Z_impl) (s0 : SZ) (f : ITZW IZ) (N : Time) :
    PrefixedPartialExtEqual Z_spec Z_impl s0 f N := by
  intro t _
  have htraj : ∀ τ, _root_.generateStateTrajectory Z_impl s0 f τ =
      _root_.generateStateTrajectory Z_spec s0 f τ := by
    intro τ
    induction τ with
    | zero => rfl
    | succ τ ih =>
      simp [_root_.generateStateTrajectory_succ, ih, h.2]
  refine ⟨htraj t, ?_⟩
  rw [htraj t, h.1]

/-- Soundness of counterexamples: if some prefix disagrees, systems are not ext-equal. -/
theorem prefixed_violation_refutes_extEqual {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (s0 : SZ) (f : ITZW IZ) (N : Time)
    (hViol : ¬ PrefixedPartialExtEqual Z_spec Z_impl s0 f N) :
    ¬ PartialExtEqual Z_spec Z_impl := by
  intro hExt
  exact hViol (partialExtEqual_implies_prefixed hExt s0 f N)

/-- Same-type: prefix violation refutes fixed-table Φ satisfaction. -/
theorem prefixed_violation_refutes_partialOpen [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (s0 : SZ) (f : ITZW IZ) (N : Time)
    (hViol : ¬ PrefixedPartialExtEqual Z_spec Z_impl s0 f N) :
    ¬ SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl := by
  intro hOpen
  have hExt := partialDynamicsOpen_iff_extEqual.mp hOpen
  exact prefixed_violation_refutes_extEqual s0 f N hViol hExt

/-- Bounded step-law check at a single state (static Def.~4.3 slice). -/
def StaticHomLawsAt {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) (x : SZ2) : Prop :=
  (Z_impl.RZ x).map HO = Z_spec.RZ (HS x) ∧
    ∀ oi, HS (Z_impl.NZ x oi) = Z_spec.NZ (HS x) (oi.map HI)

/-- Finite-state static law violation at `x` refutes homomorphism for those maps. -/
theorem static_violation_refutes_maps {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1) (x : SZ2)
    (hViol : ¬ StaticHomLawsAt Z_spec Z_impl HS HI HO x) :
    ¬ ((∀ y, (Z_impl.RZ y).map HO = Z_spec.RZ (HS y)) ∧
        (∀ y oi, HS (Z_impl.NZ y oi) = Z_spec.NZ (HS y) (oi.map HI))) := by
  intro ⟨hR, hN⟩
  exact hViol ⟨hR x, fun oi => hN x oi⟩

/-- Package surjective maps with universal static laws into a Def.~4.3 witness. -/
theorem staticHomLaws_mkWitness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hS : Function.Surjective HS) (hI : Function.Surjective HI) (hO : Function.Surjective HO)
    (hLaws : ∀ x, StaticHomLawsAt Z_spec Z_impl HS HI HO x) :
    IsHomomorphicImage Z_spec Z_impl :=
  ⟨{
    HS := HS, HI := HI, HO := HO
    HS_surjective := hS, HI_surjective := hI, HO_surjective := hO
    preserves_readout := fun x => (hLaws x).1
    preserves_transition := fun x oi => (hLaws x).2 oi
  }⟩

/-- Real-accumulator schema: bounded input class obligation (exact `ℝ`, not float). -/
def BoundedRealInput (bound : ℝ) (f : ITZW ℝ) : Prop :=
  ∀ t, ∀ u, f t = some u → |u| ≤ bound

theorem boundedRealInput_example (f : ITZW ℝ) (h : ∀ t, f t = none) :
    BoundedRealInput 1 f := by
  intro t u hu
  simp [h t] at hu

end BoundedUnrolling
