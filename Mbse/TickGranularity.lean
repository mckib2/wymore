import Mbse.Isomorphism
import Mbse.PartialDynamicsHomFragment

/-!
# Wymore homomorphism admits no temporal abstraction

A Definition 4.3 homomorphism is lock-step: one tick of the implementation must correspond to one
tick of the reference.  An implementation that needs two ticks to accomplish what the reference does
in one therefore fails to realise it, however faithful it is otherwise.  This is not a defect of the
compiled fragment but a property of the conformance relation the fragment characterises, and it is
what a systems engineer must know before writing a reference table: **the reference has to be stated
at the granularity of the build**.

The witness is deliberately minimal:

* `flipRef` — a one-bit register that flips on every tick.
* `flipImpl` — the same register with a sense/act phase, so it flips on every *second* tick.

`no_hom_flip` proves that no state, input and output map at all makes `flipImpl` a realisation of
`flipRef`, and `flip_fragment_fails` restates this as failure of the compiled fragment: a solver
handed this pair returns UNSAT, correctly.

`stretchedRef` then shows the remedy.  Re-stating the reference at two ticks per logical step
restores conformance, with an isomorphism rather than a mere homomorphism.  Nothing about the
implementation changes.
-/

namespace TickGranularity

open Homomorphism PartialDynamicsHomFragment

/-- The reference: a bit that flips on every tick. -/
def flipRef : DiscreteSystem Bool Unit Bool where
  sz_nonempty := ⟨false⟩
  NZ s
    | none => s
    | some _ => !s
  RZ s := some s

/-- The phase of the two-tick implementation. -/
inductive Phase
  | sense
  | act
  deriving DecidableEq, Repr

/--
The implementation: it holds the same bit but takes a sense tick and an act tick to flip it, so its
observable value changes only every second tick.
-/
def flipImpl : DiscreteSystem (Bool × Phase) Unit Bool where
  sz_nonempty := ⟨(false, .sense)⟩
  NZ vp
    | none => vp
    | some _ =>
        match vp.2 with
        | .sense => (vp.1, .act)
        | .act => (!vp.1, .sense)
  RZ vp := some vp.1

/--
No Wymore homomorphism realises the one-tick reference by the two-tick implementation.

The argument needs no search.  Readout preservation forces the state map to factor through the bit,
`HS (v, p) = HO v`, so it cannot distinguish the sense phase from the act phase.  But on a sense
tick the implementation keeps its bit while the reference must flip, so `HO v = !(HO v)`.
-/
theorem no_hom_flip : ¬ IsHomomorphicImage flipRef flipImpl := by
  rintro ⟨w⟩
  have hread : ∀ vp : Bool × Phase, w.HS vp = w.HO vp.1 := by
    intro vp
    exact (Option.some.inj (w.preserves_readout vp)).symm
  have hstep : w.HS (false, Phase.act) = ! w.HS (false, Phase.sense) :=
    w.preserves_transition (false, Phase.sense) (some ())
  rw [hread (false, Phase.act), hread (false, Phase.sense)] at hstep
  exact (Bool.not_ne_self (w.HO false)) hstep.symm

/-- Equivalently: the fragment compiled from the reference is *not* satisfied by the build. -/
theorem flip_fragment_fails : ¬ SystemSatisfiesPartialDynamicsHom flipRef flipImpl :=
  fun h => no_hom_flip (hom_of_partialDynamicsHom h)

/-! ## The remedy: state the reference at the granularity of the build -/

/-- The reference re-stated at two ticks per logical flip. -/
def stretchedRef : DiscreteSystem (Bool × Phase) Unit Bool where
  sz_nonempty := ⟨(false, .sense)⟩
  NZ vp
    | none => vp
    | some _ =>
        match vp.2 with
        | .sense => (vp.1, .act)
        | .act => (!vp.1, .sense)
  RZ vp := some vp.1

/-- At matched granularity the very same build is a realisation, and indeed an isomorph. -/
def stretchedIso : IsomorphismWitness stretchedRef flipImpl where
  HS := _root_.id
  HI := _root_.id
  HO := _root_.id
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro vp oi
    cases oi with
    | none => rfl
    | some u => cases vp.2 <;> rfl
  preserves_readout := by
    intro vp
    rfl
  HS_injective := Function.injective_id
  HI_injective := Function.injective_id
  HO_injective := Function.injective_id

theorem stretchedRef_realised : IsHomomorphicImage stretchedRef flipImpl :=
  ⟨stretchedIso.toHomomorphicImageWitness⟩

theorem stretchedRef_fragment_holds :
    SystemSatisfiesPartialDynamicsHom stretchedRef flipImpl :=
  partialDynamicsHom_of_hom stretchedRef_realised

/--
The two facts together are the engineering content: the same build fails one reference and satisfies
another that differs only in tick granularity.  Conformance is therefore a statement about a
reference *and* a clock, and the fragment reports exactly that.
-/
theorem tick_granularity_matters :
    ¬ SystemSatisfiesPartialDynamicsHom flipRef flipImpl ∧
      SystemSatisfiesPartialDynamicsHom stretchedRef flipImpl :=
  ⟨flip_fragment_fails, stretchedRef_fragment_holds⟩

end TickGranularity
