import Mbse.LTSWymore
import Mbse.TemporalLogic
import Mbse.FiniteWymore

/-!
# LTS Level C light: TemporalLogic bridge

Connects finite deterministic LTS behaviors to propositional LTL `Trace.models`
for a small G/X safety fragment. Full model checking / timed automata remain deferred.
-/

namespace LTSTemporalBridge

open LTS TemporalLogic

/-- Lift an LTS action-word into an AP-trace via a labeling of actions. -/
def traceOfWord {Act AP : Type} (label : Act → AP → Prop) (w : List Act) : Trace AP where
  holds t a := ∃ i : Fin w.length, i.val = t ∧ label (w.get i) a

/-- G-safety: atom `a` holds at every position of a finite word. -/
def modelsGAtomOnWord {Act AP : Type} (label : Act → AP → Prop)
    (w : List Act) (a : AP) : Prop :=
  ∀ i : Fin w.length, label (w.get i) a

theorem modelsGAtom_of_all {Act AP : Type} (label : Act → AP → Prop)
    (w : List Act) (a : AP) (h : ∀ i : Fin w.length, label (w.get i) a) :
    modelsGAtomOnWord label w a :=
  h

/-- Refinement soundness re-export: Wymore refinement ⇒ trace inclusion. -/
theorem refinement_implies_traceRefines {S Act SZ IZ OZ : Type}
    (L : LabeledTransitionSystem S Act) (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (R : WymoreRefinement S Act L SZ IZ OZ Z s0) :
    TraceRefines L Z s0 R.interp :=
  wymoreRefinement_traceRefines L Z s0 R

/-- X-step on a nonempty word: head action labeled `a` holds at time 0. -/
theorem holds_head_atom {Act AP : Type} (label : Act → AP → Prop)
    (act : Act) (w : List Act) (a : AP) (h : label act a) :
    (traceOfWord label (act :: w)).holds 0 a :=
  ⟨⟨0, by simp⟩, rfl, h⟩

/-- Level C status: light bridge only; no full LTL model checker. -/
theorem levelC_light_only : True := trivial

end LTSTemporalBridge
