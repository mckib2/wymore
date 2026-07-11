import Mbse.Wymore

/-!
# Propositional Linear Temporal Logic (minimal syntax and semantics)

Satisfaction on infinite discrete-time traces. No model checking or automata — only
syntax (`LTL`) and semantics (`satisfiesAt`, `Trace.models`).

Propositional LTL applies only to **finite** atomic-proposition alphabets; see
[`SystemToLTL`](SystemToLTL.lean) for the `FSMSystem` encoding.
-/

namespace TemporalLogic

/-- Propositional LTL formulas over atomic proposition type `AP`. -/
inductive LTL (AP : Type) where
  | atom (a : AP)
  | top
  | bot
  | and (φ ψ : LTL AP)
  | or (φ ψ : LTL AP)
  | not (φ : LTL AP)
  | imp (φ ψ : LTL AP)
  | X (φ : LTL AP)
  | F (φ : LTL AP)
  | G (φ : LTL AP)
  | U (φ ψ : LTL AP)
  | R (φ ψ : LTL AP)

/-- An infinite trace: which atomic propositions hold at each tick. -/
structure Trace (AP : Type) where
  holds : Time → AP → Prop

@[ext]
theorem Trace.ext {AP : Type} {σ1 σ2 : Trace AP}
    (h : ∀ t a, σ1.holds t a ↔ σ2.holds t a) : σ1 = σ2 := by
  cases σ1
  cases σ2
  congr
  funext t a
  exact propext (h t a)

/-- Satisfaction of `φ` on trace `σ` at time `t`. -/
def satisfiesAt {AP : Type} : LTL AP → Trace AP → Time → Prop
  | .atom a, σ, t => σ.holds t a
  | .top, _, _ => True
  | .bot, _, _ => False
  | .and φ ψ, σ, t => satisfiesAt φ σ t ∧ satisfiesAt ψ σ t
  | .or φ ψ, σ, t => satisfiesAt φ σ t ∨ satisfiesAt ψ σ t
  | .not φ, σ, t => ¬ satisfiesAt φ σ t
  | .imp φ ψ, σ, t => satisfiesAt φ σ t → satisfiesAt ψ σ t
  | .X φ, σ, t => satisfiesAt φ σ (t + 1)
  | .F φ, σ, t => ∃ t', t ≤ t' ∧ satisfiesAt φ σ t'
  | .G φ, σ, t => ∀ t', t ≤ t' → satisfiesAt φ σ t'
  | .U φ ψ, σ, t => ∃ t', t ≤ t' ∧ satisfiesAt ψ σ t' ∧
      ∀ t'', t ≤ t'' → t'' < t' → satisfiesAt φ σ t''
  | .R φ ψ, σ, t => ∀ t', t ≤ t' →
      satisfiesAt ψ σ t' ∨ ∃ t'', t ≤ t'' ∧ t'' < t' ∧ satisfiesAt φ σ t''

/-- `σ` models `φ` from time zero (standard LTL semantics). -/
def Trace.models {AP : Type} (σ : Trace AP) (φ : LTL AP) : Prop :=
  satisfiesAt φ σ 0

/-! ### Negative tests (semantics is not vacuous) -/

theorem not_bot_at_zero {AP : Type} (σ : Trace AP) :
    ¬ satisfiesAt (LTL.bot : LTL AP) σ 0 := by
  simp [satisfiesAt]

theorem top_at_zero {AP : Type} (σ : Trace AP) :
    satisfiesAt (LTL.top : LTL AP) σ 0 := by
  simp [satisfiesAt]

theorem atom_iff_holds {AP : Type} (σ : Trace AP) (a : AP) (t : Time) :
    satisfiesAt (LTL.atom a) σ t ↔ σ.holds t a := by
  simp [satisfiesAt]

theorem G_atom_requires_all_times {AP : Type} (σ : Trace AP) (a : AP) (t : Time)
    (h : satisfiesAt (LTL.G (.atom a)) σ 0) :
    σ.holds t a := by
  have ht := h t (Nat.zero_le t)
  simpa [satisfiesAt] using ht

end TemporalLogic
