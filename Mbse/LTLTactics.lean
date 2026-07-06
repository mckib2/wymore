import Mbse.WymorePropertyFragment
import Mbse.FSMProperties
import Mbse.SystemToLTL

/-!
# LTL / partial-dynamics proof tactics

Pattern census (2026-07-06): clause-satisfaction and dynamics-table membership
proofs dominate [`WymorePropertyFragment`](WymorePropertyFragment.lean) line count.
These macros and lemma aliases reduce repeated `simp`/`rcases` boilerplate.
-/

open Lean Parser Tactic WymorePropertyFragment PropertyFragment.FSM

/-- Case-split membership in FSM dynamics table (transition vs readout clause). -/
syntax (name := fsmDynamicsMemCases) "fsm_dynamics_mem_cases" : tactic

macro_rules
  | `(tactic| fsm_dynamics_mem_cases) =>
    `(tactic| rw [mem_fsmDynamicsTable_iff]; rcases h with h | h)

/-- Case-split membership in partial dynamics table (readout/autonomous/transition). -/
syntax (name := partialDynamicsMemCases) "partial_dynamics_mem_cases" : tactic

macro_rules
  | `(tactic| partial_dynamics_mem_cases) =>
    `(tactic| dsimp [partialDynamicsTable] at *; rw [List.mem_append] at *; rcases h with h | h | h)

theorem trace_models_partialReadout_tac {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (s : SZ) (o : OZ) (hR : Z.RZ s = some o) :
    (wymoreTrace Z s0 f).models (partialReadoutClause Z s o) :=
  wymoreTrace_satisfies_partialReadout Z s0 f s o hR

theorem trace_models_partialTransition_tac {SZ IZ OZ : Type} [DecidableEq IZ]
    (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZW IZ) (s : SZ) (i : IZ) :
    (wymoreTrace Z s0 f).models (partialTransitionClause Z s i) :=
  wymoreTrace_models_partialTransition Z s0 f s i

theorem trace_models_partialAutonomous_tac {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZW IZ) (s : SZ) :
    (wymoreTrace Z s0 f).models (partialAutonomousClause Z s) :=
  wymoreTrace_models_partialAutonomous Z s0 f s

theorem trace_models_fsmTransition_tac {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZ IZ) (s : SZ) (i : IZ) :
    (fsmTrace F s0 f).models (SystemToLTL.transitionClause F s i) :=
  fsmTrace_models_transitionClause F s0 f s i

theorem trace_models_fsmReadout_tac {SZ IZ OZ : Type} (F : FSMSystem SZ IZ OZ)
    (s0 : SZ) (f : ITZ IZ) (s : SZ) :
    (fsmTrace F s0 f).models (SystemToLTL.readoutClause F s) :=
  fsmTrace_models_readoutClause F s0 f s
