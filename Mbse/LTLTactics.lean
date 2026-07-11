import Mbse.WymorePropertyFragment
import Mbse.FSMProperties
import Mbse.SystemToLTL
import Mbse.PartialDynamicsHomFragment
import Mbse.HomSearch
import Mbse.PhiChecker
import Mbse.Homomorphism

/-!
# LTL / partial-dynamics proof tactics

Pattern census (2026-07-06): clause-satisfaction and dynamics-table membership
proofs dominate [`WymorePropertyFragment`](WymorePropertyFragment.lean) line count.
These macros and lemma aliases reduce repeated `simp`/`rcases` boilerplate.

Also provides `assertional_fc` / `hom_from_phi` sugar for finite verification.
-/

open Lean Parser Tactic WymorePropertyFragment PropertyFragment.FSM
  PartialDynamicsHomFragment HomSearch PhiChecker Homomorphism

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

/-- Close a goal `SystemSatisfiesPartialDynamicsHom _ _` from an `IsHomomorphicImage` hypothesis. -/
syntax (name := assertionalFc) "assertional_fc" : tactic

macro_rules
  | `(tactic| assertional_fc) =>
    `(tactic| exact partialDynamicsHom_of_hom (by assumption))

/-- Close `IsHomomorphicImage` from `SystemSatisfiesPartialDynamicsHom` via the bi-implication. -/
syntax (name := homFromPhi) "hom_from_phi" : tactic

macro_rules
  | `(tactic| hom_from_phi) =>
    `(tactic| exact partialDynamicsHom_iff_hom.mp (by assumption))

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

/-- Lemma form of finite search completeness for tactic scripts. -/
theorem hom_search_complete_of_hom [Fintype SZ1] [Fintype IZ1] [Fintype OZ1]
    [Fintype SZ2] [Fintype IZ2] [Fintype OZ2]
    [DecidableEq SZ1] [DecidableEq IZ1] [DecidableEq OZ1]
    [DecidableEq SZ2] [DecidableEq IZ2] [DecidableEq OZ2]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    (searchHom Z_spec Z_impl).isSome = true :=
  searchHom_complete Z_spec Z_impl h
