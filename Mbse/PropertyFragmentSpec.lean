import Mbse.TemporalLogic
import Mbse.Wymore

/-!
# TL fragment grammar specification

Documents the assertional fragment Φ used for bi-implication theorems.
Restrictions are TL-side only; `DiscreteSystem` remains general.
-/

namespace PropertyFragmentSpec

open TemporalLogic

/-- Allowed connectives in the assertional fragment. -/
inductive AllowedConnective where
  | imp
  | andConn
  | GConn
  | XConn

/-- Disjunction policy for Φ. -/
inductive DisjunctionPolicy where
  | excluded
  | canonicalCommitment

/-- Eventually (`F`) policy — excluded from assertional fragment (Example 3). -/
inductive EventuallyPolicy where
  | excluded

/-- Homomorphism-visible atom kinds for finite dynamics tables. -/
inductive DynamicsAtomKind where
  | stateAtom
  | inputAtom
  | outputAtom

/-- Specification of the assertional TL fragment Φ. -/
structure FragmentSpec where
  allowedConnectives : List AllowedConnective
  disjunctionPolicy : DisjunctionPolicy
  eventuallyPolicy : EventuallyPolicy
  finiteClauseEnumeration : Bool
  dynamicsComplete : Bool
  homomorphismVisibleAtoms : List DynamicsAtomKind

/-- Fragment used in Stages 1–3 bi-implication theorems. -/
def pinnedFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

/-- Readout-only fragment (Stage 2 negative example — incomplete). -/
def readoutOnlyFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn]
  disjunctionPolicy := .excluded
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := true
  dynamicsComplete := false
  homomorphismVisibleAtoms := [.stateAtom, .outputAtom]

theorem pinnedFragment_no_F : pinnedFragment.eventuallyPolicy = .excluded := rfl

theorem pinnedFragment_dynamicsComplete : pinnedFragment.dynamicsComplete = true := rfl

theorem pinnedFragment_disjunctionCanonical :
    pinnedFragment.disjunctionPolicy = .canonicalCommitment := rfl

/-- Enumeration policy for clause tables. -/
inductive EnumerationPolicy where
  | finiteClauseList
  | predicateIndexed
  | foQuantified

/-- Fragment specification for Stages 1–3 (finite total open Moore via FSM embed). -/
def pinnedFiniteFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem pinnedFinite_eq_pinned : pinnedFiniteFragment = pinnedFragment := rfl

/-- Partial open: `Option` readout/input on general `DiscreteSystem`. -/
def partialOpenFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := true
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

/-- Partial open (predicate-indexed): infinite-capable assertional laws without `Fintype`.

Paired compile objects: LTL [`compileObservablesPartialOpen`] and FO
[`compileObservablesPartialAssertionalFO`] with proved satisfaction equivalence
(`compileObservablesPartial_schema`). FO laws use four guarded `stateLaw` bundles
mirroring the LTL clause shapes. -/
def partialOpenPredicateFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := false
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem partialOpenPredicate_no_finite_enum :
    partialOpenPredicateFragment.finiteClauseEnumeration = false := rfl

theorem partialOpenPredicate_dynamicsComplete :
    partialOpenPredicateFragment.dynamicsComplete = true := rfl

/-- FO assertional formulas (`FOLTL` + `stateLaw` extensional invariants); no finite enumeration. -/
def foAssertionalFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := false
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

/-- Extensional predicate-indexed dynamics; no finite state enumeration. -/
def extensionalDynamicsFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := false
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem extensionalDynamics_no_finite_enum :
    extensionalDynamicsFragment.finiteClauseEnumeration = false := rfl

theorem extensionalDynamics_dynamicsComplete :
    extensionalDynamicsFragment.dynamicsComplete = true := rfl

/-- LTS trace refinement (nondeterministic abstract specs). -/
def ltsRefinementFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn]
  disjunctionPolicy := .excluded
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := false
  dynamicsComplete := false
  homomorphismVisibleAtoms := [.inputAtom, .outputAtom]

theorem foAssertional_no_finite_enum : foAssertionalFragment.finiteClauseEnumeration = false := rfl

theorem partialOpen_dynamicsComplete : partialOpenFragment.dynamicsComplete = true := rfl

/-! ## Fragment side conditions (TL-side gates) -/

/-- Side conditions for pinned finite Stages 1–3 bi-implication. -/
structure PinnedFiniteSideConditions (SZ IZ OZ : Type) (Z : DiscreteSystem SZ IZ OZ) : Prop where
  alwaysOutputs : AlwaysOutputs Z
  sz_finite : Nonempty (Fintype SZ)
  iz_finite : Nonempty (Fintype IZ)
  oz_finite : Nonempty (Fintype OZ)

/-- Side conditions for partial-open clause tables.

Readout-completeness (`ReadoutSpecComplete`) and dynamics-completeness (`DynamicsSpecComplete`
in `WymorePropertyFragment`) replace `AlwaysOutputs` when closed readout or autonomous-input
states need explicit clauses. On arbitrary `SZ`, use `ReadoutSpecCompleteOpen` /
`DynamicsSpecCompleteOpen` with `SystemSatisfiesPartialDynamicsOpen`. -/
structure PartialOpenSideConditions (SZ IZ OZ : Type) (Z : DiscreteSystem SZ IZ OZ) : Prop where
  sz_finite : Nonempty (Fintype SZ)
  iz_finite : Nonempty (Fintype IZ)
  dynamicsComplete : partialOpenFragment.dynamicsComplete = true

theorem partialOpenSideConditions_dynamics {SZ IZ OZ : Type} {Z : DiscreteSystem SZ IZ OZ}
    (h : PartialOpenSideConditions SZ IZ OZ Z) :
    partialOpenFragment.dynamicsComplete = true :=
  h.dynamicsComplete

/-- Side conditions for extensional dynamics (arbitrary `SZ`; requires resolvable readout). -/
structure InfiniteOpenSideConditions (SZ IZ OZ : Type) (Z : DiscreteSystem SZ IZ OZ) : Prop where
  alwaysOutputs : AlwaysOutputs Z
  dynamicsComplete : extensionalDynamicsFragment.dynamicsComplete = true

theorem infiniteOpenSideConditions_dynamics {SZ IZ OZ : Type} {Z : DiscreteSystem SZ IZ OZ}
    (h : InfiniteOpenSideConditions SZ IZ OZ Z) :
    extensionalDynamicsFragment.dynamicsComplete = true :=
  h.dynamicsComplete

end PropertyFragmentSpec
