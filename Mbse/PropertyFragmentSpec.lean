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

/-- Eventually (`F`) policy for assertional fragments.
`excluded` — production Φ_dyn (paper default).
`entailedOnly` — optional conjuncts proved redundant given Φ_dyn (safe extension).
`restrictedBounded` — bounded `F≤k` / compiled progress schemas under exploration. -/
inductive EventuallyPolicy where
  | excluded
  | entailedOnly
  | restrictedBounded

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

/-- Partial open (predicate-indexed): shared fixed-table specialization when spec and impl
share `(S,I,O)` with literal impl-state atoms.

Paired compile objects: LTL [`compileObservablesPartialOpen`] and FO
[`compileObservablesPartialAssertionalFO`] with proved satisfaction equivalence
(`compileObservablesPartial_schema`). Collapses to the hom headline tier under partial
identity hom (`PartialDynamicsHomFragment.partialDynamicsHom_iff_open_of_identityHom`). -/
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

/-- Hom-relative partial dynamics (headline tier): surjective Def 4.3 hom, predicate-indexed
spec clauses.

Semantic satisfaction coincides with [`SystemSatisfiesExtensionalCross`]
(`PartialDynamicsHomFragment.partialDynamicsHom_eq_extensionalCross`). Primary Wymore FC
hom↔Φ bi-implication. The shared fixed-table tier (`partialOpenPredicateFragment`) is the
same-type identity specialization. -/
def partialHomPredicateFragment : FragmentSpec where
  allowedConnectives := [.imp, .GConn, .XConn]
  disjunctionPolicy := .canonicalCommitment
  eventuallyPolicy := .excluded
  finiteClauseEnumeration := false
  dynamicsComplete := true
  homomorphismVisibleAtoms := [.stateAtom, .inputAtom, .outputAtom]

theorem partialHomPredicate_no_finite_enum :
    partialHomPredicateFragment.finiteClauseEnumeration = false := rfl

theorem partialHomPredicate_dynamicsComplete :
    partialHomPredicateFragment.dynamicsComplete = true := rfl

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
states need explicit clauses on the **finite-table projection**. On arbitrary `SZ`, the
shared fixed-table tier uses `SystemSatisfiesPartialDynamicsOpen` (ungated iff via
`partialDynamicsOpen_iff_hom`); the hom headline uses `SystemSatisfiesPartialDynamicsHom`
(`partialDynamicsHom_iff_hom`). `ReadoutSpecCompleteOpen` is vacuous (`True` for all `Z`);
do not treat it as a gate on either ungated iff. -/
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
