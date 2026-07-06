import Mbse.TemporalLogic

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

end PropertyFragmentSpec
