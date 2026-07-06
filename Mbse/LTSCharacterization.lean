import Mbse.LTSWymore
import Mbse.PropertyFragmentSpec

/-!
# LTS refinement characterization

Optional module for the LTS↔Wymore integration paper. Not imported by the default `Mbse` library root.
-/

namespace LTSCharacterization

open LTS LTS.Examples PropertyFragmentSpec

theorem stageLTS_refinement_sound {S Act SZ IZ OZ : Type}
    (L : LabeledTransitionSystem S Act) (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (R : WymoreRefinement S Act L SZ IZ OZ Z s0) :
    TraceRefines L Z s0 R.interp :=
  wymoreRefinement_traceRefines L Z s0 R

theorem stageLTS_trivial_refines {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ)
    (hOut : AlwaysOutputs Z) :
    TraceRefines (trivialSpec IZ OZ) Z s0 (@identityInterp IZ OZ) :=
  trivial_refinement Z s0 hOut

theorem stageLTS_nondet_obstruction (s0 : Bool) :
    ¬ TraceRefines forbidSpec toggleSystem s0 unitInterp :=
  toggle_not_refines_forbid s0

theorem stageLTS_fragment :
    ltsRefinementFragment.finiteClauseEnumeration = false :=
  foAssertional_no_finite_enum

end LTSCharacterization
