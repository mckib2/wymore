import Mbse.SystemToLTL
import Mbse.FSMProperties
import Mbse.FiniteWymore
import Mbse.PropertySemantics
import Mbse.TemporalLogic
import Mathlib.Data.Fintype.Basic

/-!
# General finite `DiscreteSystem` property fragment (Stage 3)

Dynamics-complete clause tables for **total** finite systems (`DiscreteSystem.ofTotal` /
`AlwaysOutputs`). Partial `NZ`/`RZ` (`Option.none`) are excluded from the assertional fragment —
a TL-side restriction, not a restriction on the general `DiscreteSystem` class.
-/

namespace GeneralFSMBridge

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]

open FSM

/-- Reconstruct an `FSMSystem` from a total `DiscreteSystem`. Requires `AlwaysOutputs`. -/
def ofDiscreteSystem (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) : FSMSystem SZ IZ OZ where
  sz_nonempty := Z.sz_nonempty
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s i => Z.NZ s (some i)
  RZ := fun s => Option.get (Z.RZ s) (by
    obtain ⟨o, ho⟩ := hOut s
    simp [ho])

end GeneralFSMBridge

namespace PropertyFragment.General

open TemporalLogic PropertySemantics SystemToLTL PropertyFragment.FSM
open FSM GeneralFSMBridge

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

def systemTrace (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s0 : SZ) (f : ITZ IZ) :
    Trace (Atom SZ IZ OZ) :=
  PropertyFragment.FSM.fsmTrace (ofDiscreteSystem Z hOut) s0 f

noncomputable def dynamicsTable (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    PropertySet (LTL (Atom SZ IZ OZ)) :=
  fsmDynamicsTable (ofDiscreteSystem Z hOut)

def SystemSatisfiesDynamics (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  FSMSatisfiesDynamics (ofDiscreteSystem Z_spec hSpec) (ofDiscreteSystem Z_impl hImpl)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem SystemSatisfiesDynamics_iff_fsm {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl ↔
      FSMSatisfiesDynamics (ofDiscreteSystem Z_spec hSpec)
        (ofDiscreteSystem Z_impl hImpl) :=
  Iff.rfl

def SystemExtEqual (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  FSMExtEqual (ofDiscreteSystem Z_spec hSpec) (ofDiscreteSystem Z_impl hImpl)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem SystemExtEqual_iff_fsm {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemExtEqual Z_spec Z_impl hSpec hImpl ↔
      FSMExtEqual (ofDiscreteSystem Z_spec hSpec)
        (ofDiscreteSystem Z_impl hImpl) :=
  Iff.rfl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] [Nonempty IZ] in
theorem ofDiscreteSystem_extEqual_toDiscreteSystem (F : FSMSystem SZ IZ OZ) :
    FSMExtEqual (ofDiscreteSystem (_root_.FSM.FSMSystem.toDiscreteSystem F)
      (_root_.FSM.fsm_alwaysOutputs F)) F := by
  constructor
  · intro s
    simp [ofDiscreteSystem, _root_.FSM.FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal,
      Option.get_some]
  · intro s i
    simp [ofDiscreteSystem, _root_.FSM.FSMSystem.toDiscreteSystem, DiscreteSystem.ofTotal]

end PropertyFragment.General
