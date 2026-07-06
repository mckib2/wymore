import Mbse.PropertySemantics
import Mbse.GeneralPropertyFragment
import Mbse.FSMProperties
import Mbse.PropertyFragment
import Mbse.TemporalLogic
import Mbse.SystemToLTL

/-!
# Bridges between layer-specific satisfaction and `SystemSatisfiesLTLAll`
-/

namespace PropertySemanticsBridge

open PropertySemantics PropertyFragment PropertyFragment.FSM PropertyFragment.General
  FSM FSMProperties Combinational TemporalLogic SystemToLTL

/-! ## Combinational -/

def CombSatisfiesLTLAll {IZ OZ : Type} (C : CombinationalSystem IZ OZ)
    (Phi : PropertySet (LTL (CombAtom IZ OZ))) : Prop :=
  ∀ (f : ITZ IZ) (φ : LTL (CombAtom IZ OZ)), φ ∈ Phi.formulas → (combTrace C f).models φ

theorem combSatisfiesFunction_iff_combSatisfiesLTLAll {IZ OZ : Type}
    (C : CombinationalSystem IZ OZ) (F : IZ → OZ) :
    CombSatisfiesFunction C F ↔ CombSatisfiesLTLAll C (combFunctionTable C F) :=
  Iff.rfl

/-! ## FSM -/

noncomputable def fsmTraceAll {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) (s0 : SZ)
    (f : ITZW IZ) : Trace (Atom SZ IZ OZ) :=
  PropertyFragment.FSM.fsmTrace F s0 (fun t =>
    match f t with
    | some i => i
    | none => Classical.arbitrary IZ)

theorem fsmSatisfiesDynamics_iff_systemSatisfiesLTLAll {SZ IZ OZ : Type} [Nonempty IZ]
    {F_spec F_impl : FSMSystem SZ IZ OZ} :
    FSMSatisfiesDynamics F_spec F_impl ↔
      SystemSatisfiesLTLAll F_impl.toDiscreteSystem (fsmDynamicsTable F_spec)
        (fun s0 f => fsmTraceAll F_impl s0 f) := by
  constructor
  · intro h s0 f _ φ hmem
    exact h s0 (fun t => match f t with | some i => i | none => Classical.arbitrary IZ) φ hmem
  · intro h s0 f φ hmem
    exact h s0 (fun t => some (f t)) trivial φ hmem

theorem fsmSatisfiesOutputTable_iff_systemSatisfiesLTLAll {SZ IZ OZ : Type} [Nonempty IZ]
    {F_spec F_impl : FSMSystem SZ IZ OZ} :
    FSMSatisfiesOutputTable F_spec F_impl ↔
      SystemSatisfiesLTLAll F_impl.toDiscreteSystem (fsmOutputTable F_spec)
        (fun s0 f => fsmTraceAll F_impl s0 f) := by
  constructor
  · intro h s0 f _ φ hmem
    exact h s0 (fun t => match f t with | some i => i | none => Classical.arbitrary IZ) φ hmem
  · intro h s0 f φ hmem
    exact h s0 (fun t => some (f t)) trivial φ hmem

noncomputable def systemTraceAll {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s0 : SZ)
    (f : ITZW IZ) : Trace (Atom SZ IZ OZ) :=
  systemTrace Z hOut s0 (fun t => match f t with | some i => i | none => Classical.arbitrary IZ)

theorem systemSatisfiesDynamics_iff_fsmSatisfies {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl ↔
      FSMSatisfiesDynamics (GeneralFSMBridge.ofDiscreteSystem Z_spec hSpec)
        (GeneralFSMBridge.ofDiscreteSystem Z_impl hImpl) :=
  Iff.rfl

end PropertySemanticsBridge
