import Mbse.HomSoundness
import Mbse.GeneralProperties
import Mbse.BlockerAudit
import Mbse.SpecFromProperties
import Mbse.ExtensionalDynamicsFragment
import Mbse.HimsySynthesis
import Mbse.FSMProperties
import Mbse.SystemToLTL
import Mbse.PathologyExamples
import Mbse.WymorePathologyExamples
import Mbse.ObservablesFromSpec
import Mbse.PropertySemantics
import Mbse.TemporalLogic

/-!
# Synthesis pipeline: spec ↔ Φ ↔ hom

Forward (one-way soundness): homomorphic image ⇒ property satisfaction.
Reverse (gated): under `PhiAdequate*`, property satisfaction ↔ homomorphic image.

Intentional limits: bare Φ without canonical shape or witness does not determine
`Z_spec` — see `synthesis_bare_phi_insufficient`.
-/

namespace SynthesisPipeline

open HomSoundness GeneralProperties PropertySemantics SpecFromProperties
  ExtensionalDynamicsFragment HimsySynthesis FSMProperties SystemToLTL
  PropertyFragment.FSM PropertyFragment.General BlockerAudit FragmentPathologyRegistry
  PathologyExamples WymorePathologyExamples ObservablesFromSpec TemporalLogic Homomorphism

/-! ## Forward chain (hom → Φ) -/

theorem forward_hom_implies_dynamics {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hHom : SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl :=
  system_hom_implies_satisfies hSpec hImpl hHom

theorem forward_hom_implies_extensional {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hHom : SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl :=
  (extensional_property_iff_hom hSpec hImpl).mpr hHom

theorem forward_hom_implies_extensional_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (hHom : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesExtensionalCross Z_spec Z_impl :=
  (extensional_cross_property_iff_hom).mpr hHom

/-! ## Reverse chain (gated Φ ↔ hom) -/

theorem reverse_pinned_iff {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateSpec (SystemSatisfiesDynamics Z Z hZ hZ)
      (synthesizeSpec Z hZ = synthesizeSpec Z hZ)) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  (stage3_verification_equivalence hZ hImpl) _hAdeq

theorem reverse_extensional_cross_iff {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateExtensionalCross Z) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_cross_verification_equivalence _hAdeq

theorem reverse_himsy_iff {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateHimsy w) :
    SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_impl ↔
      IsHomomorphicImage (synthesizeHimsySpec w) Z_impl :=
  (himsy_verification_equivalence w) _hAdeq

/-! ## Propositional LTL corollary (Stage 2 FSM) -/

theorem reverse_fsm_compile_iff {SZ IZ OZ : Type} [Nonempty IZ] (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F ↔
      ∀ (s0 : SZ) (f : ITZ IZ), (SystemToLTL.fsmTrace F s0 f).models (compileFSM F) :=
  fsm_satisfiesDynamics_self_iff_models_compileFSM F

/-! ## Intentional non-recovery -/

theorem synthesis_bare_phi_insufficient :
    fsmOutputTable fsmStay = fsmOutputTable fsmJump ∧ ¬ FSMExtEqual fsmStay fsmJump :=
  blocked_barePhi_uniqueZ

theorem synthesis_witness_required_for_inverse {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] (Phi : PropertySet (LTL (Atom SZ IZ OZ)))
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (h : IsSynthesizableTable Phi Z hOut) :
    recoverSpecFromTable Phi Z hOut = Z ∧
      compileObservables (recoverSpecFromTable Phi Z hOut) hOut = Phi :=
  ⟨recoverSpecFromTable_eq Phi Z hOut h, recoverSpecFromTable_compiles Phi Z hOut h⟩

theorem synthesis_executionFO_not_hom :
    SystemSatisfiesSpecFOAt foUnreachableSpec foUnreachableImpl 0 foUnreachableInput ∧
      ¬ SystemIsIdentityHomomorphicImageOpen foUnreachableSpec foUnreachableImpl
        foUnreachableSpec_alwaysOutputs foUnreachableImpl_alwaysOutputs := by
  rcases fo_execution_not_complete_for_hom with ⟨hFO, _, hHom⟩
  exact ⟨hFO, hHom⟩

end SynthesisPipeline
