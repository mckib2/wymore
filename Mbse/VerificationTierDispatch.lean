import Mbse.BlockerAudit
import Mbse.BiImplicationFailures
import Mbse.FragmentPathologyRegistry
import Mbse.HomSoundness
import Mbse.PropertySemantics
import Mbse.WymoreCharacterization
import Mbse.HimsySynthesis
import Mbse.WymorePropertyFragment
import Mbse.WymorePathologyExamples
import Mbse.PathologyExamples
import Mbse.FiniteWymore
import Mbse.CounterSystemVerification
import Mbse.ExtensionalDynamicsFragment
import Mbse.PartialDynamicsHomFragment
import Mbse.SpecFromProperties
import Mbse.GeneralProperties
import Mbse.PropertyFragmentSpec

/-!
# Verification tier dispatch

Given side conditions on `Z`, select a `VerificationTier` and dispatch to the matching
`wymore_verification_*` theorem. Blockers exclude tiers (e.g. infinite `Nat` excludes pinned finite).
-/

namespace VerificationTierDispatch

open BlockerAudit WymoreCharacterization PropertyFragmentSpec FragmentPathologyRegistry
  BiImplicationFailures CounterSystemVerification ExtensionalDynamicsFragment
  PartialDynamicsHomFragment WymorePropertyFragment WymorePathologyExamples HimsySynthesis PropertySemantics
  SpecFromProperties GeneralProperties PropertyFragment.General PathologyExamples FSM
  HomSoundness

inductive VerificationTier
  | pinnedFinite
  | partialFinite
  | partialOpen
  | partialHom
  | extensionalOpen
  | extensionalCross
  | himsy

def tierRequiresFiniteEnum : VerificationTier → Bool
  | .pinnedFinite => true
  | .partialFinite => true
  | .partialOpen => false
  | .partialHom => false
  | .extensionalOpen => false
  | .extensionalCross => false
  | .himsy => false

def tierRequiresAlwaysOutputs : VerificationTier → Bool
  | .pinnedFinite => true
  | .partialFinite => false
  | .partialOpen => false
  | .partialHom => false
  | .extensionalOpen => true
  | .extensionalCross => false
  | .himsy => false

def tierRequiresReadoutComplete : VerificationTier → Bool
  | .pinnedFinite => false
  | .partialFinite => true
  | .partialOpen => false
  | .partialHom => false
  | .extensionalOpen => false
  | .extensionalCross => false
  | .himsy => false

def tierApplicable (t : VerificationTier) {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  match t with
  | .pinnedFinite => RequiresFiniteStateEnumeration SZ ∧ AlwaysOutputs Z
  | .partialFinite => RequiresFiniteStateEnumeration SZ
  | .partialOpen => True
  | .partialHom => True
  | .extensionalOpen => AlwaysOutputs Z
  | .extensionalCross => True
  | .himsy => True

/-- Heuristic tier recommendation. Default infinite-state closed-readout systems to hom
headline (`.partialHom`); finite same-type closed-readout to shared fixed-table (`.partialOpen`). -/
noncomputable def recommendedTier (Z : DiscreteSystem SZ IZ OZ) : VerificationTier := by
  classical
  by_cases hFin : RequiresFiniteStateEnumeration SZ
  · by_cases hOut : AlwaysOutputs Z
    · exact .pinnedFinite
    · exact .partialOpen
  · by_cases hOut : AlwaysOutputs Z
    · exact .extensionalOpen
    · exact .partialHom

theorem recommendedTier_counterSystem :
    recommendedTier counterSystem = .extensionalOpen := by
  unfold recommendedTier
  simp [counterSystem_not_pinned_finite, counterSystem_alwaysOutputs]

theorem recommendedTier_closedSystem :
    recommendedTier closedSystem = .partialOpen := by
  unfold recommendedTier
  simp [closedSystem_not_alwaysOutputs, requiresFiniteStateEnumeration_of_fintype (SZ := Unit)]

theorem closedSystem_applicable_partialFinite :
    tierApplicable (.partialFinite : VerificationTier) closedSystem := by
  show RequiresFiniteStateEnumeration Unit
  exact requiresFiniteStateEnumeration_of_fintype (SZ := Unit)

theorem recommendedTier_fsmStay :
    recommendedTier fsmStay.toDiscreteSystem = .pinnedFinite := by
  unfold recommendedTier
  simp [fsm_alwaysOutputs, requiresFiniteStateEnumeration_of_fintype (SZ := fsmStates)]

theorem recommendedTier_autoNoneSpec :
    recommendedTier autoNoneSpec = .pinnedFinite := by
  unfold recommendedTier
  simp [autoNoneSpec_alwaysOutputs, requiresFiniteStateEnumeration_of_fintype (SZ := wymPathStates)]

/-! ## Blocker → tier exclusion -/

theorem tier_pinned_blocked_by_infiniteSZ :
    (¬ RequiresFiniteStateEnumeration Nat) →
      ¬ tierApplicable (.pinnedFinite : VerificationTier) counterSystem := by
  intro h
  simp [tierApplicable]
  intro hFin _
  exact h hFin

theorem tier_pinned_blocked_by_closedSystem :
    (pinnedFragment.dynamicsComplete = true ∧ ¬ AlwaysOutputs closedSystem) →
      ¬ tierApplicable (.pinnedFinite : VerificationTier) closedSystem := by
  intro h
  simp [tierApplicable]
  intro _ hOut
  exact h.2 hOut

abbrev tier_pinnedDynamics_blocked_by_autonomousNone := biImpFails_autonomousNone

/-! ## Dispatch theorems -/

theorem dispatch_pinned {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    [Nonempty IZ] {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hTier : tierApplicable (.pinnedFinite : VerificationTier) Z) :
    SystemSatisfiesDynamics Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImage (synthesizeSpec Z hZ) Z_impl hZ hImpl :=
  wymore_verification_pinned hZ hImpl

theorem dispatch_partial_readoutComplete {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [DecidableEq SZ] [DecidableEq IZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hComplete : ReadoutSpecComplete Z)
    (_hTier : tierApplicable (.partialFinite : VerificationTier) Z)
    (hAdeq : PhiAdequatePartialOpen Z) :
    SystemSatisfiesPartialDynamics Z Z_impl ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl :=
  wymore_verification_partial_readoutComplete hComplete hAdeq

theorem dispatch_partial_open {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (_hTier : tierApplicable (.partialOpen : VerificationTier) Z_spec) :
    SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl ↔
      PartialIsIdentityHomomorphicImage Z_spec Z_impl :=
  wymore_verification_partial_open

theorem dispatch_partial_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hTier : tierApplicable (.partialHom : VerificationTier) Z_spec) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      IsHomomorphicImage Z_spec Z_impl :=
  wymore_verification_partial_hom

theorem dispatch_partial_compiled {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (_hTier : tierApplicable (.partialOpen : VerificationTier) Z) :
    SystemSatisfiesPartialDynamicsCompiled Z Z_impl (compileObservablesPartialOpen Z) ↔
      PartialIsIdentityHomomorphicImage (synthesizePartialSpec Z) Z_impl :=
  wymore_verification_partial_compiled

theorem dispatch_extensional_open {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hTier : tierApplicable (.extensionalOpen : VerificationTier) Z)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  wymore_verification_extensional hZ hImpl _hAdeq

theorem dispatch_extensional_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hTier : tierApplicable (.extensionalCross : VerificationTier) Z)
    (_hAdeq : PhiAdequateExtensionalCross Z) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  wymore_verification_extensional_cross _hAdeq

theorem dispatch_himsy {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_elab : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_elab) {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hTier : tierApplicable (.himsy : VerificationTier) Z_spec)
    (_hAdeq : PhiAdequateHimsy w) :
    SystemSatisfiesExtensionalCross (synthesizeHimsySpec w) Z_impl ↔
      IsHomomorphicImage (synthesizeHimsySpec w) Z_impl :=
  (himsy_verification_equivalence w) _hAdeq

theorem dispatch_counterSystem
    (_hTier : tierApplicable (.extensionalCross : VerificationTier) counterSystem)
    (hAdeq : PhiAdequateExtensionalCross counterSystem) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ↔
      IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab :=
  wymore_verification_extensional_cross hAdeq

/-! ## Recommended tier correctness (witness catalog) -/

theorem recommendedTier_correct_counterSystem :
    tierApplicable (recommendedTier counterSystem) counterSystem ∧
      tierApplicable (.partialHom : VerificationTier) counterSystem := by
  constructor
  · simp [recommendedTier_counterSystem, tierApplicable, counterSystem_alwaysOutputs]
  · simp [tierApplicable]

theorem recommendedTier_correct_closedSystem :
    tierApplicable (recommendedTier closedSystem) closedSystem ∧
      tierApplicable (.partialFinite : VerificationTier) closedSystem ∧
      ReadoutSpecComplete closedSystem := by
  constructor
  · simp [recommendedTier_closedSystem, tierApplicable]
  constructor
  · exact closedSystem_applicable_partialFinite
  · exact closedSystem_readoutComplete

theorem recommendedTier_correct_fsmStay :
    tierApplicable (recommendedTier fsmStay.toDiscreteSystem) fsmStay.toDiscreteSystem := by
  simp only [recommendedTier_fsmStay, tierApplicable, fsm_alwaysOutputs,
    requiresFiniteStateEnumeration_of_fintype (SZ := fsmStates)]
  exact ⟨trivial, trivial⟩

theorem recommendedTier_correct_autoNoneSpec :
    tierApplicable (recommendedTier autoNoneSpec) autoNoneSpec := by
  simp only [recommendedTier_autoNoneSpec, tierApplicable, autoNoneSpec_alwaysOutputs,
    requiresFiniteStateEnumeration_of_fintype (SZ := wymPathStates)]
  exact ⟨trivial, trivial⟩

end VerificationTierDispatch
