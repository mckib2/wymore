import Mbse.BlockerAudit
import Mbse.WymoreCharacterization
import Mbse.PropertyFragmentSpec
import Mbse.FragmentPathologyRegistry
import Mbse.BiImplicationFailures
import Mbse.CounterSystemVerification
import Mbse.ExtensionalDynamicsFragment
import Mbse.SpecFromProperties
import Mbse.GeneralProperties
import Mbse.WymorePropertyFragment
import Mbse.WymorePathologyExamples

/-!
# Verification tier dispatch

Given side conditions on `Z`, select a `VerificationTier` and dispatch to the matching
`wymore_verification_*` theorem. Blockers exclude tiers (e.g. infinite `Nat` excludes pinned finite).
-/

namespace VerificationTierDispatch

open BlockerAudit WymoreCharacterization PropertyFragmentSpec FragmentPathologyRegistry
  BiImplicationFailures CounterSystemVerification ExtensionalDynamicsFragment
  WymorePropertyFragment WymorePathologyExamples HimsySynthesis PropertySemantics
  SpecFromProperties GeneralProperties PropertyFragment.General

inductive VerificationTier
  | pinnedFinite
  | partialFinite
  | partialOpen
  | extensionalOpen
  | extensionalCross
  | himsy

def tierRequiresFiniteEnum : VerificationTier → Bool
  | .pinnedFinite => true
  | .partialFinite => true
  | .partialOpen => false
  | .extensionalOpen => false
  | .extensionalCross => false
  | .himsy => false

def tierRequiresAlwaysOutputs : VerificationTier → Bool
  | .pinnedFinite => true
  | .partialFinite => false
  | .partialOpen => false
  | .extensionalOpen => true
  | .extensionalCross => false
  | .himsy => false

def tierRequiresReadoutComplete : VerificationTier → Bool
  | .pinnedFinite => false
  | .partialFinite => true
  | .partialOpen => false
  | .extensionalOpen => false
  | .extensionalCross => false
  | .himsy => false

def tierApplicable (t : VerificationTier) {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  match t with
  | .pinnedFinite => RequiresFiniteStateEnumeration SZ ∧ AlwaysOutputs Z
  | .partialFinite => True
  | .partialOpen => True
  | .extensionalOpen => AlwaysOutputs Z
  | .extensionalCross => True
  | .himsy => True

noncomputable def recommendedTier (Z : DiscreteSystem SZ IZ OZ) : VerificationTier := by
  classical
  by_cases hFin : RequiresFiniteStateEnumeration SZ
  · by_cases hOut : AlwaysOutputs Z
    · exact .pinnedFinite
    · exact .partialOpen
  · exact .extensionalCross

theorem recommendedTier_counterSystem :
    recommendedTier counterSystem = .extensionalCross := by
  unfold recommendedTier
  simp [counterSystem_not_pinned_finite]

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

theorem dispatch_counterSystem
    (_hTier : tierApplicable (.extensionalCross : VerificationTier) counterSystem)
    (hAdeq : PhiAdequateExtensionalCross counterSystem) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec counterSystem) counterElab ↔
      IsHomomorphicImage (synthesizeExtensionalSpec counterSystem) counterElab :=
  wymore_verification_extensional_cross hAdeq

end VerificationTierDispatch
