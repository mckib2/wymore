import Mbse.FSMProperties
import Mbse.Homomorphism
import Mbse.FiniteWymore
import Mbse.WymorePropertyFragment
import Mbse.FragmentPathologyRegistry

/-!
# Homomorphism witness construction (finite tiers)

Tier A: decide extensional equality on finite FSMs and build identity witness.
Tier B: verify supplied maps satisfy homomorphic-image axioms.

General automatic discovery on infinite state is not provided; see
`synthesis_automaticHomDiscovery_blocked`.
-/

namespace HomWitnessConstruction

open FSMProperties PropertyFragment.FSM FSM Homomorphism WymorePropertyFragment

variable {SZ IZ OZ : Type}

/-! ## Tier A: finite identity hom -/

section DecidableFSM

variable [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]

noncomputable instance instDecidableFsmExtEqual (F_spec F_impl : FSMSystem SZ IZ OZ) :
    Decidable (FSMExtEqual F_spec F_impl) :=
  Classical.dec _

noncomputable def checkFsmExtEqual (F_spec F_impl : FSMSystem SZ IZ OZ) : Bool :=
  decide (FSMExtEqual F_spec F_impl)

omit [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem checkFsmExtEqual_true_iff (F_spec F_impl : FSMSystem SZ IZ OZ) :
    checkFsmExtEqual F_spec F_impl = true ↔ FSMExtEqual F_spec F_impl := by
  simp [checkFsmExtEqual, decide_eq_true_eq]

def constructIdentityHomWitness (F_spec F_impl : FSMSystem SZ IZ OZ)
    (h : FSMExtEqual F_spec F_impl) : FSMIdentityHomomorphicImageWitness F_spec F_impl :=
  identityFsmWitness h

omit [Fintype SZ] [Fintype IZ] [Fintype OZ] [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem constructIdentityHom_from_decide (F_spec F_impl : FSMSystem SZ IZ OZ)
    (h : checkFsmExtEqual F_spec F_impl = true) :
    FSMIsIdentityHomomorphicImage F_spec F_impl :=
  ⟨constructIdentityHomWitness F_spec F_impl ((checkFsmExtEqual_true_iff F_spec F_impl).mp h)⟩

end DecidableFSM

/-! ## Tier B: verify supplied maps -/

section VerifyMaps

variable {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}

def tryConstructHomWitness {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hNZ : ∀ s oi, HS (Z_impl.NZ s oi) = Z_spec.NZ (HS s) (Option.map HI oi))
    (hRZ : ∀ s, Option.map HO (Z_impl.RZ s) = Z_spec.RZ (HS s))
    (hS : Function.Surjective HS) (hI : Function.Surjective HI) (hO : Function.Surjective HO) :
    HomomorphicImageWitness Z_spec Z_impl :=
  { HS := HS, HI := HI, HO := HO
    HS_surjective := hS, HI_surjective := hI, HO_surjective := hO
    preserves_transition := hNZ, preserves_readout := hRZ }

theorem tryConstructHomWitness_is_hom {Z_spec : DiscreteSystem SZ1 IZ1 OZ1}
    {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1)
    (hNZ : ∀ s oi, HS (Z_impl.NZ s oi) = Z_spec.NZ (HS s) (Option.map HI oi))
    (hRZ : ∀ s, Option.map HO (Z_impl.RZ s) = Z_spec.RZ (HS s))
    (hS : Function.Surjective HS) (hI : Function.Surjective HI) (hO : Function.Surjective HO) :
    IsHomomorphicImage Z_spec Z_impl :=
  ⟨tryConstructHomWitness HS HI HO hNZ hRZ hS hI hO⟩

end VerifyMaps

/-! ## Tier D: no general automatic discovery -/

theorem synthesis_automaticHomDiscovery_blocked :
    ¬ RequiresFiniteStateEnumeration Nat :=
  FragmentPathologyRegistry.blocked_infiniteSZ

end HomWitnessConstruction
