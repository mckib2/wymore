import Mbse.Wymore
import Mbse.PropertyFragmentSpec
import Mbse.GeneralPropertyFragment
import Mbse.GeneralProperties
import Mbse.FSMProperties
import Mbse.Homomorphism
import Mbse.SystemToFormula
import Mbse.WymorePropertyFragment
import Mbse.SpecFromProperties
import Mbse.PropertySemantics
import Mbse.TemporalLogic

/-!
# Extensional dynamics fragment (infinite-state assertional Φ)

## Fragment discovery (Phase 0)

| Candidate | Compile on infinite `Z` | hom→Φ | Φ→hom (same-type) | Decision |
|---|---|---|---|---|
| A. Extensional predicate | yes (`compileObservablesExt`) | yes | **yes** | **Adopted** |
| B. Universal FO overlay | yes (Link A) | partial | uncertain | Fallback / paper encoding only |
| C. Hybrid FO + extensional | yes | yes (Track B) | via A | Integration layer in Phase 4 |

FO-LTL (`compileSystemFO`) supports Z_spec→Φ encoding (Link A). This module carries
hom↔Φ completeness for unbounded `SZ` via predicate-indexed extensional laws, not finite
clause enumeration.

`compileObservablesExt Z_spec` names the spec-side NZ/RZ laws. Cross-type satisfaction
means ∃ surjective hom maps making the elaboration project onto those laws (Def 4.3).
Same-type satisfaction (`SystemSatisfiesExtensional`) is pointwise NZ/RZ agreement under
`AlwaysOutputs`.
-/

namespace ExtensionalDynamicsFragment

open PropertyFragmentSpec PropertyFragment.General GeneralFSMBridge GeneralProperties
  FSM FSMProperties Homomorphism SystemToFormula WymorePropertyFragment FOLTL
  SpecFromProperties PropertySemantics TemporalLogic SystemToLTL

/-! ## Resolved total maps under `AlwaysOutputs` -/

/-- Total readout extracted from an open Moore system with resolvable `RZ`. -/
def totalRz {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s : SZ) : OZ :=
  Option.get (Z.RZ s) (by
    obtain ⟨o, ho⟩ := hOut s
    simp [ho])

/-! ## Spec packaging -/

/-- Spec-side extensional dynamics: reference `NZ`/`RZ` as predicate-indexed laws. -/
structure ExtensionalDynamicsSpec (SZ IZ OZ : Type) (Z : DiscreteSystem SZ IZ OZ) where
  nzLaw : ∀ (s : SZ) (oi : Option IZ), Z.NZ s oi = Z.NZ s oi
  rzLaw : ∀ (s : SZ), Z.RZ s = Z.RZ s

/-- Compile reference observables as an extensional Φ object (no finite enumeration). -/
def compileObservablesExt {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    ExtensionalDynamicsSpec SZ IZ OZ Z :=
  { nzLaw := fun _ _ => rfl, rzLaw := fun _ => rfl }

/-! ## Extensional equality and satisfaction -/

/-- Pointwise `NZ`/`RZ` agreement on total open Moore systems (no `Fintype`). -/
def SystemExtEqualOpen {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  (∀ s, totalRz Z_impl hImpl s = totalRz Z_spec hSpec s) ∧
    (∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi)

/-- Impl satisfies spec's extensional Φ: relative pointwise `NZ`/`RZ` agreement. -/
def SystemSatisfiesExtensional {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  SystemExtEqualOpen Z_spec Z_impl hSpec hImpl

/-! ## Identity hom (same-type, infinite-capable) -/

structure SystemIdentityHomomorphicImageWitnessOpen {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) where
  preserves_readout : ∀ s, totalRz Z_impl hImpl s = totalRz Z_spec hSpec s
  preserves_transition : ∀ s oi, Z_impl.NZ s oi = Z_spec.NZ s oi

def SystemIsIdentityHomomorphicImageOpen {SZ IZ OZ : Type}
    (Z_spec Z_impl : DiscreteSystem SZ IZ OZ)
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) : Prop :=
  Nonempty (SystemIdentityHomomorphicImageWitnessOpen Z_spec Z_impl hSpec hImpl)

/-! ## Reflexivity and extensional algebra -/

theorem extensional_satisfies_reflexive {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    SystemSatisfiesExtensional Z Z hOut hOut :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem extensional_extEqual_iff_satisfies {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemExtEqualOpen Z_spec Z_impl hSpec hImpl ↔
      SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl :=
  Iff.rfl

theorem extensional_extEqual_implies_satisfies {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemExtEqualOpen Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl :=
  h

theorem extensional_satisfies_implies_extEqual {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl) :
    SystemExtEqualOpen Z_spec Z_impl hSpec hImpl :=
  h

def identityOpenWitness {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemExtEqualOpen Z_spec Z_impl hSpec hImpl) :
    SystemIdentityHomomorphicImageWitnessOpen Z_spec Z_impl hSpec hImpl where
  preserves_readout := h.1
  preserves_transition := h.2

theorem extensional_extEqual_iff_identityHom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemExtEqualOpen Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl := by
  constructor
  · intro h
    exact ⟨identityOpenWitness hSpec hImpl h⟩
  · intro ⟨w⟩
    exact ⟨w.preserves_readout, w.preserves_transition⟩

theorem extensional_satisfies_implies_hom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl :=
  (extensional_extEqual_iff_identityHom hSpec hImpl).1 h

theorem extensional_hom_implies_satisfies {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl := by
  rcases h with ⟨w⟩
  exact ⟨w.preserves_readout, w.preserves_transition⟩

/-- Main milestone: extensional Φ ↔ identity hom (same-type, arbitrary `SZ`). -/
theorem extensional_property_iff_hom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔
      SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl :=
  ⟨extensional_satisfies_implies_hom hSpec hImpl, extensional_hom_implies_satisfies hSpec hImpl⟩

/-! ## Cross-type extensional satisfaction (witness-free) -/

/-- Witness-free extensional content of Def 4.3: ∃ surjective `HS`/`HI`/`HO` with NZ/RZ laws. -/
def SystemSatisfiesExtensionalCross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  ∃ (HS : SZ2 → SZ1) (HI : IZ2 → IZ1) (HO : OZ2 → OZ1),
    Function.Surjective HS ∧ Function.Surjective HI ∧ Function.Surjective HO ∧
      (∀ s oi, HS (Z_impl.NZ s oi) = Z_spec.NZ (HS s) (oi.map HI)) ∧
        (∀ s, (Z_impl.RZ s).map HO = Z_spec.RZ (HS s))

/-- Impl satisfies compiled extensional Φ from `compileObservablesExt Z_spec`. -/
def SystemSatisfiesCompiledExtensional {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  SystemSatisfiesExtensionalCross Z_spec Z_impl

theorem extensional_cross_of_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesExtensionalCross Z_spec Z_impl := by
  rcases h with ⟨w⟩
  refine ⟨w.HS, w.HI, w.HO, w.HS_surjective, w.HI_surjective, w.HO_surjective, ?_, ?_⟩
  · exact w.preserves_transition
  · exact w.preserves_readout

theorem extensional_hom_of_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : SystemSatisfiesExtensionalCross Z_spec Z_impl) :
    IsHomomorphicImage Z_spec Z_impl := by
  rcases h with ⟨HS, HI, HO, hS, hI, hO, hN, hR⟩
  exact ⟨⟨HS, HI, HO, hS, hI, hO, hN, hR⟩⟩

/-- Main cross-type milestone: assertional Φ ↔ homomorphic image (Def 4.3). -/
theorem extensional_cross_property_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesExtensionalCross Z_spec Z_impl ↔
      IsHomomorphicImage Z_spec Z_impl :=
  ⟨extensional_hom_of_cross, extensional_cross_of_hom⟩

/-! ## Witness-indexed cross-type helper (soundness only) -/

/-- Witness-indexed packaging of Def 4.3 laws — not the bi-implication LHS (use `SystemSatisfiesExtensionalCross`). -/
def SystemSatisfiesExtensionalAt {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) : Prop :=
  (∀ s, (Z_impl.RZ s).map w.HO = Z_spec.RZ (w.HS s)) ∧
    (∀ s oi, w.HS (Z_impl.NZ s oi) = Z_spec.NZ (w.HS s) (oi.map w.HI))

theorem hom_implies_satisfies_extensional {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    SystemSatisfiesExtensionalAt w :=
  ⟨w.preserves_readout, w.preserves_transition⟩

theorem extensional_cross_at_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    SystemSatisfiesExtensionalAt w → SystemSatisfiesExtensionalCross Z_spec Z_impl :=
  fun _ => extensional_cross_of_hom ⟨w⟩

/-! ## Helper lemmas -/

theorem rz_eq_of_totalRz_eq {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hR : ∀ s, totalRz Z_impl hImpl s = totalRz Z_spec hSpec s) (s : SZ) :
    Z_impl.RZ s = Z_spec.RZ s := by
  obtain ⟨o_impl, ho_impl⟩ := hImpl s
  obtain ⟨o_spec, ho_spec⟩ := hSpec s
  have h := hR s
  simp only [totalRz, ho_impl, ho_spec, Option.get_some] at h
  rw [ho_impl, ho_spec, h]

/-! ## Same-type collapse (Track D specialization) -/

theorem extensional_sameType_implies_cross {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensionalCross Z_spec Z_impl := by
  rcases h with ⟨hR, hN⟩
  refine ⟨id, id, id, Function.surjective_id, Function.surjective_id, Function.surjective_id, ?_, ?_⟩
  · intro s oi; simp [hN]
  · intro s; simp [rz_eq_of_totalRz_eq hSpec hImpl hR s]

theorem extensional_cross_implies_sameType_of_identityHom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (hHom : SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl :=
  extensional_hom_implies_satisfies hSpec hImpl hHom

theorem extensional_sameType_collapse_iff_hom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl ↔
      (SystemSatisfiesExtensionalCross Z_spec Z_impl ∧
        SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) := by
  constructor
  · intro h
    exact ⟨extensional_sameType_implies_cross hSpec hImpl h,
      extensional_satisfies_implies_hom hSpec hImpl h⟩
  · intro ⟨_, hHom⟩
    exact extensional_hom_implies_satisfies hSpec hImpl hHom

/-! ## Finite-tier agreement (unifies with pinned Stages 1–3) -/

theorem totalRz_eq_fsmRz {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s : SZ) :
    totalRz Z hOut s = (ofDiscreteSystem Z hOut).RZ s := rfl

theorem openHomWitness_to_finite {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (w : SystemIdentityHomomorphicImageWitnessOpen Z_spec Z_impl hSpec hImpl) :
    SystemIdentityHomomorphicImageWitness Z_spec Z_impl hSpec hImpl where
  preserves_readout := fun s => by
    simpa [totalRz_eq_fsmRz] using w.preserves_readout s
  preserves_transition := fun s i => by
    simpa [ofDiscreteSystem] using w.preserves_transition s (some i)

theorem extensional_openHom_implies_finiteHom {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemIsIdentityHomomorphicImageOpen Z_spec Z_impl hSpec hImpl) :
    SystemIsIdentityHomomorphicImage Z_spec Z_impl hSpec hImpl := by
  rcases h with ⟨w⟩
  exact ⟨openHomWitness_to_finite hSpec hImpl w⟩

theorem extensional_implies_dynamicsTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] [Nonempty IZ] {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl) :
    SystemSatisfiesDynamics Z_spec Z_impl hSpec hImpl :=
  system_hom_implies_satisfies hSpec hImpl
    (extensional_openHom_implies_finiteHom hSpec hImpl
      (extensional_satisfies_implies_hom hSpec hImpl h))

theorem finiteHomWitness_to_open_ofTotal {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    {NZ_spec NZ_impl : SZ → IZ → SZ} {RZ_spec RZ_impl : SZ → OZ}
    (hNE_spec : Nonempty SZ) (hNE_impl : Nonempty SZ)
    (hSpec : AlwaysOutputs (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec))
    (hImpl : AlwaysOutputs (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl))
    (w : SystemIdentityHomomorphicImageWitness
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl) :
    SystemIdentityHomomorphicImageWitnessOpen
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl where
  preserves_readout := fun s => by
    simpa [totalRz_eq_fsmRz, DiscreteSystem.ofTotal] using
      w.preserves_readout s
  preserves_transition := fun s oi => by
    cases oi with
    | none => simp [DiscreteSystem.ofTotal]
    | some i =>
      simpa [DiscreteSystem.ofTotal, ofDiscreteSystem] using w.preserves_transition s i

theorem extensional_dynamicsTable_implies_extensional_ofTotal {SZ IZ OZ : Type} [Fintype SZ]
    [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {NZ_spec NZ_impl : SZ → IZ → SZ} {RZ_spec RZ_impl : SZ → OZ}
    (hNE_spec : Nonempty SZ) (hNE_impl : Nonempty SZ)
    (hDyn : SystemSatisfiesDynamics
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl)
      (ofTotal_alwaysOutputs NZ_spec RZ_spec hNE_spec)
      (ofTotal_alwaysOutputs NZ_impl RZ_impl hNE_impl)) :
    SystemSatisfiesExtensional
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl)
      (ofTotal_alwaysOutputs NZ_spec RZ_spec hNE_spec)
      (ofTotal_alwaysOutputs NZ_impl RZ_impl hNE_impl) := by
  have hSpec := ofTotal_alwaysOutputs NZ_spec RZ_spec hNE_spec
  have hImpl := ofTotal_alwaysOutputs NZ_impl RZ_impl hNE_impl
  rcases (system_property_iff_hom hSpec hImpl).mp hDyn with ⟨w⟩
  exact extensional_hom_implies_satisfies hSpec hImpl
    ⟨finiteHomWitness_to_open_ofTotal hNE_spec hNE_impl hSpec hImpl w⟩

/-! ## FO-LTL bridge (Link A integration) -/

/-- Extensional agreement implies impl canonical trajectories satisfy spec-side execution FO. -/
theorem extensional_implies_impl_satisfies_specFO {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hSpec : AlwaysOutputs Z_spec) (hImpl : AlwaysOutputs Z_impl)
    (h : SystemSatisfiesExtensional Z_spec Z_impl hSpec hImpl)
    (s0 : SZ) (f : ITZW IZ) :
    SatisfiesFO (compileSystemFO Z_spec s0) Z_impl s0 f
      (generateStateTrajectory Z_impl s0 f)
      (generateOutputTrajectory Z_impl s0 f) := by
  rcases h with ⟨hR, hN⟩
  simp only [SatisfiesFO, compileSystemFO]
  refine ⟨rfl, ?_, ?_⟩
  · intro t
    rw [_root_.generateStateTrajectory_succ,
      hN (generateStateTrajectory Z_impl s0 f t) (f t)]
  · intro t
    rw [generateOutputTrajectory_val,
      rz_eq_of_totalRz_eq hSpec hImpl hR (generateStateTrajectory Z_impl s0 f t)]

theorem extensional_subsumes_executionFO {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s0 : SZ) (f : ITZW IZ) :
    SystemSatisfiesExtensional Z Z hOut hOut → SystemSatisfiesFO Z s0 f := by
  intro _
  rw [systemSatisfiesFO_iff_execution]
  exact canonical_is_wymore_execution Z s0 f

/-! ## Extensional synthesis + PhiAdequate (Track D verification template)

Synthesis is identity today; adequacy gate is structurally required for the paper template.
Cross-type `SystemSatisfiesExtensionalCross` is the general hom↔Φ result; same-type pointwise
ext requires `AlwaysOutputs`. `compileObservablesExt` is predicate-indexed, not a finite `PropertySet`.
-/

/-- Link B: synthesized spec compiles to the same extensional Φ as the reference. -/
theorem compileObservablesExt_synthesize {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    compileObservablesExt (synthesizeExtensionalSpec Z) = compileObservablesExt Z := rfl

theorem extensional_cross_satisfies_reflexive {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) :
    SystemSatisfiesExtensionalCross Z Z := by
  refine ⟨id, id, id, Function.surjective_id, Function.surjective_id, Function.surjective_id, ?_, ?_⟩
  · intro s oi; simp
  · intro s; simp

def PhiAdequateExtensionalCross {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop :=
  PhiAdequateSpec (SystemSatisfiesExtensionalCross Z Z) (synthesizeExtensionalSpec Z = Z)

def PhiAdequateExtensionalOpen {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) : Prop :=
  PhiAdequateSpec (SystemSatisfiesExtensional Z Z hOut hOut) (synthesizeExtensionalSpec Z = Z)

structure ExtensionalDynamicsAdequate {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) : Prop where
  selfSatisfiesCross : SystemSatisfiesExtensionalCross Z Z
  canonical : synthesizeExtensionalSpec Z = Z

theorem extensional_phi_adequate_cross {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    PhiAdequateExtensionalCross Z := by
  constructor
  · exact extensional_cross_satisfies_reflexive Z
  · exact synthesizeExtensionalSpec_eq Z

theorem extensional_phi_adequate_open {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) :
    PhiAdequateExtensionalOpen Z hOut := by
  constructor
  · exact extensional_satisfies_reflexive Z hOut
  · exact synthesizeExtensionalSpec_eq Z

theorem extensionalDynamicsAdequate_iff {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) :
    ExtensionalDynamicsAdequate Z ↔ PhiAdequateExtensionalCross Z := by
  constructor
  · intro h
    exact ⟨h.selfSatisfiesCross, h.canonical⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-- Reference is synthesizable from its own extensional Φ when self-satisfies under `AlwaysOutputs`. -/
def IsSynthesizableExtensional {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) : Prop :=
  SystemSatisfiesExtensional Z Z hOut hOut ∧ synthesizeExtensionalSpec Z = Z

theorem extensional_self_synthesizable {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) :
    IsSynthesizableExtensional Z hOut :=
  ⟨extensional_satisfies_reflexive Z hOut, synthesizeExtensionalSpec_eq Z⟩

/-- Finite reference recoverable from dynamics table + extensional self-satisfaction. -/
def IsRecoverableExtensionalTable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
    (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) : Prop :=
  IsSynthesizableTable Phi Z hOut ∧ IsSynthesizableExtensional Z hOut

theorem isRecoverableExtensionalTable_of {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] (Phi : PropertySet (LTL (Atom SZ IZ OZ))) (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (hTable : IsSynthesizableTable Phi Z hOut) :
    IsRecoverableExtensionalTable Phi Z hOut :=
  ⟨hTable, extensional_self_synthesizable Z hOut⟩

theorem extensional_synthesized_cross_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl := by
  simp [synthesizeExtensionalSpec, extensional_cross_property_iff_hom]

theorem extensional_synthesized_sameType_iff_hom {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl := by
  simp [synthesizeExtensionalSpec, extensional_property_iff_hom hZ hImpl]

theorem extensional_synthesized_verification_cross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_hAdeq : PhiAdequateExtensionalCross Z) :
    SystemSatisfiesExtensionalCross (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_synthesized_cross_iff_hom

theorem extensional_synthesized_verification_open {SZ IZ OZ : Type}
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl)
    (_hAdeq : PhiAdequateExtensionalOpen Z hZ) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl ↔
      SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z) Z_impl hZ hImpl :=
  extensional_synthesized_sameType_iff_hom hZ hImpl

theorem extensional_synthesized_compiled_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesCompiledExtensional (synthesizeExtensionalSpec Z) Z_impl ↔
      IsHomomorphicImage (synthesizeExtensionalSpec Z) Z_impl :=
  extensional_synthesized_cross_iff_hom

/-! ## Tier unification (finite pinned ↔ extensional) -/

theorem extensional_satisfies_iff_dynamics_ofTotal {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] [Nonempty IZ]
    {NZ_spec NZ_impl : SZ → IZ → SZ} {RZ_spec RZ_impl : SZ → OZ}
    (hNE_spec : Nonempty SZ) (hNE_impl : Nonempty SZ)
    (hSpec : AlwaysOutputs (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec))
    (hImpl : AlwaysOutputs (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl)) :
    SystemSatisfiesExtensional
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl ↔
      SystemSatisfiesDynamics
        (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
        (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl :=
  ⟨fun h => extensional_implies_dynamicsTable hSpec hImpl h,
    extensional_dynamicsTable_implies_extensional_ofTotal hNE_spec hNE_impl⟩

theorem synthesizeExtensional_eq_synthesize {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    synthesizeExtensionalSpec Z = synthesizeSpec Z hOut := rfl

theorem identityHom_open_iff_finite_ofTotal {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ]
    [Fintype OZ] [Nonempty IZ]
    {NZ_spec NZ_impl : SZ → IZ → SZ} {RZ_spec RZ_impl : SZ → OZ}
    (hNE_spec : Nonempty SZ) (hNE_impl : Nonempty SZ)
    (hSpec : AlwaysOutputs (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec))
    (hImpl : AlwaysOutputs (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl)) :
    SystemIsIdentityHomomorphicImageOpen
      (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
      (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl ↔
      SystemIsIdentityHomomorphicImage
        (DiscreteSystem.ofTotal NZ_spec RZ_spec hNE_spec)
        (DiscreteSystem.ofTotal NZ_impl RZ_impl hNE_impl) hSpec hImpl := by
  constructor
  · intro ⟨w⟩
    exact ⟨openHomWitness_to_finite hSpec hImpl w⟩
  · intro ⟨w⟩
    exact ⟨finiteHomWitness_to_open_ofTotal hNE_spec hNE_impl hSpec hImpl w⟩

theorem extensional_synthesized_iff_pinned_synthesized_ofTotal {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {NZ Z_impl_NZ : SZ → IZ → SZ} {RZ Z_impl_RZ : SZ → OZ}
    (hNE : Nonempty SZ) :
    let Z_spec := DiscreteSystem.ofTotal NZ RZ hNE
    let Z_impl := DiscreteSystem.ofTotal Z_impl_NZ Z_impl_RZ hNE
    let hZ := ofTotal_alwaysOutputs NZ RZ hNE
    let hImpl := ofTotal_alwaysOutputs Z_impl_NZ Z_impl_RZ hNE
    (SystemSatisfiesExtensional Z_spec Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImageOpen (synthesizeExtensionalSpec Z_spec) Z_impl hZ hImpl) ↔
      (SystemSatisfiesDynamics Z_spec Z_impl hZ hImpl ↔
        SystemIsIdentityHomomorphicImage (synthesizeSpec Z_spec hZ) Z_impl hZ hImpl) := by
  dsimp only
  have hZ := ofTotal_alwaysOutputs NZ RZ hNE
  have hImpl := ofTotal_alwaysOutputs Z_impl_NZ Z_impl_RZ hNE
  rw [extensional_synthesized_sameType_iff_hom hZ hImpl, system_synthesized_property_iff_hom hZ hImpl]
  simp only [synthesizeExtensionalSpec, synthesizeSpec]

theorem extensional_synthesized_implies_pinned_synthesized {SZ IZ OZ : Type}
    [Fintype SZ] [Fintype IZ] [Fintype OZ] [Nonempty IZ]
    {Z Z_impl : DiscreteSystem SZ IZ OZ}
    (hZ : AlwaysOutputs Z) (hImpl : AlwaysOutputs Z_impl) :
    SystemSatisfiesExtensional Z Z_impl hZ hImpl →
      SystemSatisfiesDynamics Z Z_impl hZ hImpl :=
  extensional_implies_dynamicsTable hZ hImpl

end ExtensionalDynamicsFragment
