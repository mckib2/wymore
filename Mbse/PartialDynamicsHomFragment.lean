import Mbse.ExtensionalDynamicsFragment
import Mbse.WymorePropertyFragment
import Mbse.Homomorphism
import Mbse.WymorePathologyExamples

/-!
# Partial dynamics hom headline tier

Hom-relative partial dynamics: witness-free satisfaction via surjective Def 4.3 maps
(`SystemSatisfiesPartialDynamicsHom`) — the primary Wymore FC hom↔Φ bi-implication.

Pattern classes covered (see comparative report): cross-type elaboration, same-type
state renaming, infinite state with closed readout.

Semantic content coincides with [`SystemSatisfiesExtensionalCross`]. This module supplies
engineering-facing names, collapse theorems, and hom-relative trace/LTL/FO encodings
indexed by spec states.
-/

namespace PartialDynamicsHomFragment

open ExtensionalDynamicsFragment WymorePropertyFragment Homomorphism
  WymorePathologyExamples TemporalLogic SystemToFormula FOLTL

/-! ## Witness-free hom-relative partial dynamics (Phase 1 semantic core) -/

/-- Hom-relative partial dynamics: ∃ surjective `HS`/`HI`/`HO` with partial NZ/RZ laws.

  Coincides with [`SystemSatisfiesExtensionalCross`]: open/closed readout and full
  transition content under Option `map`. Subsumes cross-type elaboration and
  same-type surjective non-identity hom. -/
abbrev SystemSatisfiesPartialDynamicsHom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2) : Prop :=
  SystemSatisfiesExtensionalCross Z_spec Z_impl

theorem partialDynamicsHom_eq_extensionalCross {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      SystemSatisfiesExtensionalCross Z_spec Z_impl :=
  Iff.rfl

theorem partialDynamicsHom_of_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl :=
  extensional_cross_of_hom h

theorem hom_of_partialDynamicsHom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : SystemSatisfiesPartialDynamicsHom Z_spec Z_impl) :
    IsHomomorphicImage Z_spec Z_impl :=
  extensional_hom_of_cross h

/-- Main hom-projection milestone: partial dynamics hom ↔ Def 4.3 homomorphic image. -/
theorem partialDynamicsHom_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      IsHomomorphicImage Z_spec Z_impl :=
  extensional_cross_property_iff_hom

/-! ## Witness-indexed packaging -/

/-- Witness-indexed partial hom dynamics — packaged Def 4.3 laws. -/
abbrev PartialDynamicsHomWitness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) : Prop :=
  SystemSatisfiesExtensionalAt w

theorem partialDynamicsHomWitness_iff {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    PartialDynamicsHomWitness w ↔ SystemSatisfiesExtensionalAt w :=
  Iff.rfl

theorem partialDynamicsHomWitness_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    PartialDynamicsHomWitness w :=
  hom_implies_satisfies_extensional w

/-! ## Predicate-indexed compile object (spec-side, hom tier) -/

/-- Spec-side predicate-indexed partial dynamics compile for the hom projection tier.

  Clauses are indexed by **spec** states; satisfaction is hom-relative (Phase 2 trace
  encoding). On the semantic tier, compiled content matches [`compileObservablesPartialOpen`]
  on `Z_spec`. -/
abbrev compileObservablesPartialHom {SZ IZ OZ : Type} [DecidableEq IZ]
    (Z_spec : DiscreteSystem SZ IZ OZ) : PartialDynamicsOpenCompile SZ IZ OZ Z_spec :=
  compileObservablesPartialOpen Z_spec

theorem compileObservablesPartialHom_eq_open {SZ IZ OZ : Type} [DecidableEq IZ]
    (Z_spec : DiscreteSystem SZ IZ OZ) :
    compileObservablesPartialHom Z_spec = compileObservablesPartialOpen Z_spec :=
  rfl

/-! ## Collapse: headline identity tier ↔ hom projection -/

/-- Identity partial hom witness from pointwise agreement. -/
def partialIdentity_to_homWitness {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (w : PartialIdentityHomomorphicImageWitness Z_spec Z_impl) :
    HomomorphicImageWitness Z_spec Z_impl where
  HS := id
  HI := id
  HO := id
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := fun s oi => by simp [w.preserves_transition s oi]
  preserves_readout := fun s => by simp [w.preserves_readout s]

theorem partialIdentityHom_implies_hom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    IsHomomorphicImage Z_spec Z_impl := by
  rcases h with ⟨w⟩
  exact ⟨partialIdentity_to_homWitness w⟩

theorem partialIdentityHom_implies_partialDynamicsHom {SZ IZ OZ : Type}
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl :=
  partialDynamicsHom_of_hom (partialIdentityHom_implies_hom h)

theorem partialDynamicsOpen_implies_hom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (h : SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl :=
  partialIdentityHom_implies_partialDynamicsHom (partialDynamicsOpen_iff_hom.1 h)

theorem partialDynamicsOpen_implies_partialDynamicsHom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ} :
    SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl →
      SystemSatisfiesPartialDynamicsHom Z_spec Z_impl :=
  partialDynamicsOpen_implies_hom

theorem partialIdentityHom_implies_open {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hHom : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl := by
  have hEq : PartialExtEqual Z_spec Z_impl :=
    partial_extEqual_iff_identityHom.mpr hHom
  exact partial_extEqual_implies_satisfiesOpen hEq

theorem partialDynamicsHom_implies_open_of_identityHom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hHom : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl →
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl :=
  fun _ => partialIdentityHom_implies_open hHom

theorem partialDynamicsHom_iff_open_of_identityHom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hHom : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHom Z_spec Z_impl ↔
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl :=
  ⟨partialDynamicsHom_implies_open_of_identityHom hHom,
    partialDynamicsOpen_implies_hom⟩

/-! ## Separation witnesses (strict generalization) -/

theorem swapHom_satisfies_partialDynamicsHom :
    SystemSatisfiesPartialDynamicsHom swapSpecSys swapImplSys :=
  swapHom_satisfies_cross

theorem counterElab_satisfies_partialDynamicsHom :
    SystemSatisfiesPartialDynamicsHom counterSystem counterElab :=
  counterElab_satisfies_extensional_cross

theorem swapHom_hom_separation :
    IsHomomorphicImage swapSpecSys swapImplSys ∧
      SystemSatisfiesPartialDynamicsHom swapSpecSys swapImplSys ∧
        IsNonIdentityWitness swapHomWitness ∧
          ¬ SystemSatisfiesPartialDynamicsOpen swapSpecSys swapImplSys ∧
            ¬ SystemSatisfiesExtensional swapSpecSys swapImplSys
              swapSpecSys_alwaysOutputs swapImplSys_alwaysOutputs :=
  ⟨swapHom_sameType_image, swapHom_satisfies_partialDynamicsHom, swapHom_isNonIdentity,
    swapHom_not_partialDynamicsOpen, swapHom_not_extensional⟩

/-! ## Phase 2: hom-relative trace encoding (spec-indexed, witness-relative) -/

/-- Atoms for hom-relative traces: spec-indexed state plus impl-side input/output. -/
inductive HomRelativeAtom (SZ1 IZ1 OZ1 : Type) (SZ2 IZ2 OZ2 : Type) where
  | specState (s : SZ1)
  | input (oi : Option IZ2)
  | output (ro : Option OZ2)

/-- Impl trace with spec-state atoms via hom projection `w.HS`. -/
def homRelativeTrace {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) :
    Trace (HomRelativeAtom SZ1 IZ1 OZ1 SZ2 IZ2 OZ2) where
  holds t a :=
    match a with
    | .specState s => w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s
    | .input oi => f t = oi
    | .output ro => _root_.generateOutputTrajectory Z_impl s0 f t = ro

/-- Trajectory readout law: spec open readout projected under `w.HO`. -/
def homTrace_readoutOpen {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (o : OZ1)
    (_hR : Z_spec.RZ s = some o) : Prop :=
  ∀ (s0 : SZ2) (f : ITZW IZ2) (t : Time),
    w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s →
      (_root_.generateOutputTrajectory Z_impl s0 f t).map w.HO = some o

def homTrace_readoutClosed {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1)
    (_hR : Z_spec.RZ s = none) : Prop :=
  ∀ (s0 : SZ2) (f : ITZW IZ2) (t : Time),
    w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s →
      (_root_.generateOutputTrajectory Z_impl s0 f t).map w.HO = none

def homTrace_autonomous {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) : Prop :=
  ∀ (s0 : SZ2) (f : ITZW IZ2) (t : Time),
    w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s →
      f t = none →
        w.HS (_root_.generateStateTrajectory Z_impl s0 f (t + 1)) = Z_spec.NZ s none

def homTrace_transition {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (i : IZ1) : Prop :=
  ∀ (s0 : SZ2) (f : ITZW IZ2) (t : Time),
    w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s →
      ∀ i2, f t = some i2 → w.HI i2 = i →
        w.HS (_root_.generateStateTrajectory Z_impl s0 f (t + 1)) = Z_spec.NZ s (some i)

/-- Open readout law alias (four-clause family). -/
abbrev partialHomReadoutOpenLaw {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (o : OZ1)
    (hR : Z_spec.RZ s = some o) : Prop :=
  homTrace_readoutOpen w s o hR

/-- Closed readout at spec state `s` (LTL shape for same impl output carrier). -/
def partialHomClosedReadoutClause {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) :
    LTL (HomRelativeAtom SZ1 IZ1 OZ1 SZ2 IZ2 OZ2) :=
  LTL.G (LTL.imp (LTL.atom (.specState s)) (LTL.atom (.output none)))

/-- Autonomous transition at spec state `s`. -/
def partialHomAutonomousClause {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (_w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) :
    LTL (HomRelativeAtom SZ1 IZ1 OZ1 SZ2 IZ2 OZ2) :=
  LTL.imp (LTL.and (LTL.atom (.specState s)) (LTL.atom (.input none)))
    (LTL.X (LTL.atom (.specState (Z_spec.NZ s none))))

def SystemSatisfiesPartialDynamicsHomTraceCore {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) : Prop :=
  (∀ s o hR, homTrace_readoutOpen w s o hR) ∧
    (∀ s hR, homTrace_readoutClosed w s hR) ∧
      (∀ s, homTrace_autonomous w s)

def SystemSatisfiesPartialDynamicsHomTraceTransitions {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) : Prop :=
  ∀ s i, homTrace_transition w s i

def SystemSatisfiesPartialDynamicsHomTraceAt {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) : Prop := by
  classical
  by_cases _h : Nonempty IZ1
  · exact SystemSatisfiesPartialDynamicsHomTraceCore w ∧
      SystemSatisfiesPartialDynamicsHomTraceTransitions w
  · exact SystemSatisfiesPartialDynamicsHomTraceCore w

def SystemSatisfiesPartialDynamicsHomTrace {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} : Prop :=
  ∃ w : HomomorphicImageWitness Z_spec Z_impl,
    SystemSatisfiesPartialDynamicsHomTraceAt (w := w)

theorem homTrace_readoutOpen_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (o : OZ1) (hR : Z_spec.RZ s = some o)
    (s0 : SZ2) (f : ITZW IZ2) (t : Time)
    (hs : w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s) :
    (_root_.generateOutputTrajectory Z_impl s0 f t).map w.HO = some o := by
  have h := w.preserves_readout (_root_.generateStateTrajectory Z_impl s0 f t)
  simp only [_root_.generateOutputTrajectory, hs, hR] at h ⊢
  exact h

theorem homTrace_readoutClosed_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (hR : Z_spec.RZ s = none)
    (s0 : SZ2) (f : ITZW IZ2) (t : Time)
    (hs : w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s) :
    (_root_.generateOutputTrajectory Z_impl s0 f t).map w.HO = none := by
  have h := w.preserves_readout (_root_.generateStateTrajectory Z_impl s0 f t)
  simp only [_root_.generateOutputTrajectory, hs, hR] at h ⊢
  exact h

theorem homTrace_autonomous_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1)
    (s0 : SZ2) (f : ITZW IZ2) (t : Time)
    (hs : w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s) (hnone : f t = none) :
    w.HS (_root_.generateStateTrajectory Z_impl s0 f (t + 1)) = Z_spec.NZ s none := by
  have hx := w.preserves_transition (_root_.generateStateTrajectory Z_impl s0 f t) none
  simp [hs] at hx
  rw [_root_.generateStateTrajectory_succ, hnone, hx]

theorem homTrace_transition_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s : SZ1) (i : IZ1)
    (s0 : SZ2) (f : ITZW IZ2) (t : Time)
    (hs : w.HS (_root_.generateStateTrajectory Z_impl s0 f t) = s)
    {i2 : IZ2} (hi : f t = some i2) (hmap : w.HI i2 = i) :
    w.HS (_root_.generateStateTrajectory Z_impl s0 f (t + 1)) = Z_spec.NZ s (some i) := by
  have hx := w.preserves_transition (_root_.generateStateTrajectory Z_impl s0 f t) (some i2)
  simp [hs, hmap] at hx
  rw [_root_.generateStateTrajectory_succ, hi, hx]

theorem partialDynamicsHomTraceAt_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHomTraceAt (w := w) := by
  classical
  unfold SystemSatisfiesPartialDynamicsHomTraceAt
  split_ifs with hne
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro s o hR s0 f t hs
        exact homTrace_readoutOpen_of_witness w s o hR s0 f t hs
      · intro s hR s0 f t hs
        exact homTrace_readoutClosed_of_witness w s hR s0 f t hs
      · intro s s0 f t hs hnone
        exact homTrace_autonomous_of_witness w s s0 f t hs hnone
    · intro s i s0 f t hs i2 hi hmap
      exact homTrace_transition_of_witness w s i s0 f t hs hi hmap
  · refine ⟨?_, ?_, ?_⟩
    · intro s o hR s0 f t hs
      exact homTrace_readoutOpen_of_witness w s o hR s0 f t hs
    · intro s hR s0 f t hs
      exact homTrace_readoutClosed_of_witness w s hR s0 f t hs
    · intro s s0 f t hs hnone
      exact homTrace_autonomous_of_witness w s s0 f t hs hnone

theorem partialDynamicsHomTrace_of_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (h : IsHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := Z_spec) (Z_impl := Z_impl) := by
  rcases h with ⟨w⟩
  exact ⟨w, partialDynamicsHomTraceAt_of_witness w⟩

theorem partialDynamicsHomTraceAt_iff_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHomTraceAt (w := w) ↔ PartialDynamicsHomWitness w :=
  ⟨fun _ => partialDynamicsHomWitness_of_witness w,
    fun _ => partialDynamicsHomTraceAt_of_witness w⟩

theorem partialDynamicsHomTrace_iff_hom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := Z_spec) (Z_impl := Z_impl) ↔
      IsHomomorphicImage Z_spec Z_impl := by
  constructor
  · intro ⟨w, _⟩
    exact ⟨w⟩
  · intro h
    exact partialDynamicsHomTrace_of_hom h

theorem partialDynamicsHomTrace_iff_partialDynamicsHom {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2} :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := Z_spec) (Z_impl := Z_impl) ↔
      SystemSatisfiesPartialDynamicsHom (Z_spec := Z_spec) (Z_impl := Z_impl) :=
  partialDynamicsHomTrace_iff_hom.trans partialDynamicsHom_iff_hom.symm

/-! ## Phase 2 regressions: trace tier vs headline -/

theorem swapHom_satisfies_partialDynamicsHomTrace :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := swapSpecSys) (Z_impl := swapImplSys) :=
  partialDynamicsHomTrace_of_hom swapHom_sameType_image

theorem swapHom_not_partialDynamicsHomTrace_headline :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := swapSpecSys) (Z_impl := swapImplSys) ∧
      ¬ SystemSatisfiesPartialDynamicsOpen swapSpecSys swapImplSys :=
  ⟨swapHom_satisfies_partialDynamicsHomTrace, swapHom_not_partialDynamicsOpen⟩

theorem counterElab_satisfies_partialDynamicsHomTrace :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := counterSystem) (Z_impl := counterElab) :=
  partialDynamicsHomTrace_of_hom counterElab_hom_to_counterSystem

theorem partialDynamicsHomTrace_collapses_to_open_of_identityHom {SZ IZ OZ : Type} [DecidableEq IZ]
    {Z_spec Z_impl : DiscreteSystem SZ IZ OZ}
    (hId : PartialIsIdentityHomomorphicImage Z_spec Z_impl) :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := Z_spec) (Z_impl := Z_impl) ↔
      SystemSatisfiesPartialDynamicsOpen Z_spec Z_impl :=
  ⟨fun _ => partialIdentityHom_implies_open hId,
    fun hOpen => partialDynamicsHomTrace_of_hom (partialIdentityHom_implies_hom
      (partialDynamicsOpen_iff_hom.1 hOpen))⟩

theorem counterClosedReadout_satisfies_partialDynamicsHomTrace :
    SystemSatisfiesPartialDynamicsHomTrace
      (Z_spec := counterClosedReadout) (Z_impl := counterClosedReadout) :=
  partialDynamicsHomTrace_of_hom (partialIdentityHom_implies_hom
    (partialDynamicsOpen_iff_hom.1 counterClosedReadout_satisfiesOpen_refl))

/-! ## Phase 2 FO mirror (hom-relative assertional compile) -/

/-- Hom-relative partial assertional FO compile at impl initial state `s0`. -/
noncomputable def compileObservablesPartialHomFO {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    (Z_spec : DiscreteSystem SZ1 IZ1 OZ1) (Z_impl : DiscreteSystem SZ2 IZ2 OZ2)
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) : FOLFormula SZ1 IZ1 OZ1 :=
  compilePartialHomAssertionalFO Z_spec Z_impl w s0

/-- Impl canonical trajectories satisfy hom-relative partial assertional FO. -/
def SystemSatisfiesPartialHomAssertionalFOAt {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2) : Prop :=
  partialHomAssertionalLawsProp Z_spec Z_impl w ∧
    IsWymoreExecution Z_spec (w.HS s0) (projectedInput w.HI f)
      (projectedStateTrajectory w s0 f) (projectedOutputTrajectory w s0 f)

theorem partialHomAssertionalLawsProp_iff_partialDynamicsHomWitness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) :
    partialHomAssertionalLawsProp Z_spec Z_impl w ↔ PartialDynamicsHomWitness w := by
  rw [partialHomAssertionalLawsProp_iff_witness]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem partialHomAssertionalFOAt_of_witness {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (h : PartialDynamicsHomWitness w) :
    SystemSatisfiesPartialHomAssertionalFOAt (w := w) s0 f := by
  refine ⟨?_, ?_⟩
  · exact (partialHomAssertionalLawsProp_iff_partialDynamicsHomWitness w).mpr h
  · exact hom_preserves_wymore_execution w s0 f (canonical_is_wymore_execution Z_impl s0 f)

theorem partialDynamicsHomWitness_of_partialHomAssertionalFOAt {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (w : HomomorphicImageWitness Z_spec Z_impl) (s0 : SZ2) (f : ITZW IZ2)
    (_h : SystemSatisfiesPartialHomAssertionalFOAt (w := w) s0 f) :
    PartialDynamicsHomWitness w :=
  (partialHomAssertionalLawsProp_iff_partialDynamicsHomWitness w).mp _h.1

theorem partialDynamicsHomTrace_iff_partialAssertionalHomFO {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    [DecidableEq IZ1]
    {Z_spec : DiscreteSystem SZ1 IZ1 OZ1} {Z_impl : DiscreteSystem SZ2 IZ2 OZ2}
    (s0 : SZ2) (f : ITZW IZ2) :
    SystemSatisfiesPartialDynamicsHomTrace (Z_spec := Z_spec) (Z_impl := Z_impl) ↔
      ∃ w : HomomorphicImageWitness Z_spec Z_impl,
        SystemSatisfiesPartialHomAssertionalFOAt (w := w) s0 f := by
  constructor
  · intro ⟨w, hTrace⟩
    refine ⟨w, ?_⟩
    refine partialHomAssertionalFOAt_of_witness w s0 f ?_
    exact (partialDynamicsHomTraceAt_iff_witness w).mp hTrace
  · intro ⟨w, hFO⟩
    refine ⟨w, ?_⟩
    exact partialDynamicsHomTraceAt_of_witness w

end PartialDynamicsHomFragment
