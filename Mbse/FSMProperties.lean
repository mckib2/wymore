import Mbse.SystemToLTL
import Mbse.FiniteWymore
import Mbse.PropertySemantics
import Mbse.TemporalLogic
import Mathlib.Data.Fintype.Basic

/-!
# FSM property fragments (Stage 2)

Readout-only output-table properties document an **incomplete** TL fragment.
Full dynamics property sets (transition + readout clauses) yield bi-implication
with identity homomorphic images under the same `SZ`/`IZ`/`OZ` types.
-/

namespace PropertyFragment.FSM

/- Section variables support clause tables; not every lemma body references them. -/

open TemporalLogic PropertySemantics SystemToLTL
open FSM

variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

def fsmTrace (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : Trace (Atom SZ IZ OZ) :=
  SystemToLTL.fsmTrace F s0 f

/-! ## Readout-only fragment (incomplete) -/

def safetyOutput (s : SZ) (o : OZ) : LTL (Atom SZ IZ OZ) :=
  LTL.G (LTL.imp (LTL.atom (.state s)) (LTL.atom (.output o)))

noncomputable def fsmOutputTable (F : FSMSystem SZ IZ OZ) : PropertySet (LTL (Atom SZ IZ OZ)) :=
  ⟨Finset.univ.toList.map fun s => safetyOutput s (F.RZ s)⟩

def FSMSatisfiesOutputTable (F_ref : FSMSystem SZ IZ OZ) (F : FSMSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZ IZ) (φ : LTL (Atom SZ IZ OZ)),
    φ ∈ (fsmOutputTable F_ref).formulas → (fsmTrace F s0 f).models φ

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsmSatisfiesOutputTable_iff_traceModels (F_ref F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F_ref F ↔
      ∀ (s0 : SZ) (f : ITZ IZ) (φ : LTL (Atom SZ IZ OZ)),
        φ ∈ (fsmOutputTable F_ref).formulas → (fsmTrace F s0 f).models φ :=
  Iff.rfl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem mem_fsmOutputTable_iff (F : FSMSystem SZ IZ OZ) (φ : LTL (Atom SZ IZ OZ)) :
    φ ∈ (fsmOutputTable F).formulas ↔ ∃ s, φ = safetyOutput s (F.RZ s) := by
  dsimp [fsmOutputTable]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, heq⟩
    exact ⟨s, heq.symm⟩
  · rintro ⟨s, heq⟩
    exact ⟨s, heq.symm⟩

theorem fsmOutputTable_mem (F : FSMSystem SZ IZ OZ) (s : SZ) :
    safetyOutput s (F.RZ s) ∈ (fsmOutputTable F).formulas :=
  (mem_fsmOutputTable_iff F (safetyOutput s (F.RZ s))).2 ⟨s, rfl⟩

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsmTrace_satisfies_safetyOutput (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (s : SZ) :
    (fsmTrace F s0 f).models (safetyOutput s (F.RZ s)) := by
  simp only [Trace.models, satisfiesAt, safetyOutput]
  intro t _ hs
  simp only [fsmTrace, SystemToLTL.fsmTrace] at hs ⊢
  rw [FSM.generateOutputTrajectory_eq, hs]

/-! ## Full dynamics fragment -/

/-- Dynamics-complete property set: all transition and readout clauses from `F`. -/
noncomputable def fsmDynamicsTable (F : FSMSystem SZ IZ OZ) : PropertySet (LTL (Atom SZ IZ OZ)) :=
  ⟨transitionClauses F ++ readoutClauses F⟩

def FSMSatisfiesDynamics (F_ref : FSMSystem SZ IZ OZ) (F : FSMSystem SZ IZ OZ) : Prop :=
  ∀ (s0 : SZ) (f : ITZ IZ) (φ : LTL (Atom SZ IZ OZ)),
    φ ∈ (fsmDynamicsTable F_ref).formulas → (fsmTrace F s0 f).models φ

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsmSatisfiesDynamics_iff_traceModels (F_ref F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_ref F ↔
      ∀ (s0 : SZ) (f : ITZ IZ) (φ : LTL (Atom SZ IZ OZ)),
        φ ∈ (fsmDynamicsTable F_ref).formulas → (fsmTrace F s0 f).models φ :=
  Iff.rfl

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem mem_fsmDynamicsTable_iff (F : FSMSystem SZ IZ OZ) (φ : LTL (Atom SZ IZ OZ)) :
    φ ∈ (fsmDynamicsTable F).formulas ↔
      φ ∈ transitionClauses F ∨ φ ∈ readoutClauses F := by
  simp [fsmDynamicsTable, List.mem_append]

theorem mem_fsmDynamicsTable_transition (F : FSMSystem SZ IZ OZ) (s : SZ) (i : IZ) :
    transitionClause F s i ∈ (fsmDynamicsTable F).formulas := by
  rw [mem_fsmDynamicsTable_iff]
  exact Or.inl ((mem_transitionClauses_iff F (transitionClause F s i)).2 ⟨s, i, rfl⟩)

theorem mem_fsmDynamicsTable_readout (F : FSMSystem SZ IZ OZ) (s : SZ) :
    readoutClause F s ∈ (fsmDynamicsTable F).formulas := by
  rw [mem_fsmDynamicsTable_iff]
  exact Or.inr ((mem_readoutClauses_iff F (readoutClause F s)).2 ⟨s, rfl⟩)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsmTrace_models_transitionClause (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (s : SZ)
    (i : IZ) :
    (fsmTrace F s0 f).models (transitionClause F s i) :=
  fsmTrace_satisfies_transitionClause F s0 f 0 s i

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsmTrace_models_readoutClause (F : FSMSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) (s : SZ) :
    (fsmTrace F s0 f).models (readoutClause F s) :=
  fsmTrace_satisfies_readoutClause F s0 f 0 s

theorem fsm_dynamics_satisfies_reflexive (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F F := by
  intro s0 f φ hmem
  rw [mem_fsmDynamicsTable_iff] at hmem
  rcases hmem with hmem | hmem
  · rcases (mem_transitionClauses_iff F φ).mp hmem with ⟨s, i, heq⟩
    subst heq
    exact fsmTrace_models_transitionClause F s0 f s i
  · rcases (mem_readoutClauses_iff F φ).mp hmem with ⟨s, heq⟩
    subst heq
    exact fsmTrace_models_readoutClause F s0 f s

/-- Extensional equality of finite Moore machines. -/
def FSMExtEqual (F G : FSMSystem SZ IZ OZ) : Prop :=
  (∀ s, F.RZ s = G.RZ s) ∧ (∀ s i, F.NZ s i = G.NZ s i)

theorem fsm_satisfies_reflexive (F : FSMSystem SZ IZ OZ) :
    FSMSatisfiesOutputTable F F := by
  intro s0 f φ hmem
  rcases (mem_fsmOutputTable_iff F φ).mp hmem with ⟨s, heq⟩
  subst heq
  exact fsmTrace_satisfies_safetyOutput F s0 f s

theorem fsm_extEqual_implies_satisfies_output {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMExtEqual F_spec F_impl) :
    FSMSatisfiesOutputTable F_spec F_impl := by
  intro s0 f φ hmem
  rcases (mem_fsmOutputTable_iff F_spec φ).mp hmem with ⟨s, heq⟩
  subst heq
  have hout := fsmTrace_satisfies_safetyOutput F_impl s0 f s
  rw [← h.1 s] at hout
  exact hout

theorem fsm_extEqual_implies_satisfies_dynamics {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMExtEqual F_spec F_impl) :
    FSMSatisfiesDynamics F_spec F_impl := by
  intro s0 f φ hmem
  rw [mem_fsmDynamicsTable_iff] at hmem
  rcases hmem with hmem | hmem
  · rcases (mem_transitionClauses_iff F_spec φ).mp hmem with ⟨s, i, heq⟩
    subst heq
    simpa [transitionClause, h.2 s i] using
      fsmTrace_models_transitionClause F_impl s0 f s i
  · rcases (mem_readoutClauses_iff F_spec φ).mp hmem with ⟨s, heq⟩
    subst heq
    simpa [readoutClause, h.1 s] using
      fsmTrace_models_readoutClause F_impl s0 f s

theorem fsm_satisfies_implies_readout_agreement {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMSatisfiesDynamics F_spec F_impl) :
    ∀ s, F_impl.RZ s = F_spec.RZ s := by
  intro s
  have hne : (Finset.univ : Finset IZ).Nonempty := Finset.univ_nonempty
  let f : ITZ IZ := fun _ => hne.choose
  have hφ := h s f (readoutClause F_spec s) (mem_fsmDynamicsTable_readout F_spec s)
  simp only [Trace.models, readoutClause, fsmTrace, SystemToLTL.fsmTrace] at hφ
  have hs : (fsmTrace F_impl s f).holds 0 (.state s) := by
    simp [fsmTrace, SystemToLTL.fsmTrace, FSM.generateStateTrajectory_zero]
  have hout := hφ hs
  simp only [satisfiesAt,
    FSM.generateOutputTrajectory_eq, FSM.generateStateTrajectory_zero] at hout
  exact Option.some.inj hout

theorem fsm_satisfies_implies_extEqual {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMSatisfiesDynamics F_spec F_impl) :
    FSMExtEqual F_spec F_impl := by
  constructor
  · intro s
    exact (fsm_satisfies_implies_readout_agreement h s).symm
  · intro s i
    let f : ITZ IZ := fun _ => i
    have hmodels := h s f (transitionClause F_spec s i) (mem_fsmDynamicsTable_transition F_spec s i)
    simp only [Trace.models, transitionClause, fsmTrace, SystemToLTL.fsmTrace] at hmodels
    have hs : (fsmTrace F_impl s f).holds 0 (.state s) := by
      simp [fsmTrace, SystemToLTL.fsmTrace, FSM.generateStateTrajectory_zero]
    have hi : (fsmTrace F_impl s f).holds 0 (.input i) := by
      simp [fsmTrace, SystemToLTL.fsmTrace, f]
    have hnext := hmodels (And.intro hs hi)
    exact hnext.symm

theorem fsm_satisfies_dynamics_spec_extEqual {F_spec F_spec' F_impl : FSMSystem SZ IZ OZ}
    (h : FSMExtEqual F_spec F_spec') :
    FSMSatisfiesDynamics F_spec F_impl ↔ FSMSatisfiesDynamics F_spec' F_impl := by
  constructor
  · intro hSat
    have hExt := fsm_satisfies_implies_extEqual hSat
    refine fsm_extEqual_implies_satisfies_dynamics ?_
    constructor
    · intro s; rw [← h.1 s, hExt.1 s]
    · intro s i; rw [← h.2 s i, hExt.2 s i]
  · intro hSat
    have hExt := fsm_satisfies_implies_extEqual hSat
    refine fsm_extEqual_implies_satisfies_dynamics ?_
    constructor
    · intro s; rw [h.1 s, hExt.1 s]
    · intro s i; rw [h.2 s i, hExt.2 s i]

theorem fsm_satisfies_dynamics_impl_extEqual {F_spec F_impl F_impl' : FSMSystem SZ IZ OZ}
    (h : FSMExtEqual F_impl F_impl') :
    FSMSatisfiesDynamics F_spec F_impl ↔ FSMSatisfiesDynamics F_spec F_impl' := by
  constructor
  · intro hSat
    have hExt := fsm_satisfies_implies_extEqual hSat
    refine fsm_extEqual_implies_satisfies_dynamics ?_
    constructor
    · intro s; rw [hExt.1 s, h.1 s]
    · intro s i; rw [hExt.2 s i, h.2 s i]
  · intro hSat
    have hExt := fsm_satisfies_implies_extEqual hSat
    refine fsm_extEqual_implies_satisfies_dynamics ?_
    constructor
    · intro s; rw [hExt.1 s, h.1 s]
    · intro s i; rw [hExt.2 s i, h.2 s i]

end PropertyFragment.FSM

namespace FSMProperties


variable {SZ IZ OZ : Type} [Fintype SZ] [Fintype IZ] [Fintype OZ]
variable [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ]
variable [Nonempty IZ]

open PropertyFragment.FSM FSM PropertySemantics TemporalLogic

structure FSMIdentityHomomorphicImageWitness (F_spec F_impl : FSMSystem SZ IZ OZ) where
  preserves_readout : ∀ s, F_impl.RZ s = F_spec.RZ s
  preserves_transition : ∀ s i, F_impl.NZ s i = F_spec.NZ s i

def FSMIsIdentityHomomorphicImage (F_spec F_impl : FSMSystem SZ IZ OZ) : Prop :=
  Nonempty (FSMIdentityHomomorphicImageWitness F_spec F_impl)

omit [DecidableEq SZ] [DecidableEq IZ] [DecidableEq OZ] in
theorem fsm_extEqual_iff_identityHom (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMExtEqual F_spec F_impl ↔ FSMIsIdentityHomomorphicImage F_spec F_impl := by
  constructor
  · intro ⟨hR, hN⟩
    exact ⟨⟨fun s => (hR s).symm, fun s i => (hN s i).symm⟩⟩
  · intro ⟨w⟩
    exact ⟨fun s => (w.preserves_readout s).symm, fun s i => (w.preserves_transition s i).symm⟩

def identityFsmWitness {F_spec F_impl : FSMSystem SZ IZ OZ} (h : FSMExtEqual F_spec F_impl) :
    FSMIdentityHomomorphicImageWitness F_spec F_impl where
  preserves_readout := fun s => (h.1 s).symm
  preserves_transition := fun s i => (h.2 s i).symm

theorem fsm_satisfies_implies_hom {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMSatisfiesDynamics F_spec F_impl) :
    FSMIsIdentityHomomorphicImage F_spec F_impl :=
  ⟨identityFsmWitness (fsm_satisfies_implies_extEqual h)⟩

theorem fsm_hom_implies_satisfies {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMIsIdentityHomomorphicImage F_spec F_impl) :
    FSMSatisfiesDynamics F_spec F_impl := by
  rcases h with ⟨w⟩
  exact fsm_extEqual_implies_satisfies_dynamics
    ⟨fun s => (w.preserves_readout s).symm, fun s i => (w.preserves_transition s i).symm⟩

/-- Stage-2 full bi-implication for dynamics property sets under identity maps. -/
theorem fsm_property_iff_hom (F_spec F_impl : FSMSystem SZ IZ OZ) :
    FSMSatisfiesDynamics F_spec F_impl ↔
      FSMIsIdentityHomomorphicImage F_spec F_impl :=
  ⟨fsm_satisfies_implies_hom, fsm_hom_implies_satisfies⟩

theorem fsm_extEqual_implies_hom (F : FSMSystem SZ IZ OZ) (h : FSMExtEqual F F) :
    FSMIsIdentityHomomorphicImage F F :=
  (fsm_extEqual_iff_identityHom F F).1 h

/-- Bi-implication under extensional equality (output-table fragment only). -/
theorem fsm_extEqual_iff_satisfies_and_hom (F : FSMSystem SZ IZ OZ) :
    FSMExtEqual F F ↔
      FSMSatisfiesOutputTable F F ∧ FSMIsIdentityHomomorphicImage F F := by
  constructor
  · intro h
    exact ⟨fsm_satisfies_reflexive F, (fsm_extEqual_iff_identityHom F F).1 h⟩
  · intro ⟨_, hHom⟩
    exact (fsm_extEqual_iff_identityHom F F).2 hHom

/-- Documented TL-side gap: output-table properties do not determine `NZ`. -/
theorem fsm_readout_agreement (F_spec F_impl : FSMSystem SZ IZ OZ)
    (h : FSMSatisfiesOutputTable F_spec F_impl) :
    ∀ s, F_impl.RZ s = F_spec.RZ s := by
  intro s
  have hne : (Finset.univ : Finset IZ).Nonempty := Finset.univ_nonempty
  let f : ITZ IZ := fun _ => hne.choose
  have hφ := h s f (safetyOutput s (F_spec.RZ s)) (fsmOutputTable_mem F_spec s)
  have ht := hφ 0 (Nat.zero_le 0)
  have hs : (fsmTrace F_impl s f).holds 0 (.state s) := by
    simp [fsmTrace, SystemToLTL.fsmTrace, FSM.generateStateTrajectory_zero]
  have hout := ht hs
  simp only [satisfiesAt, fsmTrace, SystemToLTL.fsmTrace,
    FSM.generateOutputTrajectory_eq, FSM.generateStateTrajectory_zero] at hout
  exact Option.some.inj hout

/-- Dynamics satisfaction implies extensional equality (full `NZ`/`RZ`). -/
theorem fsm_dynamics_implies_extEqual {F_spec F_impl : FSMSystem SZ IZ OZ}
    (h : FSMSatisfiesDynamics F_spec F_impl) :
    FSMExtEqual F_spec F_impl :=
  fsm_satisfies_implies_extEqual h

end FSMProperties
