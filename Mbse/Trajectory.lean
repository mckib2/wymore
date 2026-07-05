import Mbse.WymoreCore

/-!
# Trajectory proof automation for Wymore discrete systems

General lemmas capturing recurring induction, output-from-state, RSN, finset,
classical-choice, and AlwaysOutputs patterns used across `Wymore.lean` and
`Homomorphism.lean`.
-/

namespace Trajectory

variable {SZ IZ OZ : Type}

/-! ## Trajectory induction -/

/-- Standard induction on `Time` (Nat). -/
theorem trajectory_induction {P : Time → Prop} (h0 : P 0) (hs : ∀ t, P t → P (t + 1)) :
    ∀ t, P t :=
  fun t => Nat.rec h0 hs t

/-- State trajectory commutes with a map that preserves `NZ` and input reindexing. -/
theorem map_preserves_state_trajectory
    {SZ' IZ' OZ' : Type}
    (Z : DiscreteSystem SZ IZ OZ) (Z' : DiscreteSystem SZ' IZ' OZ')
    (φ : SZ → SZ') (mapInput : Option IZ → Option IZ')
    (preserves : ∀ s oi, φ (Z.NZ s oi) = Z'.NZ (φ s) (mapInput oi))
    (s0 : SZ) (f : ITZW IZ) :
    ∀ t, φ (generateStateTrajectory Z s0 f t) =
      generateStateTrajectory Z' (φ s0) (fun τ => mapInput (f τ)) t := by
  intro t
  induction t with
  | zero => rfl
  | succ n ih =>
    simp only [generateStateTrajectory_succ]
    rw [preserves, ih]

theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, m.φS (generateStateTrajectory Z1 s0 f t) =
      generateStateTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t :=
  map_preserves_state_trajectory Z1 Z2 m.φS (fun oi => oi.map m.φI) m.preserves_transition s0 f

/-! ## Output from state -/

theorem outputTrajectory_of_state_eq
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h : generateStateTrajectory Z x f t = generateStateTrajectory Z x g t) :
    generateOutputTrajectory Z x f t = generateOutputTrajectory Z x g t := by
  unfold generateOutputTrajectory
  rw [h]

theorem morphism_preserves_output_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, (generateOutputTrajectory Z1 s0 f t).map m.φO =
      generateOutputTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t := by
  intro t
  unfold generateOutputTrajectory
  rw [m.preserves_readout, morphism_preserves_state_trajectory m s0 f t]

/-! ## Time invariance -/

theorem stateTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
      generateStateTrajectory Z x f (s + t) := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [ih]
    unfold translate
    congr 2
    exact Nat.add_comm t s

theorem outputTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateOutputTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
      generateOutputTrajectory Z x f (s + t) := by
  unfold generateOutputTrajectory
  rw [stateTrajectory_time_invariance Z x f s t]

theorem outputTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (hst : generateStateTrajectory Z x f t = generateStateTrajectory Z x g t) :
    generateOutputTrajectory Z x f t = generateOutputTrajectory Z x g t :=
  outputTrajectory_of_state_eq Z x f g t hst

/-! ## RSN / nonanticipatory -/

theorem rsn_agree_on {A B : Type} (f g : A → B) (S : Set A) (h : RSN f S = RSN g S) :
    ∀ a ∈ S, f a = g a :=
  (rsn_eq_iff f g S).1 h

theorem rsn_agree_lt {B : Type} (f g : Time → B) (t : Time)
    (h : ∀ i, i < t → f i = g i) :
    RSN f {i | i < t} = RSN g {i | i < t} :=
  (rsn_eq_iff f g {i | i < t}).2 (fun i hi => h i hi)

theorem stateTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t := by
  induction t with
  | zero => simp only [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i, i < t → f i = g i := fun i hi =>
      h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := h_agree t (Nat.lt_succ_self t)
    rw [ih (rsn_agree_lt f g t h_lt), h_eq]

/-! ## Finset cardinality bridges -/

theorem exists_two_distinct_of_card_gt_one {α : Type} [DecidableEq α] (s : Finset α)
    (h : s.card > 1) : ∃ x y : α, x ∈ s ∧ y ∈ s ∧ x ≠ y :=
  (Finset.one_lt_card_iff).1 h

theorem card_gt_one_of_exists_two_distinct {α : Type} [DecidableEq α] (s : Finset α)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) : s.card > 1 :=
  (Finset.one_lt_card_iff).2 ⟨x, y, hx, hy, hne⟩

theorem varyingOutput_iff_card_rng {SZ OZ : Type} [Fintype SZ] [Fintype OZ] [DecidableEq OZ]
    (RZ : SZ → OZ) :
    (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ RZ s1 = o1 ∧ RZ s2 = o2) ↔
      Finset.card (RNG RZ) > 1 := by
  constructor
  · rintro ⟨o1, o2, s1, s2, ho, h1, h2⟩
    exact card_gt_one_of_exists_two_distinct (RNG RZ)
      (Finset.mem_image.mpr ⟨s1, Finset.mem_univ _, h1⟩)
      (Finset.mem_image.mpr ⟨s2, Finset.mem_univ _, h2⟩) ho
  · intro h
    obtain ⟨o1, o2, hm1, hm2, ho⟩ := exists_two_distinct_of_card_gt_one (RNG RZ) h
    obtain ⟨s1, _, hs1⟩ := Finset.mem_image.mp hm1
    obtain ⟨s2, _, hs2⟩ := Finset.mem_image.mp hm2
    exact ⟨o1, o2, s1, s2, ho, hs1, hs2⟩

/-! ## Classical choice on surjections -/

theorem choose_preimage {α β : Type} (f : α → β) (hf : Function.Surjective f) (b : β) :
    f (Classical.choose (hf b)) = b :=
  Classical.choose_spec (hf b)

theorem choose_some_map {α β : Type} (f : α → β) (hf : Function.Surjective f) (b : β) :
    (some (Classical.choose (hf b))).map f = some b := by
  simp [choose_preimage f hf b]

theorem choose_alwaysOutputs {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (s : SZ) {o : OZ} (ho : Z.RZ s = some o) :
    Classical.choose (hOut s) = o :=
  Option.some_injective _ ((Classical.choose_spec (hOut s)).symm.trans ho)

/-! ## Fin helpers -/

theorem fin_one_eq (i j : Fin 1) : i = j :=
  Subsingleton.elim i j

theorem fin_one_indices_eq {n : Nat} (hn : n = 1) (i j : Fin n) : i = j := by
  subst hn
  exact fin_one_eq i j

/-! ## AlwaysOutputs elimination -/

theorem alwaysOutputs_elim {P : Prop} {SZ IZ OZ : Type}
    (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) (s : SZ)
    (h : Z.RZ s = none) : P :=
  nomatch alwaysOutputs_not_none Z hOut s h

end Trajectory
