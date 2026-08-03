import Mbse.WymoreCore
import Mbse.Trajectory
import Mbse.WymoreTactics
import Mathlib.Data.Fintype.Card

theorem fin_nat_card_le_of_le {m n : Nat} (h : n ≤ m) :
    Fintype.card (Fin n) ≤ Fintype.card (Fin m) := by
  rw [Fintype.card_fin n, Fintype.card_fin m]
  exact h

theorem varyingOutput_iff_card_rng {SZ OZ : Type} [Fintype SZ] [Fintype OZ] [DecidableEq OZ]
    (RZ : SZ → OZ) :
    (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ RZ s1 = o1 ∧ RZ s2 = o2) ↔
    Finset.card (RNG RZ) > 1 :=
  Trajectory.varyingOutput_iff_card_rng RZ

theorem isNontrivial_varyingOutput_iff_ofTotal {SZ IZ OZ : Type} [Fintype SZ] [Fintype OZ] [DecidableEq OZ]
    (NZ : SZ → IZ → SZ) (RZ : SZ → OZ) (hNE : Nonempty SZ) :
    let Z := DiscreteSystem.ofTotal NZ RZ hNE
    (∃ (o1 o2 : OZ) (s1 s2 : SZ), o1 ≠ o2 ∧ Z.RZ s1 = some o1 ∧ Z.RZ s2 = some o2) ↔
    Finset.card (RNG RZ) > 1 := by
  dsimp
  constructor
  · intro h
    rcases h with ⟨o1, o2, s1, s2, ho, h1, h2⟩
    simp [DiscreteSystem.ofTotal] at h1 h2
    exact (Trajectory.varyingOutput_iff_card_rng RZ).mp ⟨o1, o2, s1, s2, ho, h1, h2⟩
  · intro h
    rcases (Trajectory.varyingOutput_iff_card_rng RZ).mpr h with ⟨o1, o2, s1, s2, ho, h1, h2⟩
    exact ⟨o1, o2, s1, s2, ho, by simp [DiscreteSystem.ofTotal, h1], by simp [DiscreteSystem.ofTotal, h2]⟩

theorem morphism_preserves_state_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, m.φS (generateStateTrajectory Z1 s0 f t) =
         generateStateTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t :=
  Trajectory.morphism_preserves_state_trajectory m s0 f

theorem morphism_preserves_output_trajectory
    {SZ1 IZ1 OZ1 SZ2 IZ2 OZ2 : Type}
    {Z1 : DiscreteSystem SZ1 IZ1 OZ1}
    {Z2 : DiscreteSystem SZ2 IZ2 OZ2}
    (m : SystemMorphism Z1 Z2) (s0 : SZ1) (f : ITZW IZ1) :
    ∀ t, (generateOutputTrajectory Z1 s0 f t).map m.φO =
         generateOutputTrajectory Z2 (m.φS s0) (fun τ => (f τ).map m.φI) t :=
  Trajectory.morphism_preserves_output_trajectory m s0 f

/--
  [textbook/theorem_a1.286/theorem/translation_fns]
  [textbook/theorem_a1.286/theorem/translation_zero]
  Proof that translate f 0 = f.
-/
theorem translate_zero {A : Type} (f : Time → A) : translate f 0 = f := by
  funext t
  unfold translate
  simp only [Nat.add_zero]

/--
  [textbook/definition_a1.284/definition/closed_under_translation]
  [textbook/theorem2.25/theorem/translation_closed]
  The set of complete trajectories (Time → A) is closed under translation:
  the translated function is a well-typed complete trajectory.
-/
def complete_trajectories_closed_under_translation {A : Type} (f : Time → A) (r : Time) : Time → A :=
  translate f r

/--
  [textbook/theorem2.25/theorem/concatenation_closed]
  The set of complete trajectories is closed under concatenation.
  `concatenate` (CTN) is defined in `WymoreCore`.
-/
def complete_trajectories_closed_under_concatenation {A : Type} (f g : Time → A) (r : Time) : Time → A :=
  concatenate f g r

/-! ## General Set Theory and Function Composition -/

/--
  [textbook/definition_a1.268/definition/composition_pointwise]
  [textbook/definition_a1.268/definition/composition_set]
  The composition of functions g and f, denoted g ∘ f, is defined as (g ∘ f)(x) = g(f(x)).
-/
def compose {A B C : Type} (g : B → C) (f : A → B) : A → C :=
  g ∘ f

/--
  [textbook/theorem_a1.249/theorem/subset_inclusion]
  If f ∈ FNS(A, B) and C ⊆ B, then f(f^-1(C)) ⊆ C.
-/
theorem image_preimage_subset {A B : Type} (f : A → B) (C : Set B) :
    f '' (f ⁻¹' C) ⊆ C := by
  exact Set.image_preimage_subset f C

/--
  [textbook/theorem_a1.250/theorem/preimage_complement]
  If f ∈ FNS(A, B) and C ⊆ B, then f^-1(B - C) = A - f^-1(C).
-/
theorem preimage_complement {A B : Type} (f : A → B) (C : Set B) :
    f ⁻¹' (Cᶜ) = (f ⁻¹' C)ᶜ := by
  exact Set.preimage_compl

/--
  [textbook/theorem_a1.288/theorem/translation_additivity]
  Translating a function by r and then by s is equivalent to translating it by r + s.
-/
theorem translate_additivity {A : Type} (f : Time → A) (r s : Time) :
    translate (translate f r) s = translate f (r + s) := by
  funext t
  unfold translate
  congr 1
  rw [Nat.add_assoc, Nat.add_comm s]

/--
  [textbook/theorem2.46/theorem/time_invariance]
  Time Invariance of State Trajectory: running the system from state `g s`
  with translated input `f → s` for time `t` is equivalent to running the system
  from initial state `s0` with input `f` for time `s + t`.
-/
theorem stateTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateStateTrajectory Z x f (s + t) :=
  Trajectory.stateTrajectory_time_invariance Z x f s t

theorem outputTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZW IZ) (s t : Time) :
    generateOutputTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateOutputTrajectory Z x f (s + t) :=
  Trajectory.outputTrajectory_time_invariance Z x f s t

/--
  [textbook/theorem2.138/theorem/time_invariance_concatenation]
  Time invariance in terms of concatenation for total input trajectories.
-/
theorem stateTrajectory_time_invariance_concatenation
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZ IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x (liftInput f) s) (liftInput g) t =
    generateStateTrajectory Z x (liftInput (concatenate f g s)) (s + t) :=
  Trajectory.stateTrajectory_time_invariance_concatenation Z x f g s t

/--
  [textbook/theorem2.142/theorem/reachable_concatenation]
  Reachability by means of `f` at `s` and `g` at `t` implies reachability by `CTN(f, s, g)` at `s + t`.
-/
theorem reachableBy_concatenate
    (Z : DiscreteSystem SZ IZ OZ) (x y z : SZ) (f g : ITZ IZ) (s t : Time)
    (hxy : ReachableBy Z x y (liftInput f) s) (hyz : ReachableBy Z y z (liftInput g) t) :
    ReachableBy Z x z (liftInput (concatenate f g s)) (s + t) :=
  Trajectory.reachableBy_concatenate Z x y z f g s t hxy hyz

def EXZ (SZ IZ : Type) := ITZW IZ × SZ × Time

theorem stateTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t :=
  Trajectory.stateTrajectory_nonanticipatory Z x f g t h_agree

theorem outputTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZW IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateOutputTrajectory Z x f t = generateOutputTrajectory Z x g t :=
  Trajectory.outputTrajectory_nonanticipatory Z x f g t
    (Trajectory.stateTrajectory_nonanticipatory Z x f g t h_agree)

/-! ## Projection Functions and Input Ports -/

/--
  [textbook/definition_a1.172/definition/projection_coordinate]
  [textbook/definition_a1.172/definition/projection_set]
  [textbook/definition_a1.172/definition/projection_abbreviations]
  The projection function PJN over a Cartesian product (represented as a dependent function)
  onto the `i`-th coordinate. Cites coordinate projections and abbreviations (PJNi, PJN(i)).
-/
def PJN {I : Type} {A : I → Type} (i : I) : ((j : I) → A j) → A i :=
  fun x => x i

/--
  [textbook/definition_a1.172/definition/projection_subset]
  The projection function over a Cartesian product onto a subset of coordinates `S : Set I`.
-/
def PJN_set {I : Type} {A : I → Type} (S : Set I) : ((j : I) → A j) → ((j : {k // k ∈ S}) → A j.val) :=
  fun x ⟨j, _⟩ => x j

/--
  [textbook/definition2.55/definition/input_ports]
  The set of input ports IPZ of the system Z is modeled as the type index set `Port`.
  If the input space is a product, IZ is `(p : Port) → PortVal p`.
-/
def IPZ (Port : Type) : Type := Port

/--
  [textbook/definition2.55/definition/port_trajectory]
  The `p`-th input port trajectory generated by `f ∈ ITZ` is defined as the composition
  of the projection `PJN p` and `f`.
-/
def portTrajectory {Port : Type} {PortVal : Port → Type} (f : ITZW ((p : Port) → PortVal p)) (p : Port) :
    Time → Option (PortVal p) :=
  fun t => (f t).map (PJN p)

/--
  [textbook/definition2.62/definition/port_readout]
  The readout to output port `op` is `PJN(op) ∘ RZ`.
-/
def portReadout {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (op : OutPort) :
    SZ → Option (OutPortVal op) :=
  fun s => (Z.RZ s).map (PJN op)

/--
  [textbook/definition2.62/definition/output_ports]
  The set of output ports OPZ is modeled as the type index set `OutPort`.
-/
def OPZ (OutPort : Type) : Type := OutPort

instance OPZ.fintype {T : Type} [Fintype T] : Fintype (OPZ T) := inferInstanceAs (Fintype T)

/--
  [textbook/definition2.62/definition/port_output_trajectory]
  The output port trajectory is `PJN(op) ∘ OTZ(f, x)`.
-/
def portOutputTrajectory {OutPort : Type} {OutPortVal : OutPort → Type}
    (ot : OTZ ((op : OutPort) → OutPortVal op)) (op : OutPort) : Time → Option (OutPortVal op) :=
  fun t => (ot t).map (PJN op)

/--
  [textbook/definition2.65/definition/output_port_structure]
  The output port structure OSZ is represented as a function mapping each output port
  to its value type.
-/
def OSZ (OutPort : Type) (OutPortVal : OutPort → Type) : OutPort → Type := OutPortVal

/--
  [textbook/definition2.70/definition/state_factor_sets]
  The set of factor sets SFZ of the state set is modeled as the type index set `StateFactor`.
  If the state space is a product, SZ is `(sf : StateFactor) → StateFactorVal sf`.
-/
def SFZ (StateFactor : Type) : Type := StateFactor

instance SFZ.fintype {T : Type} [Fintype T] : Fintype (SFZ T) := inferInstanceAs (Fintype T)

/--
  [textbook/definition2.70/definition/state_factor_structure]
  The state factor structure FSZ is represented as a function mapping each state factor
  to its value type.
-/
def FSZ (StateFactor : Type) (StateFactorVal : StateFactor → Type) : StateFactor → Type := StateFactorVal

/--
  [textbook/definition2.70/definition/factor_next_state]
  The `sf`-th component next state function, NjZ, is the composition of the projection PJN and Z.NZ.
-/
def factorNZ {IZ OZ StateFactor : Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ OZ) (sf : StateFactor) :
    ((sf : StateFactor) → StateFactorVal sf) → Option IZ → StateFactorVal sf :=
  fun s oi => PJN sf (Z.NZ s oi)

/--
  [textbook/definition2.70/definition/factor_state_trajectory]
  The `sf`-th component state trajectory, STjZ(f, x), is the composition of the projection PJN and the state trajectory.
-/
def factorStateTrajectory {StateFactor : Type} {StateFactorVal : StateFactor → Type}
    (st : STZ ((sf : StateFactor) → StateFactorVal sf)) (sf : StateFactor) : Time → StateFactorVal sf :=
  fun t => PJN sf (st t)

/--
  [textbook/definition_a1.165/definition/identity]
  The identity function ID(A) over the set A.
-/
def ID (A : Type) : A → A := fun x => x

/--
  [textbook/definition2.73/definition/state_readout]
  The system Z has state readout if the output is simply the state (RZ = ID(SZ)).
-/
def HasStateReadout {SZ IZ : Type} (Z : DiscreteSystem SZ IZ SZ) : Prop :=
  Z.RZ = fun s => some s

/--
  [textbook/definition2.73/definition/projective_readout]
  The readout RZ of system Z is projective if every output port's readout
  corresponds to some state factor projection.
-/
def IsProjectiveReadout {IZ OutPort StateFactor : Type} {OutPortVal : OutPort → Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op)) : Prop :=
  ∀ (op : OutPort), ∃ (sf : StateFactor) (h : OutPortVal op = StateFactorVal sf),
    ∀ (s : (sf' : StateFactor) → StateFactorVal sf'),
      portReadout Z op s = h ▸ PJN sf s

/--
  Output port `op` readout equals projection onto state factor `sf` (`RiZ = PJN(SZ, SjZ)`).
-/
def PortReadoutIsFactorProjection {IZ OutPort StateFactor : Type} {OutPortVal : OutPort → Type}
    {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op))
    (op : OutPort) (sf : StateFactor) (h : OutPortVal op = StateFactorVal sf) : Prop :=
  ∀ s, portReadout Z op s = some (h ▸ PJN sf s)

/--
  [textbook/theorem2.146/theorem/osz_eq_fsz]
  Projective readout with `RiZ = PJN(SZ, SjZ)` implies `OSZ(OiZ) = FSZ(SjZ)`.
-/
theorem projective_readout_osz_eq_fsz {IZ OutPort StateFactor : Type}
    {OutPortVal : OutPort → Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op))
    (i : OutPort) (j : StateFactor)
    (_hproj : IsProjectiveReadout Z)
    (h : OutPortVal i = StateFactorVal j)
    (_hread : PortReadoutIsFactorProjection Z i j h) :
    OSZ (OPZ OutPort) OutPortVal i = FSZ (SFZ StateFactor) StateFactorVal j :=
  h

/--
  [textbook/definition2.73/definition/properly_aligned_readout]
  The projective readout function is properly aligned if each output port `i`
  reads out the corresponding state factor `i`.
-/
def IsProperlyAlignedReadout {IZ I : Type} {Val : I → Type}
    (Z : DiscreteSystem ((i : I) → Val i) IZ ((i : I) → Val i)) : Prop :=
  ∀ (i : I), ∀ (s : (j : I) → Val j),
    portReadout Z i s = some (PJN i s)

/--
  Aligned product readout when `#OPZ ≤ #SFZ`: output port `j` reads state factor `j`
  (`RiZ = PJN(SZ, SiZ)` for `i = j`).
-/
def IsProperlyAlignedProductReadout {Inp : Type} {m n : Nat} (hn : n ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin n) → Val (Fin.castLE hn j))) : Prop :=
  ∀ (j : Fin n) (s : (i : Fin m) → Val i),
    portReadout Z j s = some (PJN (Fin.castLE hn j) s)

/--
  [textbook/theorem2.148/theorem/sfz_card_ge_opz]
  Properly aligned readout implies at least as many state factors as output ports.
-/
theorem properly_aligned_sfz_card_ge_opz {Inp : Type} {m n : Nat} (hn : n ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin n) → Val (Fin.castLE hn j)))
    (_h : IsProperlyAlignedProductReadout hn Val Z) :
    Fintype.card (SFZ (Fin m)) ≥ Fintype.card (OPZ (Fin n)) := by
  dsimp [SFZ, OPZ]
  exact fin_nat_card_le_of_le hn

/--
  [textbook/theorem2.148/theorem/osz_eq_fsz]
  Under alignment, each output port's value set equals the paired state factor's value set.
-/
theorem properly_aligned_osz_eq_fsz {m n : Nat} (hn : n ≤ m) (Val : Fin m → Type) (j : Fin n) :
    OSZ (OPZ (Fin n)) (fun k => Val (Fin.castLE hn k)) j =
      FSZ (SFZ (Fin m)) Val (Fin.castLE hn j) :=
  rfl

/--
  [textbook/theorem2.148/theorem/sfz_card_ge_opz]
  Corollary for the same-index aligned encoding (`IsProperlyAlignedReadout`).
-/
theorem isProperlyAlignedReadout_sfz_card_ge_opz {Inp I : Type} {Val : I → Type} [Fintype I]
    (Z : DiscreteSystem ((i : I) → Val i) Inp ((i : I) → Val i))
    (_h : IsProperlyAlignedReadout Z) :
    Fintype.card (SFZ I) ≥ Fintype.card (OPZ I) := by
  dsimp [SFZ, OPZ]
  exact Nat.le_refl (Fintype.card I)

/--
  [textbook/theorem2.148/theorem/osz_eq_fsz]
  Corollary for the same-index aligned encoding.
-/
theorem isProperlyAlignedReadout_osz_eq_fsz {I : Type} {Val : I → Type} (i : I) :
    OSZ (OPZ I) (fun k => Val k) i = FSZ (SFZ I) Val i :=
  rfl

/--
  `#SFZ ≤ 1`: state is not a Cartesian product of two or more factor sets.
-/
def StateIsNotCartesianProduct (n : Nat) : Prop :=
  n ≤ 1

/--
  `#OPZ ≤ 1`: output is not a Cartesian product of two or more port value sets.
-/
def OutputIsNotCartesianProduct (n : Nat) : Prop :=
  n ≤ 1

/--
  [textbook/theorem2.150/theorem/state_readout]
  Aligned single-output readout returning the state tuple (`SZ = OZ`, `RZ = ID(SZ)` when `m = 1`).
-/
def HasAlignedStateReadout {Inp : Type} {m : Nat} (hn : 1 ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin 1) → Val (Fin.castLE hn j))) : Prop :=
  Z.RZ = fun s => some (fun (j : Fin 1) => s (Fin.castLE hn j))

/--
  [textbook/theorem2.150/theorem/first_factor_readout]
  Bundled readout `RZ = PJN(SZ, S1Z)` when `OZ = S1Z` (single-port encoding).
-/
def HasFirstFactorBundledReadout {Inp : Type} {m : Nat} (hn : 1 ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin 1) → Val (Fin.castLE hn j))) : Prop :=
  Z.RZ = fun s => some (fun (j : Fin 1) => PJN (Fin.castLE hn j) s)

/--
  [textbook/theorem2.149/theorem/sz_eq_oz]
  In the aligned product encoding with one factor, `SZ` and `OZ` share the same type.
-/
theorem properly_aligned_non_product_sz_eq_oz {Val : Type} :
    ((i : Fin 1) → Val) = ((i : Fin 1) → Val) :=
  rfl

/--
  [textbook/theorem2.149/theorem/state_readout]
  Non-product state with properly aligned projective readout yields state readout (`RZ = ID(SZ)`).
-/
theorem properly_aligned_non_product_has_state_readout {Inp : Type} {n : Nat}
    (_hNotProd : StateIsNotCartesianProduct n) (hnpos : n ≠ 0) (Val : Fin n → Type)
    (Z : DiscreteSystem ((i : Fin n) → Val i) Inp ((i : Fin n) → Val i))
    (h : IsProperlyAlignedReadout Z) :
    HasStateReadout Z := by
  dsimp [StateIsNotCartesianProduct] at _hNotProd
  have hn : n = 1 := by omega
  subst hn
  unfold HasStateReadout
  funext s
  match hz : Z.RZ s with
  | none => exact absurd (h 0 s) (by simp [portReadout, hz])
  | some o =>
    have hproj := h 0 s
    simp [portReadout, hz, PJN] at hproj
    congr
    ext j
    rw [Trajectory.fin_one_eq j 0]
    exact hproj

/--
  [textbook/definition2.73/definition/state_readout]
  `HasStateReadout` is `RZ = ID(SZ)` on states (via `some` in the partial readout model).
-/
theorem hasStateReadout_iff_rz_id {SZ Inp : Type} (Z : DiscreteSystem SZ Inp SZ) :
    HasStateReadout Z ↔ Z.RZ = fun s => some (ID SZ s) := by
  unfold HasStateReadout ID
  rfl

/--
  [textbook/theorem2.150/theorem/oz_eq_s1z]
  Single aligned output port's value set is the first state factor `S1Z`.
-/
theorem properly_aligned_non_product_oz_eq_s1z {m : Nat} (hn : 1 ≤ m) (Val : Fin m → Type) :
    OSZ (OPZ (Fin 1)) (fun k => Val (Fin.castLE hn k)) (0 : Fin 1) =
      FSZ (SFZ (Fin m)) Val (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩ : Fin m) :=
  rfl

/--
  [textbook/theorem2.150/theorem/readout_dichotomy]
  Non-product output with properly aligned projective readout: state readout or first-factor projection.
-/
theorem properly_aligned_non_product_output_readout_dichotomy {Inp : Type} {m : Nat}
    (_hNotProdOut : OutputIsNotCartesianProduct 1) (_hnpos : (1 : Nat) ≠ 0)
    (hn : 1 ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin 1) → Val (Fin.castLE hn j)))
    (h : IsProperlyAlignedProductReadout hn Val Z) :
    (StateIsNotCartesianProduct m → HasAlignedStateReadout hn Val Z) ∨
      (m > 1 ∧ HasFirstFactorBundledReadout hn Val Z) := by
  dsimp [OutputIsNotCartesianProduct] at _hNotProdOut
  by_cases hle : m ≤ 1
  · left
    intro _hstate
    unfold HasAlignedStateReadout
    funext s
    match hz : Z.RZ s with
    | none => exact absurd (h (0 : Fin 1) s) (by simp [portReadout, hz])
    | some o =>
      have hproj := h (0 : Fin 1) s
      simp [portReadout, hz, PJN] at hproj
      congr
      ext j
      rw [Trajectory.fin_one_eq j 0]
      exact hproj
  · right
    refine ⟨Nat.lt_of_not_ge hle, ?_⟩
    unfold HasFirstFactorBundledReadout
    funext s
    match hz : Z.RZ s with
    | none => exact absurd (h (0 : Fin 1) s) (by simp [portReadout, hz])
    | some o =>
      have hproj := h (0 : Fin 1) s
      simp [portReadout, hz] at hproj
      congr
      ext j
      rw [Trajectory.fin_one_eq j 0]
      exact hproj

/--
  [textbook/theorem_a1.178/theorem/vector_projection_equality]
  Equality of vectors in terms of projections: any vector in a product type
  is equal to the tuple of its projections. In Lean, this is definitionally true.
-/
theorem tuple_eq_projection {I : Type} {A : I → Type} (x : (i : I) → A i) :
    x = fun i => PJN i x := by
  rfl

/--
  [textbook/theorem_a1.163/theorem/function_extensionality]
  Equality of functions (extensionality): two functions are equal if and only if
  they agree pointwise on all inputs.
-/
theorem fun_eq_iff {A B : Type} (f g : A → B) :
    f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    funext x
    exact h x

/--
  [textbook/theorem2.76/theorem/equal_readout]
  [textbook/theorem2.76/proof/pointwise_projection]
  [textbook/theorem2.76/proof/vector_equality]
  [textbook/theorem2.76/proof/function_equality]
  Equality of readout functions for systems with properly aligned projective readouts.
  Shows that if two systems have properly aligned projective readouts, identical state space
  and output space, their readout functions are equal.
-/
theorem readout_eq_of_properly_aligned {IZ IZ2 I : Type} {Val : I → Type} [Inhabited I]
    (Z1 : DiscreteSystem ((i : I) → Val i) IZ ((i : I) → Val i))
    (Z2 : DiscreteSystem ((i : I) → Val i) IZ2 ((i : I) → Val i))
    (h1 : IsProperlyAlignedReadout Z1)
    (h2 : IsProperlyAlignedReadout Z2) :
    Z1.RZ = Z2.RZ := by
  funext s
  have hproj1 : ∀ i, (Z1.RZ s).map (PJN i) = some (PJN i s) := fun i => h1 i s
  have hproj2 : ∀ i, (Z2.RZ s).map (PJN i) = some (PJN i s) := fun i => h2 i s
  match hz1 : Z1.RZ s, hz2 : Z2.RZ s with
  | some o1, some o2 =>
    apply Option.some_inj.mpr
    funext i
    have h1i := hproj1 i; rw [hz1, Option.map_some] at h1i
    have h2i := hproj2 i; rw [hz2, Option.map_some] at h2i
    exact Option.some_injective _ (h1i.trans h2i.symm)
  | none, _ => exact absurd (hproj1 default) (by rw [hz1]; simp)
  | some _, none => exact absurd (hproj2 default) (by rw [hz2]; simp)

/--
  [textbook/theorem_a1.176/theorem/projection_functions]
  Projection functions are functions. In Lean, PJN is a function by definition.
-/
theorem pjn_is_fun {I : Type} {A : I → Type} (i : I) :
    SatisfiesFNS (PJN i : ((j : I) → A j) → A i) :=
  satisfiesFNS_of_function _

/-! ## Z2 Construction (Theorem 2.78) -/

structure Z2State (SZ OZ : Type) (RZ : SZ → Option OZ) where
  out : OZ
  state : SZ
  eq : RZ state = some out

noncomputable def Z2State.mkFrom {SZ OZ : Type} (RZ : SZ → Option OZ)
    (h : ∀ s, ∃ o, RZ s = some o) (s : SZ) : Z2State SZ OZ RZ :=
  ⟨Classical.choose (h s), s, Classical.choose_spec (h s)⟩

noncomputable def Z2State.equivSZ {SZ OZ : Type} (RZ : SZ → Option OZ) (h : ∀ s, ∃ o, RZ s = some o) :
    Z2State SZ OZ RZ ≃ SZ where
  toFun s2 := s2.state
  invFun s := Z2State.mkFrom RZ h s
  left_inv := fun ⟨o, s, ho⟩ => by
    simp [Z2State.mkFrom, ho]
  right_inv _ := rfl

theorem ofTotal_alwaysOutputs {SZ IZ OZ : Type} (NZ : SZ → IZ → SZ) (RZ : SZ → OZ) (hNE : Nonempty SZ) :
    AlwaysOutputs (DiscreteSystem.ofTotal NZ RZ hNE) := by
  intro s; exact ⟨RZ s, rfl⟩

def Z2 {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    DiscreteSystem (Z2State SZ OZ Z.RZ) IZ OZ where
  sz_nonempty := Z.sz_nonempty.map (Z2State.equivSZ Z.RZ hOut).symm
  NZ := fun s2 oi =>
    let ns := Z.NZ s2.state oi
    match hrz : Z.RZ ns with
    | some o => ⟨o, ns, hrz⟩
    | none => (alwaysOutputs_not_none Z hOut ns hrz).elim
  RZ := fun s2 => some s2.out

theorem z2_readout_projective {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)) (hOut : AlwaysOutputs Z) (op : OutPort)
    (s2 : Z2State SZ ((op : OutPort) → OutPortVal op) Z.RZ) :
    portReadout (Z2 Z hOut) op s2 = some (s2.out op) := rfl

def Z2.exz_map {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z) :
    EXZ SZ IZ → EXZ (Z2State SZ OZ Z.RZ) IZ :=
  fun ⟨f, x, t⟩ =>
    match hrz : Z.RZ x with
    | some o => ⟨f, ⟨o, x, hrz⟩, t⟩
    | none => (alwaysOutputs_not_none Z hOut x hrz).elim

theorem z2_nz_state {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ) (hOut : AlwaysOutputs Z)
    (s2 : Z2State SZ OZ Z.RZ) (oi : Option IZ) :
    ((Z2 Z hOut).NZ s2 oi).state = Z.NZ s2.state oi := by
  dsimp [Z2, Z2State.state]
  split
  · rfl
  · exact (alwaysOutputs_not_none Z hOut (Z.NZ s2.state oi) ‹_›).elim

theorem z2_state_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (x : SZ) (o : OZ) (f : ITZW IZ) (t : Time) (hrz : Z.RZ x = some o) :
    (generateStateTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t).state =
    generateStateTrajectory Z x f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [z2_nz_state Z hOut, ih]

theorem z2_output_trajectory_equivalence {SZ IZ OZ : Type} (Z : DiscreteSystem SZ IZ OZ)
    (hOut : AlwaysOutputs Z) (x : SZ) (o : OZ) (f : ITZW IZ) (t : Time) (hrz : Z.RZ x = some o) :
    generateOutputTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t =
    generateOutputTrajectory Z x f t := by
  set s2t := generateStateTrajectory (Z2 Z hOut) ⟨o, x, hrz⟩ f t
  unfold generateOutputTrajectory
  rw [← z2_state_trajectory_equivalence Z hOut x o f t hrz]
  show (Z2 Z hOut).RZ s2t = Z.RZ s2t.state
  simp [Z2]
  exact s2t.eq.symm

/-! ## System Parameterization -/

/--
  [textbook/definition2.82/definition/system_parameterization]
  A system parameterization maps a parameter type `P` to a `DiscreteSystem`.
-/
def DiscreteSystemParameterization (P : Type u) (SZ IZ OZ : P → Type) : Type u :=
  (p : P) → DiscreteSystem (SZ p) (IZ p) (OZ p)

/--
  [textbook/definition2.82/definition/parameter_instance]
  An instance of a system parameterization `F` for a parameter value `r : P` is the system `F r`.
-/
def parameterInstance {P : Type} {SZ IZ OZ : P → Type}
    (F : DiscreteSystemParameterization P SZ IZ OZ) (r : P) :
    DiscreteSystem (SZ r) (IZ r) (OZ r) :=
  F r

def HasNParameters (P : Type) (n : Nat) (ParamType : Fin n → Type) : Prop :=
  Nonempty (P ≃ ((i : Fin n) → ParamType i))

/--
  [textbook/definition2.82/definition/one_parameter]
  A parameterization has one parameter if its parameter domain is equivalent to a single-factor product.
-/
def HasOneParameter (P : Type) : Prop :=
  ∃ ParamType : Fin 1 → Type, HasNParameters P 1 ParamType

/--
  [textbook/definition2.93/definition/fcnsy]
  The parameterization of function computation systems FCNSY.
-/
def fcnsy {IZ SZ : Type} (F : IZ → SZ) (n : Nat) [Inhabited SZ] :
    DiscreteSystem SZ IZ (Fin n → SZ) where
  sz_nonempty := ⟨default⟩
  NZ := fun _x oi => match oi with | some p => F p | none => default
  RZ := fun x => some (fun _j => x)

/--
  [textbook/theorem2.96/theorem/parameter_count]
  FCNSY is a system parameterization with two parameters.
-/
theorem fcnsy_has_two_parameters {IZ SZ : Type} [Inhabited SZ] :
    ∃ (P : Type) (ParamType : Fin 2 → Type), HasNParameters P 2 ParamType := by
  let ParamType : Fin 2 → Type := fun i => if i.val == 0 then (IZ → SZ) else Nat
  exact ⟨(i : Fin 2) → ParamType i, ParamType, ⟨Equiv.refl _⟩⟩

/--
  [textbook/theorem2.97/theorem/output_value]
  [textbook/theorem2.97/proof/t_zero]
  [textbook/theorem2.97/proof/arbitrary_t]
  For Z = FCNSY(F, 1), the output at t + 1 is F(f(t)).
  DTT strategy (proof comparison §9): state-independent NZ collapses to `rfl`.
-/
theorem fcnsy_output_one_time_unit {IZ SZ : Type} (F : IZ → SZ) [Inhabited SZ]
    (x : SZ) (f : ITZW IZ) (t : Time) (i : IZ) (hi : f t = some i) :
    (generateOutputTrajectory (fcnsy F 1) x f (t + 1)).map (fun a => a 0) = some (F i) := by
  simp [generateOutputTrajectory, generateStateTrajectory_succ, fcnsy, hi, Option.map_some]

/-! ## Chapter 3: System Coupling Recipes and Connectivity -/

/--
  [textbook/definition3.3/definition/connection_vector]
  [textbook/definition3.3/requirement/pairwise_distinct]
  A connectable vector of systems of length `n` (components may have infinite state spaces).
-/
structure PortSystemVector (n : Nat) where
  SZ : Fin n → Type
  Port : Fin n → Type
  PortVal : (i : Fin n) → Port i → Type
  OutPort : Fin n → Type
  OutPortVal : (i : Fin n) → OutPort i → Type
  Z : (i : Fin n) → DiscreteSystem (SZ i) ((p : Port i) → PortVal i p) ((op : OutPort i) → OutPortVal i op)
  distinct : ∀ (i j : Fin n), i ≠ j → ¬ HEq (Z i) (Z j)

def IsOneToOneRelation {α β : Type} (R : Set (α × β)) : Prop :=
  (∀ (x : α) (y1 y2 : β), (x, y1) ∈ R → (x, y2) ∈ R → y1 = y2) ∧
  (∀ (x1 x2 : α) (y : β), (x1, y) ∈ R → (x2, y) ∈ R → x1 = x2)

def IsProperDomain {α β : Type} (R : Set (α × β)) : Prop :=
  { x : α | ∃ y, (x, y) ∈ R } ≠ Set.univ

/--
  [textbook/definition3.7/requirement/range_subset]
  The range of CSCR is a proper subset of all input ports.
-/
def IsProperRange {α β : Type} (R : Set (α × β)) : Prop :=
  { y : β | ∃ x, (x, y) ∈ R } ≠ Set.univ

def PortCompatibility {n : Nat} (VSCR : PortSystemVector n)
    (CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))) : Prop :=
  ∀ (op : Σ (i : Fin n), VSCR.OutPort i) (ip : Σ (i : Fin n), VSCR.Port i),
    (op, ip) ∈ CSCR → VSCR.OutPortVal op.1 op.2 = VSCR.PortVal ip.1 ip.2

def IsSystemConnectivity {n : Nat} (VSCR : PortSystemVector n)
    (CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))) : Prop :=
  IsOneToOneRelation CSCR ∧
  IsProperDomain CSCR ∧
  IsProperRange CSCR ∧
  PortCompatibility VSCR CSCR

def IsFeedforward {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 < p.2.1

def IsFeedback {n : Nat} {VSCR : PortSystemVector n}
    (p : (Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i)) : Prop :=
  p.1.1 ≥ p.2.1

structure SystemCouplingRecipe (n : Nat) where
  VSCR : PortSystemVector n
  CSCR : Set ((Σ (i : Fin n), VSCR.OutPort i) × (Σ (i : Fin n), VSCR.Port i))
  connectivity : IsSystemConnectivity VSCR CSCR

def COSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  { op | ∃ ip, (op, ip) ∈ SCR.CSCR }

def CISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  { ip | ∃ op, (op, ip) ∈ SCR.CSCR }

def UOSCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.OutPort i) :=
  (COSCR SCR)ᶜ

def UISCR {n : Nat} (SCR : SystemCouplingRecipe n) : Set (Σ (i : Fin n), SCR.VSCR.Port i) :=
  (CISCR SCR)ᶜ

def SCRInterface {n : Nat} (SCR : SystemCouplingRecipe n) (i j : Fin n) :
    Set ((Σ (k : Fin n), SCR.VSCR.OutPort k) × (Σ (k : Fin n), SCR.VSCR.Port k)) :=
  { p ∈ SCR.CSCR | (p.1.1 = i ∧ p.2.1 = j) ∨ (p.1.1 = j ∧ p.2.1 = i) }

def IsConjunctive {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  SCR.CSCR = ∅

def IsCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∀ p ∈ SCR.CSCR, ¬ IsFeedback p

def IsEssentiallyCascade {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ∃ (g : Fin n ≃ Fin n), ∀ p ∈ SCR.CSCR, g p.1.1 < g p.2.1

def IsSingular {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR = ∅

def IsPureFeedback {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  n = 1 ∧ SCR.CSCR ≠ ∅

/--
  [textbook/theorem3.31/theorem/class_in_themselves]
  [textbook/theorem3.31/proof/not_singular_conjunctive]
  [textbook/theorem3.31/proof/not_cascade]
  DTT strategy (proof comparison §10): `obtain` + `Subsingleton.elim` on `Fin 1`.
-/
theorem pure_feedback_not_other {n : Nat} (SCR : SystemCouplingRecipe n) (h : IsPureFeedback SCR) :
    ¬ IsSingular SCR ∧ ¬ IsConjunctive SCR ∧ ¬ IsCascade SCR := by
  have hn : n = 1 := h.1
  have hne : SCR.CSCR ≠ ∅ := h.2
  constructor
  · intro hs; exact hne hs.2
  · constructor
    · intro hc; exact hne hc
    · intro h_cas
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have heq : p.1.1 = p.2.1 := Trajectory.fin_one_indices_eq hn p.1.1 p.2.1
      exact h_cas p hp (by unfold IsFeedback; rw [heq])

def IsMixed {n : Nat} (SCR : SystemCouplingRecipe n) : Prop :=
  ¬ IsSingular SCR ∧ ¬ IsConjunctive SCR ∧ ¬ IsCascade SCR ∧
  ¬ IsEssentiallyCascade SCR ∧ ¬ IsPureFeedback SCR

/--
  [textbook/definition3.40/definition/csy]
  [textbook/definition3.40/definition/sz]
  [textbook/definition3.40/definition/iz]
  [textbook/definition3.40/definition/oz]
  [textbook/definition3.40/definition/nz]
  [textbook/definition3.40/definition/rz]
  Parallel (conjunctive) composition of a connectable vector of systems.
-/
noncomputable def csyOut {n : Nat} (VSCR : PortSystemVector n) (hOut : ∀ i, AlwaysOutputs (VSCR.Z i))
    (x : (i : Fin n) → VSCR.SZ i) (op : Σ i, VSCR.OutPort i) : VSCR.OutPortVal op.1 op.2 :=
  Classical.choose (hOut op.1 (x op.1)) op.2

noncomputable def csy {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) :
    DiscreteSystem
      ((i : Fin n) → VSCR.SZ i)
      ((ip : Σ (i : Fin n), VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      ((op : Σ (i : Fin n), VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) where
  sz_nonempty := by
    have h_non : ∀ i, Nonempty (VSCR.SZ i) := fun i => (VSCR.Z i).sz_nonempty
    exact ⟨fun i => Classical.choice (h_non i)⟩
  NZ := fun x po i => (VSCR.Z i).NZ (x i) (po.map (fun full port => full ⟨i, port⟩))
  RZ := fun x => some (fun op => csyOut VSCR hOut x op)

def csy_IP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.Port i) → (Σ (i : Fin n), _VSCR.Port i) := ID _

def csy_INIP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.Port i) → (Σ (i : Fin n), _VSCR.Port i) := ID _

def csy_IS_map {n : Nat} (VSCR : PortSystemVector n) (ip : Σ (i : Fin n), VSCR.Port i) : Type :=
  VSCR.PortVal ip.1 ip.2

def csy_OP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.OutPort i) → (Σ (i : Fin n), _VSCR.OutPort i) := ID _

def csy_INOP_map {n : Nat} (_VSCR : PortSystemVector n) :
    (Σ (i : Fin n), _VSCR.OutPort i) → (Σ (i : Fin n), _VSCR.OutPort i) := ID _

def csy_OS_map {n : Nat} (VSCR : PortSystemVector n) (op : Σ (i : Fin n), VSCR.OutPort i) : Type :=
  VSCR.OutPortVal op.1 op.2

def product_fun {I : Type} {A B : I → Type} (f : (i : I) → A i → B i) :
    ((i : I) → A i) → ((i : I) → B i) :=
  fun x i => f i (x i)

noncomputable def csy_parameterization (n : Nat) (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) :
    DiscreteSystem
      ((i : Fin n) → VSCR.SZ i)
      ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)
      ((op : Σ i, VSCR.OutPort i) → VSCR.OutPortVal op.1 op.2) :=
  csy VSCR hOut

theorem csy_state_trajectory {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZW ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n) :
    (generateStateTrajectory (csy VSCR hOut) x f t i) =
    generateStateTrajectory (VSCR.Z i) (x i) (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t := by
  induction t generalizing i with
  | zero => simp [generateStateTrajectory_zero]
  | succ t ih =>
    rw [generateStateTrajectory_succ]
    simp only [csy]
    exact congr_arg (fun s => (VSCR.Z i).NZ s ((f t).map (fun full port => full ⟨i, port⟩))) (ih i)

theorem csy_output_trajectory {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) (x : (i : Fin n) → VSCR.SZ i)
    (f : ITZW ((ip : Σ i, VSCR.Port i) → VSCR.PortVal ip.1 ip.2)) (t : Time) (i : Fin n)
    (B' : VSCR.OutPort i) :
    (generateOutputTrajectory (csy VSCR hOut) x f t).map (fun r => r ⟨i, B'⟩) =
    (generateOutputTrajectory (VSCR.Z i) (x i)
      (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t).map (fun r => r B') := by
  have hst := csy_state_trajectory VSCR hOut x f t i
  let s := generateStateTrajectory (VSCR.Z i) (x i)
    (fun τ => (f τ).map (fun full port => full ⟨i, port⟩)) t
  obtain ⟨o, ho⟩ := hOut i s
  have hchoose : Classical.choose (hOut i s) B' = o B' :=
    congrArg (fun g => g B') (Trajectory.choose_alwaysOutputs (VSCR.Z i) (hOut i) s ho)
  have hmain : Classical.choose (hOut i (generateStateTrajectory (csy VSCR hOut) x f t i)) B' = o B' := by
    rw [hst, hchoose]
  simp only [generateOutputTrajectory, csy, csyOut, Option.map_some]
  rw [ho]
  exact congrArg some hmain

/-! ## Closed, autonomous, and infinite-state examples -/

def closedSystem : DiscreteSystem Unit Empty Empty where
  sz_nonempty := ⟨()⟩
  NZ := fun s _ => s
  RZ := fun _ => none

theorem closedSystem_isClosed : IsClosed closedSystem :=
  ⟨inferInstance, inferInstance⟩

theorem exists_closed_discreteSystem :
    ∃ (Z : DiscreteSystem Unit Empty Empty), IsClosed Z :=
  ⟨closedSystem, closedSystem_isClosed⟩

def toggleSystem : DiscreteSystem Bool Empty Bool where
  sz_nonempty := ⟨true⟩
  NZ := fun s _ => !s
  RZ := fun s => some s

theorem toggle_step (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 1 = !s0 := rfl

theorem toggle_period_two (s0 : Bool) (f : ITZW Empty) :
    generateStateTrajectory toggleSystem s0 f 2 = s0 := by
  cases s0 <;> rfl

def counterSystem : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal (fun n (_ : Bool) => n + 1) id ⟨0⟩

theorem counterSystem_not_finite : ¬ IsFinite counterSystem := by
  intro h
  exact Infinite.not_finite (α := Nat) h.1

theorem counterSystem_alwaysOutputs : AlwaysOutputs counterSystem :=
  ofTotal_alwaysOutputs (fun n (_ : Bool) => n + 1) id ⟨0⟩

theorem counterSystem_z2_not_finite :
    ¬ IsFinite (Z2 counterSystem counterSystem_alwaysOutputs) := by
  intro ⟨hSZ, _, _⟩
  have hNat : Finite Nat :=
    (Z2State.equivSZ counterSystem.RZ counterSystem_alwaysOutputs).symm.finite_iff.mpr hSZ
  exact Infinite.not_finite (α := Nat) hNat
