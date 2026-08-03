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

/--
  [textbook/exercise3.120/theorem/conjunctive_input_port_map]
  `IP&(V,Z) ∈ FNS(IPZ, 1TO1, ONTO, ⋃{IPZi})`.
-/
theorem csy_IP_map_inFNS1TO1Onto {n : Nat} (VSCR : PortSystemVector n) :
    InFNS1TO1Onto (csy_IP_map VSCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.120/theorem/conjunctive_inverse_input_port_map]
  `INIP&(V,Z) ∈ FNS(⋃{IPZi}, 1TO1, ONTO, IPZ)`.
-/
theorem csy_INIP_map_inFNS1TO1Onto {n : Nat} (VSCR : PortSystemVector n) :
    InFNS1TO1Onto (csy_INIP_map VSCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.120/theorem/conjunctive_input_port_structure]
  `IS&(V,Z) = ISZ` on conjunctive input ports.
-/
theorem csy_IS_map_eq {n : Nat} (VSCR : PortSystemVector n)
    (ip : Σ (i : Fin n), VSCR.Port i) :
    csy_IS_map VSCR ip = VSCR.PortVal ip.1 ip.2 := rfl

/--
  [textbook/exercise3.120/theorem/conjunctive_output_port_map]
  `OP&(V,Z) ∈ FNS(OPZ, 1TO1, ONTO, ⋃{OPZi})`.
-/
theorem csy_OP_map_inFNS1TO1Onto {n : Nat} (VSCR : PortSystemVector n) :
    InFNS1TO1Onto (csy_OP_map VSCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.120/theorem/conjunctive_output_port_structure]
  `OS&(V,Z) = OSZ` on conjunctive output ports.
-/
theorem csy_OS_map_eq {n : Nat} (VSCR : PortSystemVector n)
    (op : Σ (i : Fin n), VSCR.OutPort i) :
    csy_OS_map VSCR op = VSCR.OutPortVal op.1 op.2 := rfl

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

/-! ## Chapter 3: Resultant Systems (RSY) -/

/--
  [textbook/definition3.47/definition/unconnected_input_port]
  An unconnected input port of a coupling recipe (element of `UISCR`).
-/
def UnconnInPort {n : Nat} (SCR : SystemCouplingRecipe n) : Type :=
  { ip : Σ (i : Fin n), SCR.VSCR.Port i // ip ∈ UISCR SCR }

/--
  [textbook/definition3.47/definition/unconnected_output_port]
  An unconnected output port of a coupling recipe (element of `UOSCR`).
-/
def UnconnOutPort {n : Nat} (SCR : SystemCouplingRecipe n) : Type :=
  { op : Σ (i : Fin n), SCR.VSCR.OutPort i // op ∈ UOSCR SCR }

/--
  [textbook/definition3.47/definition/iz]
  External input space: values on unconnected input ports (`UISCR`).
-/
def rsy_IZ {n : Nat} (SCR : SystemCouplingRecipe n) : Type :=
  (ip : UnconnInPort SCR) → SCR.VSCR.PortVal ip.val.1 ip.val.2

/--
  [textbook/definition3.47/definition/oz]
  External output space: values on unconnected output ports (`UOSCR`).
-/
def rsy_OZ {n : Nat} (SCR : SystemCouplingRecipe n) : Type :=
  (op : UnconnOutPort SCR) → SCR.VSCR.OutPortVal op.val.1 op.val.2

/--
  [textbook/definition3.47/definition/sz]
  State space of the resultant: product of component state spaces.
-/
def rsy_SZ {n : Nat} (SCR : SystemCouplingRecipe n) : Type :=
  (i : Fin n) → SCR.VSCR.SZ i

lemma mem_ciscr_iff {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) :
    ip ∈ CISCR SCR ↔ ∃ op, (op, ip) ∈ SCR.CSCR := Iff.rfl

lemma mem_uiscr_iff {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) :
    ip ∈ UISCR SCR ↔ ip ∉ CISCR SCR := by
  simp [UISCR]

/--
  [textbook/definition3.47/definition/connected_output]
  The output port feeding a connected input port `ip` via `CSCR`.
-/
noncomputable def connectedOutput {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (h : ip ∈ CISCR SCR) :
    Σ (i : Fin n), SCR.VSCR.OutPort i :=
  Classical.choose (mem_ciscr_iff SCR ip |>.mp h)

lemma connectedOutput_spec {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (h : ip ∈ CISCR SCR) :
    (connectedOutput SCR ip h, ip) ∈ SCR.CSCR :=
  Classical.choose_spec (mem_ciscr_iff SCR ip |>.mp h)

noncomputable def rsyOutAt {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) (x : rsy_SZ SCR)
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) : SCR.VSCR.OutPortVal op.1 op.2 :=
  csyOut SCR.VSCR hOut x op

/--
  [textbook/definition3.47/definition/component_input]
  Resolve the input function for component `i` from external inputs and feedback wiring.
-/
noncomputable def rsy_component_input_fun {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) : (p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p := by
  classical
  intro port
  let ip : Σ (j : Fin n), SCR.VSCR.Port j := ⟨i, port⟩
  by_cases hU : ip ∈ UISCR SCR
  · exact extIn ⟨ip, hU⟩
  · have hC : ip ∈ CISCR SCR := by simpa [UISCR, Set.mem_compl_iff] using hU
    let op := connectedOutput SCR ip hC
    have hop : (op, ip) ∈ SCR.CSCR := connectedOutput_spec SCR ip hC
    have hcomp := SCR.connectivity.2.2.2 op ip hop
    exact hcomp ▸ rsyOutAt SCR hOut x op

lemma rsy_component_input_uiscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : SCR.VSCR.Port i) (hU : ⟨i, port⟩ ∈ UISCR SCR) :
    rsy_component_input_fun SCR hOut i extIn x port = extIn ⟨⟨i, port⟩, hU⟩ := by
  classical
  dsimp [rsy_component_input_fun]
  simp [hU]

lemma rsy_component_input_ciscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : SCR.VSCR.Port i) (hC : ⟨i, port⟩ ∈ CISCR SCR) :
    rsy_component_input_fun SCR hOut i extIn x port =
      let op := connectedOutput SCR ⟨i, port⟩ hC
      have hop : (op, ⟨i, port⟩) ∈ SCR.CSCR := connectedOutput_spec SCR ⟨i, port⟩ hC
      SCR.connectivity.2.2.2 op ⟨i, port⟩ hop ▸ rsyOutAt SCR hOut x op := by
  classical
  dsimp [rsy_component_input_fun]
  have hU : ⟨i, port⟩ ∉ UISCR SCR := by simpa [UISCR, CISCR] using hC
  simp [hU]

/--
  [textbook/definition3.47/definition/nz]
  Next-state: each component updates via `NZi` on resolved inputs.
-/
noncomputable def rsy_NZ {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR) (po : Option (rsy_IZ SCR))
    (i : Fin n) : SCR.VSCR.SZ i :=
  (SCR.VSCR.Z i).NZ (x i) (po.map (fun extIn => rsy_component_input_fun SCR hOut i extIn x))

/--
  [textbook/definition3.47/definition/rz]
  Readout: projections of component readouts on unconnected output ports.
-/
noncomputable def rsy_RZ {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR) : Option (rsy_OZ SCR) :=
  some (fun op : UnconnOutPort SCR => rsyOutAt SCR hOut x op.val)

/--
  [textbook/definition3.47/definition/rsy]
  Resultant system `RSY(SCR)` with external I/O on unconnected ports and feedback via `CSCR`.
  When `CSCR = ∅`, this coincides with `csy SCR.VSCR` on isomorphic I/O spaces.
-/
noncomputable def rsy {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :
    DiscreteSystem (rsy_SZ SCR) (rsy_IZ SCR) (rsy_OZ SCR) where
  sz_nonempty := by
    have h_non : ∀ i, Nonempty (SCR.VSCR.SZ i) := fun i => (SCR.VSCR.Z i).sz_nonempty
    exact ⟨fun i => Classical.choice (h_non i)⟩
  NZ := rsy_NZ SCR hOut
  RZ := rsy_RZ SCR hOut

/--
  [textbook/definition3.47/definition/rsy_param]
  Parameter bundle for `RSY`: coupling recipe plus total component readouts (needed for feedback).
-/
structure RSYParam (n : Nat) where
  SCR : SystemCouplingRecipe n
  hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)

/--
  [textbook/definition3.47/definition/rsy_relation]
  Relational membership `(SCR, Z) ∈ RSY` for the fundamental parameterization theorem.
-/
def InRSY (n : Nat) (p : RSYParam n)
    (Z : DiscreteSystem (rsy_SZ p.SCR) (rsy_IZ p.SCR) (rsy_OZ p.SCR)) : Prop :=
  Z = rsy p.SCR p.hOut

/--
  [textbook/definition3.47/definition/ip_map]
  Input port map `IP@(SCR, Z)`: external input ports index unconnected component ports.
-/
def rsy_IP_map {n : Nat} (SCR : SystemCouplingRecipe n) (ip : UnconnInPort SCR) : UnconnInPort SCR :=
  ip

/--
  [textbook/definition3.47/definition/inip_map]
  Inverse input port map `INIP@(SCR, Z) = IP@(SCR, Z)⁻¹`.
-/
def rsy_INIP_map {n : Nat} (SCR : SystemCouplingRecipe n) (ip : UnconnInPort SCR) : UnconnInPort SCR :=
  ip

/--
  [textbook/definition3.47/definition/is_map]
  Input port structure `IS@(SCR, Z)` on resultant input ports.
-/
def rsy_IS_map {n : Nat} (SCR : SystemCouplingRecipe n) (ip : UnconnInPort SCR) : Type :=
  SCR.VSCR.PortVal ip.val.1 ip.val.2

/--
  [textbook/definition3.47/definition/op_map]
  Output port map `OP@(SCR, Z)`: external output ports index unconnected component ports.
-/
def rsy_OP_map {n : Nat} (SCR : SystemCouplingRecipe n) (op : UnconnOutPort SCR) : UnconnOutPort SCR :=
  op

/--
  [textbook/definition3.47/definition/inop_map]
  Inverse output port map `INOP@(SCR, Z) = OP@(SCR, Z)⁻¹`.
-/
def rsy_INOP_map {n : Nat} (SCR : SystemCouplingRecipe n) (op : UnconnOutPort SCR) : UnconnOutPort SCR :=
  op

/--
  [textbook/definition3.47/definition/os_map]
  Output port structure `OS@(SCR, Z)` on resultant output ports.
-/
def rsy_OS_map {n : Nat} (SCR : SystemCouplingRecipe n) (op : UnconnOutPort SCR) : Type :=
  SCR.VSCR.OutPortVal op.val.1 op.val.2

/--
  [textbook/exercise3.121/theorem/resultant_input_port_map]
  `IP@(SCR,Z) ∈ FNS(IPZ, 1TO1, ONTO, UISCR)`.
-/
theorem rsy_IP_map_inFNS1TO1Onto {n : Nat} (SCR : SystemCouplingRecipe n) :
    InFNS1TO1Onto (rsy_IP_map SCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.121/theorem/resultant_inverse_input_port_map]
  `INIP@(SCR,Z) ∈ FNS(UISCR, 1TO1, ONTO, IPZ)`.
-/
theorem rsy_INIP_map_inFNS1TO1Onto {n : Nat} (SCR : SystemCouplingRecipe n) :
    InFNS1TO1Onto (rsy_INIP_map SCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.121/theorem/resultant_input_port_structure]
  `IS@(SCR,Z) = ISZ` on resultant input ports.
-/
theorem rsy_IS_map_eq {n : Nat} (SCR : SystemCouplingRecipe n) (ip : UnconnInPort SCR) :
    rsy_IS_map SCR ip = SCR.VSCR.PortVal ip.val.1 ip.val.2 := rfl

/--
  [textbook/exercise3.121/theorem/resultant_output_port_map]
  `OP@(SCR,Z) ∈ FNS(OPZ, 1TO1, ONTO, UOSCR)`.
-/
theorem rsy_OP_map_inFNS1TO1Onto {n : Nat} (SCR : SystemCouplingRecipe n) :
    InFNS1TO1Onto (rsy_OP_map SCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.121/theorem/resultant_inverse_output_port_map]
  `INOP@(SCR,Z) ∈ FNS(UOSCR, 1TO1, ONTO, OPZ)`.
-/
theorem rsy_INOP_map_inFNS1TO1Onto {n : Nat} (SCR : SystemCouplingRecipe n) :
    InFNS1TO1Onto (rsy_INOP_map SCR) :=
  inFNS1TO1Onto_id

/--
  [textbook/exercise3.121/theorem/resultant_output_port_structure]
  `OS@(SCR,Z) = OSZ` on resultant output ports.
-/
theorem rsy_OS_map_eq {n : Nat} (SCR : SystemCouplingRecipe n) (op : UnconnOutPort SCR) :
    rsy_OS_map SCR op = SCR.VSCR.OutPortVal op.val.1 op.val.2 := rfl

/--
  [textbook/definition3.47/definition/open_loop]
  Open-loop system `Z& = CSY(VSCR)` determined by a coupling recipe.
-/
noncomputable def rsy_open_loop_system {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :
    DiscreteSystem
      ((i : Fin n) → SCR.VSCR.SZ i)
      ((ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2)
      ((op : Σ (i : Fin n), SCR.VSCR.OutPort i) → SCR.VSCR.OutPortVal op.1 op.2) :=
  csy SCR.VSCR hOut

/--
  [textbook/definition3.47/definition/closed_loop]
  Closed-loop system `Z@ = RSY(SCR)` determined by a coupling recipe.
-/
noncomputable def rsy_closed_loop_system {n : Nat} (p : RSYParam n) :
    DiscreteSystem (rsy_SZ p.SCR) (rsy_IZ p.SCR) (rsy_OZ p.SCR) :=
  rsy p.SCR p.hOut

/--
  [textbook/theorem3.62/theorem/rsy_parameterization]
  [textbook/theorem3.62/proof/dsystems]
  [textbook/theorem3.62/proof/existence]
  [textbook/theorem3.62/proof/uniqueness]
  Resultant systems `RSY` form a system parameterization.
-/
noncomputable def rsy_parameterization (n : Nat) :
    DiscreteSystemParameterization (RSYParam n)
      (fun p => rsy_SZ p.SCR)
      (fun p => rsy_IZ p.SCR)
      (fun p => rsy_OZ p.SCR) :=
  fun p => rsy p.SCR p.hOut

/--
  [textbook/theorem3.62/proof/dsystems]
  Every parameter instance lies in `RSY` (is a valid discrete system).
-/
theorem rsy_parameterization_membership (n : Nat) (p : RSYParam n) :
    InRSY n p (rsy_parameterization n p) :=
  rfl

/--
  [textbook/theorem3.62/proof/existence]
  For every coupling-recipe parameter, a resultant system exists.
-/
theorem rsy_parameterization_exists (n : Nat) (p : RSYParam n) :
    ∃ Z, InRSY n p Z :=
  ⟨rsy p.SCR p.hOut, rfl⟩

/--
  [textbook/theorem3.62/proof/uniqueness]
  The resultant is unique for a given coupling recipe.
-/
theorem rsy_parameterization_unique (n : Nat) (p : RSYParam n)
    (Z : DiscreteSystem (rsy_SZ p.SCR) (rsy_IZ p.SCR) (rsy_OZ p.SCR)) (h : InRSY n p Z) :
    Z = rsy_parameterization n p :=
  h

theorem rsy_parameter_instance (n : Nat) (p : RSYParam n) :
    rsy_parameterization n p = rsy p.SCR p.hOut :=
  rfl

theorem rsy_closed_loop_is_rsy {n : Nat} (p : RSYParam n) :
    rsy_closed_loop_system p = rsy p.SCR p.hOut :=
  rfl

theorem rsy_closed_loop_is_parameter_instance (n : Nat) (p : RSYParam n) :
    rsy_closed_loop_system p = rsy_parameterization n p :=
  rfl

theorem rsy_open_loop_is_csy {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :
    rsy_open_loop_system SCR hOut = csy SCR.VSCR hOut :=
  rfl

/-! ## Theorem 3.64: open-loop / closed-loop feedback reclosure -/

/--
  [textbook/theorem3.64/definition/open_loop_ports]
  Open-loop `Z&` port types (tagged union of component ports).
-/
def openLoopInputPort {n : Nat} (SCR : SystemCouplingRecipe n) :=
  Σ (i : Fin n), SCR.VSCR.Port i

def openLoopOutputPort {n : Nat} (SCR : SystemCouplingRecipe n) :=
  Σ (i : Fin n), SCR.VSCR.OutPort i

lemma sigmaOutPort_nonempty {n : Nat} (SCR : SystemCouplingRecipe n) :
    Nonempty (Σ (i : Fin n), SCR.VSCR.OutPort i) := by
  by_contra hne
  have hall : ∀ op, op ∈ {x | ∃ y, (x, y) ∈ SCR.CSCR} := by
    intro op
    exact absurd ⟨op⟩ hne
  exact SCR.connectivity.2.1 (Set.eq_univ_of_forall hall)

lemma sigmaPort_nonempty {n : Nat} (SCR : SystemCouplingRecipe n) :
    Nonempty (Σ (i : Fin n), SCR.VSCR.Port i) := by
  by_contra hne
  have hall : ∀ ip, ip ∈ {y | ∃ x, (x, y) ∈ SCR.CSCR} := by
    intro ip
    exact absurd ⟨ip⟩ hne
  exact SCR.connectivity.2.2.1 (Set.eq_univ_of_forall hall)

private theorem isProperDomain_empty {α β : Type} (hα : Nonempty α) :
    IsProperDomain (∅ : Set (α × β)) := by
  intro h
  obtain ⟨x⟩ := hα
  simp [Set.eq_univ_iff_forall] at h
  exact h x

private theorem isProperRange_empty {α β : Type} (hβ : Nonempty β) :
    IsProperRange (∅ : Set (α × β)) := by
  intro h
  obtain ⟨y⟩ := hβ
  simp [Set.eq_univ_iff_forall] at h
  cases (h y)

theorem empty_scr_connectivity {n : Nat} (VSCR : PortSystemVector n)
    (hOut : Nonempty (Σ (i : Fin n), VSCR.OutPort i))
    (hIn : Nonempty (Σ (i : Fin n), VSCR.Port i)) :
    IsSystemConnectivity VSCR (∅ : Set ((Σ (i : Fin n), VSCR.OutPort i) ×
      (Σ (i : Fin n), VSCR.Port i))) := by
  refine ⟨ ?_, ?_, ?_, ?_ ⟩
  · refine ⟨ ?_, ?_ ⟩
    · intro _ _ _ h; cases h
    · intro _ _ _ h; cases h
  · exact isProperDomain_empty hOut
  · exact isProperRange_empty hIn
  · intro _ _ h
    cases h

/--
  [textbook/theorem3.64/definition/conjunctive_scr]
  Conjunctive coupling recipe `(VSCR, ∅)` for the same component vector.
-/
def conjunctiveSCR {n : Nat} (SCR : SystemCouplingRecipe n) : SystemCouplingRecipe n where
  VSCR := SCR.VSCR
  CSCR := ∅
  connectivity := empty_scr_connectivity SCR.VSCR (sigmaOutPort_nonempty SCR) (sigmaPort_nonempty SCR)

theorem conjunctiveSCR_is_conjunctive {n : Nat} (SCR : SystemCouplingRecipe n) :
    IsConjunctive (conjunctiveSCR SCR) := by
  dsimp [conjunctiveSCR, IsConjunctive]

lemma mem_uiscr_conjunctive {n : Nat} (SCR : SystemCouplingRecipe n) (h : IsConjunctive SCR)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) : ip ∈ UISCR SCR := by
  rw [UISCR, Set.mem_compl_iff, CISCR, Set.mem_setOf_eq]
  rintro ⟨op, hop⟩
  rw [h] at hop
  cases hop

lemma mem_uoscr_conjunctive {n : Nat} (SCR : SystemCouplingRecipe n) (h : IsConjunctive SCR)
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) : op ∈ UOSCR SCR := by
  rw [UOSCR, Set.mem_compl_iff, COSCR, Set.mem_setOf_eq]
  rintro ⟨ip, hop⟩
  rw [h] at hop
  cases hop

/--
  [textbook/exercise3.123/definition/unconn_input_equiv]
  On conjunctive recipes, unconnected input ports are the full tagged union.
-/
noncomputable def unconnInPortEquiv {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) : UnconnInPort SCR ≃ Σ (i : Fin n), SCR.VSCR.Port i where
  toFun ip := ip.val
  invFun ip := ⟨ip, mem_uiscr_conjunctive SCR h ip⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
  [textbook/exercise3.123/definition/unconn_output_equiv]
  On conjunctive recipes, unconnected output ports are the full tagged union.
-/
noncomputable def unconnOutPortEquiv {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) : UnconnOutPort SCR ≃ Σ (i : Fin n), SCR.VSCR.OutPort i where
  toFun op := op.val
  invFun op := ⟨op, mem_uoscr_conjunctive SCR h op⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma sigmaPort_nonempty_vscr {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (h : Nonempty (VSCR.Port i)) : Nonempty (Σ (j : Fin n), VSCR.Port j) :=
  ⟨⟨i, Classical.choice h⟩⟩

lemma sigmaOutPort_nonempty_vscr {n : Nat} (VSCR : PortSystemVector n) (i : Fin n)
    (h : Nonempty (VSCR.OutPort i)) : Nonempty (Σ (j : Fin n), VSCR.OutPort j) :=
  ⟨⟨i, Classical.choice h⟩⟩

/--
  [textbook/exercise3.122/definition/singular_scr]
  Singular coupling recipe `(V, ∅)` for a one-component connectable vector.
-/
def singularSCR (V : PortSystemVector 1)
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i)) : SystemCouplingRecipe 1 where
  VSCR := V
  CSCR := ∅
  connectivity := empty_scr_connectivity V hOutNE hInNE

theorem singularSCR_is_singular (V : PortSystemVector 1)
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i)) :
    IsSingular (singularSCR V hOutNE hInNE) :=
  ⟨rfl, rfl⟩

theorem singular_scr_inRSY (V : PortSystemVector 1)
    (hOut : ∀ i, AlwaysOutputs (V.Z i))
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i)) :
    InRSY 1 ⟨singularSCR V hOutNE hInNE, hOut⟩ (rsy (singularSCR V hOutNE hInNE) hOut) :=
  rfl

/--
  [textbook/exercise3.122/definition/port_vector_of_system]
  Embed a port-encoded discrete system as a one-component connectable vector.
-/
def portVectorOfSystem {SZ Port OutPort : Type}
    (PortVal : Port → Type) (OutPortVal : OutPort → Type)
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((op : OutPort) → OutPortVal op)) :
    PortSystemVector 1 where
  SZ := fun _ => SZ
  Port := fun _ => Port
  PortVal := fun _ p => PortVal p
  OutPort := fun _ => OutPort
  OutPortVal := fun _ op => OutPortVal op
  Z := fun _ => Z
  distinct := fun i j hne => absurd (Trajectory.fin_one_eq i j) hne

noncomputable def finArrowOneEquiv (A : Type) : (Fin 1 → A) ≃ A where
  toFun f := f 0
  invFun a := fun _ => a
  left_inv f := funext (fun i => by have hi := Trajectory.fin_one_eq i 0; subst hi; rfl)
  right_inv _ := rfl

noncomputable def singularStateEquiv {SZ Port OutPort : Type}
    (PortVal : Port → Type) (OutPortVal : OutPort → Type)
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((op : OutPort) → OutPortVal op))
    (hOutNE : Nonempty (Σ (i : Fin 1), (portVectorOfSystem PortVal OutPortVal Z).OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), (portVectorOfSystem PortVal OutPortVal Z).Port i)) :
    SZ ≃ rsy_SZ (singularSCR (portVectorOfSystem PortVal OutPortVal Z) hOutNE hInNE) :=
  (finArrowOneEquiv SZ).symm

theorem singularSCR_is_conjunctive (V : PortSystemVector 1)
    (hOutNE : Nonempty (Σ (i : Fin 1), V.OutPort i))
    (hInNE : Nonempty (Σ (i : Fin 1), V.Port i)) :
    IsConjunctive (singularSCR V hOutNE hInNE) :=
  rfl

noncomputable def rsyIzFromPortInput {n : Nat} (SCR : SystemCouplingRecipe n)
    (_h : IsConjunctive SCR)
    (g : (i : Fin n) → (p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p) :
    rsy_IZ SCR :=
  fun ip => g ip.val.1 ip.val.2

noncomputable def portInputToRsyTrajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR)
    (f : ITZW ((ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2)) :
    ITZW (rsy_IZ SCR) :=
  fun τ => (f τ).map (fun full => rsyIzFromPortInput SCR h (fun i p => full ⟨i, p⟩))

noncomputable def singularPortTrajectory {Port : Type} (PortVal : Port → Type)
    (f : ITZW ((p : Port) → PortVal p)) :
    ITZW ((ip : Σ (_ : Fin 1), Port) → PortVal ip.2) :=
  fun τ => (f τ).map (fun g ip => g ip.2)

noncomputable def singularRsyInputTrajectory (SCR : SystemCouplingRecipe 1)
    (h : IsConjunctive SCR)
    (f : ITZW ((p : SCR.VSCR.Port 0) → SCR.VSCR.PortVal 0 p)) :
    ITZW (rsy_IZ SCR) :=
  portInputToRsyTrajectory SCR h (fun τ => (f τ).map (fun g ip =>
    match ip with
    | ⟨0, p⟩ => g p))

noncomputable def singularRsyIzFromPortInput (SCR : SystemCouplingRecipe 1) (_h : IsConjunctive SCR)
    (g : (p : SCR.VSCR.Port 0) → SCR.VSCR.PortVal 0 p) : rsy_IZ SCR :=
  fun ip => match ip.val with | ⟨0, p⟩ => g p

noncomputable def rsyExtInOfCsy {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (extIn : rsy_IZ SCR) :
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2 :=
  fun ip => extIn ⟨ip, mem_uiscr_conjunctive SCR h ip⟩

noncomputable def csyExtInFromRsy {n : Nat} (SCR : SystemCouplingRecipe n)
    (_h : IsConjunctive SCR)
    (fullIn : (ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2) :
    rsy_IZ SCR :=
  fun ip => fullIn ip.val

theorem rsy_conjunctive_scr_NZ_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (x : rsy_SZ SCR) (extIn : rsy_IZ SCR) (i : Fin n) :
    rsy_NZ SCR hOut x (some extIn) i =
      (csy SCR.VSCR hOut).NZ x (some (rsyExtInOfCsy SCR h extIn)) i := by
  simp only [csy, rsy_NZ]
  congr 1
  apply congr_arg some
  funext port
  dsimp [rsy_component_input_fun, rsyExtInOfCsy]
  have hU := mem_uiscr_conjunctive SCR h ⟨i, port⟩
  simp [hU]

theorem rsy_conjunctive_scr_RZ_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    (_h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (x : rsy_SZ SCR) (op : Σ (i : Fin n), SCR.VSCR.OutPort i) :
    rsyOutAt SCR hOut x op = csyOut SCR.VSCR hOut x op := by
  dsimp [rsyOutAt, csyOut]

lemma singular_scr_NZ_eq {SCR : SystemCouplingRecipe 1} (h : IsConjunctive SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) (x : rsy_SZ SCR)
    (g : (p : SCR.VSCR.Port 0) → SCR.VSCR.PortVal 0 p) :
    rsy_NZ SCR hOut x (some (singularRsyIzFromPortInput SCR h g)) 0 =
      (csy SCR.VSCR hOut).NZ x (some (fun ip => match ip with | ⟨0, p⟩ => g p)) 0 :=
  rsy_conjunctive_scr_NZ_eq SCR h hOut x (singularRsyIzFromPortInput SCR h g) 0

lemma singular_scr_RZ_eq {SCR : SystemCouplingRecipe 1} (h : IsConjunctive SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) (x : rsy_SZ SCR) (p : SCR.VSCR.OutPort 0) :
    rsyOutAt SCR hOut x ⟨0, p⟩ = csyOut SCR.VSCR hOut x ⟨0, p⟩ :=
  rsy_conjunctive_scr_RZ_eq SCR h hOut x ⟨0, p⟩

/--
  [textbook/exercise3.123/theorem/conjunctive_rsy_eq_csy]
  On conjunctive recipes, `RSY(SCR)` and `CSY(VSCR)` agree on next-state and readout.
-/
theorem conjunctive_rsy_eq_csy {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :
    InRSY n ⟨SCR, hOut⟩ (rsy SCR hOut) ∧
      (∀ (x : rsy_SZ SCR) (extIn : rsy_IZ SCR) (i : Fin n),
        rsy_NZ SCR hOut x (some extIn) i =
          (csy SCR.VSCR hOut).NZ x (some (rsyExtInOfCsy SCR h extIn)) i) ∧
      (∀ (x : rsy_SZ SCR) (op : Σ (i : Fin n), SCR.VSCR.OutPort i),
        rsyOutAt SCR hOut x op = csyOut SCR.VSCR hOut x op) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x extIn i
    exact rsy_conjunctive_scr_NZ_eq SCR h hOut x extIn i
  · intro x op
    exact rsy_conjunctive_scr_RZ_eq SCR h hOut x op

/--
  [textbook/exercise3.122/theorem/every_system_is_resultant]
  Every port-encoded discrete system is the resultant of its singular recipe `(Z, ∅)`.
-/
theorem every_port_system_is_resultant {SZ Port OutPort : Type}
    (PortVal : Port → Type) (OutPortVal : OutPort → Type)
    (Z : DiscreteSystem SZ ((p : Port) → PortVal p) ((op : OutPort) → OutPortVal op))
    (hOut : AlwaysOutputs Z)
    (hPort : Nonempty Port) (hOutPort : Nonempty OutPort) :
    let V := portVectorOfSystem PortVal OutPortVal Z
    let hOutNE := sigmaOutPort_nonempty_vscr V 0 ⟨Classical.choice hOutPort⟩
    let hInNE := sigmaPort_nonempty_vscr V 0 ⟨Classical.choice hPort⟩
    let SCR := singularSCR V hOutNE hInNE
    let hConj := singularSCR_is_conjunctive V hOutNE hInNE
    IsSingular SCR ∧
      InRSY 1 ⟨SCR, fun _ => hOut⟩ (rsy SCR (fun _ => hOut)) ∧
      (∀ (x : SZ) (g : (p : Port) → PortVal p),
        rsy_NZ SCR (fun _ => hOut) (fun _ => x)
          (some (singularRsyIzFromPortInput SCR hConj g)) 0 =
          Z.NZ x (some g)) ∧
      (∀ (x : SZ) (p : OutPort),
        rsyOutAt SCR (fun _ => hOut) (fun _ => x) ⟨0, p⟩ =
          csyOut V (fun _ => hOut) (fun _ => x) ⟨0, p⟩) := by
  let V := portVectorOfSystem PortVal OutPortVal Z
  let hOutNE := sigmaOutPort_nonempty_vscr V 0 ⟨Classical.choice hOutPort⟩
  let hInNE := sigmaPort_nonempty_vscr V 0 ⟨Classical.choice hPort⟩
  let SCR := singularSCR V hOutNE hInNE
  let hConj := singularSCR_is_conjunctive V hOutNE hInNE
  refine ⟨singularSCR_is_singular V hOutNE hInNE, ?_, ?_, ?_⟩
  · rfl
  · intro x g
    simpa using singular_scr_NZ_eq hConj (fun _ => hOut) (fun _ => x) g
  · intro x p
    simpa using singular_scr_RZ_eq hConj (fun _ => hOut) (fun _ => x) p

theorem csy_alwaysOutputs {n : Nat} (VSCR : PortSystemVector n)
    (hOut : ∀ i, AlwaysOutputs (VSCR.Z i)) : AlwaysOutputs (csy VSCR hOut) := by
  intro x
  dsimp [csy]
  exact ⟨fun op => csyOut VSCR hOut x op, rfl⟩

/--
  [textbook/theorem3.64/definition/open_loop_port_vector]
  `VSCR$ = Z&`: singleton connectable vector whose component is the open-loop system.
-/
noncomputable def openLoopPortVector {n : Nat} (p : RSYParam n) : PortSystemVector 1 where
  SZ := fun _ => (i : Fin n) → p.SCR.VSCR.SZ i
  Port := fun _ => openLoopInputPort p.SCR
  PortVal := fun _ ip => p.SCR.VSCR.PortVal ip.1 ip.2
  OutPort := fun _ => openLoopOutputPort p.SCR
  OutPortVal := fun _ op => p.SCR.VSCR.OutPortVal op.1 op.2
  Z := fun _ => rsy_open_loop_system p.SCR p.hOut
  distinct := fun i j hne => absurd (Trajectory.fin_one_eq i j) hne

/--
  [textbook/theorem3.64/definition/feedback_cscr]
  `CSCR$`: relabel original connections onto open-loop ports via `IP&` / `OP&`.
-/
def feedbackSCR_CSCR {n : Nat} (SCR : SystemCouplingRecipe n) :
    Set ((Σ (_ : Fin 1), openLoopOutputPort SCR) × (Σ (_ : Fin 1), openLoopInputPort SCR)) :=
  { p | ∃ op ip, (op, ip) ∈ SCR.CSCR ∧ p = (⟨0, op⟩, ⟨0, ip⟩) }

theorem feedbackSCR_portCompatibility {n : Nat} (p : RSYParam n) :
    PortCompatibility (openLoopPortVector p) (feedbackSCR_CSCR p.SCR) := by
  intro op ip h
  rcases Set.mem_setOf.mp h with ⟨scrOp, scrIp, hpair, heq⟩
  dsimp [PortCompatibility, openLoopPortVector, openLoopInputPort, openLoopOutputPort]
  have hop : op.2 = scrOp := congr_arg Sigma.snd (congr_arg Prod.fst heq)
  have hip : ip.2 = scrIp := congr_arg Sigma.snd (congr_arg Prod.snd heq)
  rw [hop, hip]
  exact p.SCR.connectivity.2.2.2 scrOp scrIp hpair

theorem feedbackSCR_connectivity {n : Nat} (p : RSYParam n) :
    IsSystemConnectivity (openLoopPortVector p) (feedbackSCR_CSCR p.SCR) := by
  refine ⟨ ⟨ ?_, ?_ ⟩, ⟨ ?_, ⟨ ?_, ?_ ⟩ ⟩⟩
  · intro x y1 y2 h1 h2
    rcases Set.mem_setOf.mp h1 with ⟨op1, ip1, hpair1, heq1⟩
    rcases Set.mem_setOf.mp h2 with ⟨op2, ip2, hpair2, heq2⟩
    have hop : op1 = op2 := by
      have h1x := (congr_arg Prod.fst heq1).symm
      have h2x := congr_arg Prod.fst heq2
      exact congr_arg Sigma.snd (h1x.trans h2x)
    have hip : ip1 = ip2 := p.SCR.connectivity.1.1 op1 ip1 ip2 hpair1 (hop ▸ hpair2)
    have hy1 : y1 = ⟨0, ip1⟩ := congr_arg Prod.snd heq1
    have hy2 : y2 = ⟨0, ip2⟩ := congr_arg Prod.snd heq2
    rw [hy1, hy2]
    exact congrArg (Sigma.mk 0) hip
  · intro x1 x2 y h1 h2
    rcases Set.mem_setOf.mp h1 with ⟨op1, ip1, hpair1, heq1⟩
    rcases Set.mem_setOf.mp h2 with ⟨op2, ip2, hpair2, heq2⟩
    have hip : ip1 = ip2 := by
      have h1y := (congr_arg Prod.snd heq1).symm
      have h2y := congr_arg Prod.snd heq2
      exact congr_arg Sigma.snd (h1y.trans h2y)
    have hop : op1 = op2 := p.SCR.connectivity.1.2 op1 op2 ip1 hpair1 (hip ▸ hpair2)
    have hx1 : x1 = ⟨0, op1⟩ := congr_arg Prod.fst heq1
    have hx2 : x2 = ⟨0, op2⟩ := congr_arg Prod.fst heq2
    rw [hx1, hx2]
    exact congrArg (Sigma.mk 0) hop
  · intro heq
    obtain ⟨op, hopdom⟩ := show ∃ op, op ∉ {x | ∃ y, (x, y) ∈ p.SCR.CSCR} from by
      by_contra hall
      push Not at hall
      exact p.SCR.connectivity.2.1 (Set.eq_univ_of_forall hall)
    have hnot : (⟨0, op⟩ : Σ (_ : Fin 1), openLoopOutputPort p.SCR) ∉
        {x | ∃ y, (x, y) ∈ feedbackSCR_CSCR p.SCR} := by
      intro hmem
      obtain ⟨ip, hpair⟩ := hmem
      rcases Set.mem_setOf.mp hpair with ⟨scrOp, scrIp, hp, heq'⟩
      have hop' : op = scrOp := congr_arg Sigma.snd (congr_arg Prod.fst heq')
      subst hop'
      exact hopdom (Set.mem_setOf.mpr ⟨scrIp, hp⟩)
    exact hnot (heq ▸ Set.mem_univ (⟨0, op⟩ : Σ (_ : Fin 1), openLoopOutputPort p.SCR))
  · intro heq
    obtain ⟨ip, hipdom⟩ := show ∃ ip, ip ∉ {y | ∃ x, (x, y) ∈ p.SCR.CSCR} from by
      by_contra hall
      push Not at hall
      exact p.SCR.connectivity.2.2.1 (Set.eq_univ_of_forall hall)
    have hnot : (⟨0, ip⟩ : Σ (_ : Fin 1), openLoopInputPort p.SCR) ∉
        {y | ∃ x, (x, y) ∈ feedbackSCR_CSCR p.SCR} := by
      intro hmem
      obtain ⟨op, hpair⟩ := hmem
      rcases Set.mem_setOf.mp hpair with ⟨scrOp, scrIp, hp, heq'⟩
      have hip' : ip = scrIp := congr_arg Sigma.snd (congr_arg Prod.snd heq')
      subst hip'
      exact hipdom (Set.mem_setOf.mpr ⟨scrOp, hp⟩)
    exact hnot (heq ▸ Set.mem_univ (⟨0, ip⟩ : Σ (_ : Fin 1), openLoopInputPort p.SCR))
  · exact feedbackSCR_portCompatibility p

/--
  [textbook/theorem3.64/definition/feedback_scr]
  Pure-feedback coupling recipe `SCR$ = (VSCR$, CSCR$)`.
-/
noncomputable def feedbackSCR {n : Nat} (p : RSYParam n) : SystemCouplingRecipe 1 where
  VSCR := openLoopPortVector p
  CSCR := feedbackSCR_CSCR p.SCR
  connectivity := feedbackSCR_connectivity p

lemma mem_feedbackSCR_CSCR_iff {n : Nat} (SCR : SystemCouplingRecipe n)
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) (ip : Σ (i : Fin n), SCR.VSCR.Port i) :
    (⟨0, op⟩, ⟨0, ip⟩) ∈ feedbackSCR_CSCR SCR ↔ (op, ip) ∈ SCR.CSCR := by
  constructor
  · intro h
    rcases Set.mem_setOf.mp h with ⟨scrOp, scrIp, hp, heq⟩
    have hop : op = scrOp := congr_arg Sigma.snd (congr_arg Prod.fst heq)
    have hip : ip = scrIp := congr_arg Sigma.snd (congr_arg Prod.snd heq)
    simpa [hop, hip] using hp
  · intro hp
    exact Set.mem_setOf.mpr ⟨op, ip, hp, rfl⟩

lemma mem_ciscr_feedbackSCR_iff {n : Nat} (p : RSYParam n) (ip : openLoopInputPort p.SCR) :
    (⟨0, ip⟩ : Σ (_ : Fin 1), openLoopInputPort p.SCR) ∈ CISCR (feedbackSCR p) ↔
      ip ∈ CISCR p.SCR := by
  dsimp [CISCR, feedbackSCR, feedbackSCR_CSCR, Set.mem_setOf_eq]
  constructor
  · rintro ⟨op, hmem⟩
    rcases Set.mem_setOf.mp hmem with ⟨scrOp, scrIp, hp, heq⟩
    have hip : ip = scrIp := congr_arg Sigma.snd (congr_arg Prod.snd heq)
    subst hip
    exact ⟨scrOp, hp⟩
  · rintro ⟨scrOp, hp⟩
    exact ⟨⟨0, scrOp⟩, Set.mem_setOf.mpr ⟨scrOp, ip, hp, rfl⟩⟩

lemma mem_coscr_feedbackSCR_iff {n : Nat} (p : RSYParam n) (op : openLoopOutputPort p.SCR) :
    (⟨0, op⟩ : Σ (_ : Fin 1), openLoopOutputPort p.SCR) ∈ COSCR (feedbackSCR p) ↔
      op ∈ COSCR p.SCR := by
  dsimp [COSCR, feedbackSCR, feedbackSCR_CSCR, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ip, hmem⟩
    rcases Set.mem_setOf.mp hmem with ⟨scrOp, scrIp, hp, heq⟩
    have hop : op = scrOp := congr_arg Sigma.snd (congr_arg Prod.fst heq)
    subst hop
    exact ⟨scrIp, hp⟩
  · rintro ⟨scrIp, hp⟩
    exact ⟨⟨0, scrIp⟩, Set.mem_setOf.mpr ⟨op, scrIp, hp, rfl⟩⟩

lemma mem_uiscr_feedbackSCR {n : Nat} (p : RSYParam n) (ip : openLoopInputPort p.SCR) :
    (⟨0, ip⟩ : Σ (_ : Fin 1), openLoopInputPort p.SCR) ∈ UISCR (feedbackSCR p) ↔
      ip ∈ UISCR p.SCR :=
  Iff.not (mem_ciscr_feedbackSCR_iff p ip)

lemma mem_uoscr_feedbackSCR {n : Nat} (p : RSYParam n) (op : openLoopOutputPort p.SCR) :
    (⟨0, op⟩ : Σ (_ : Fin 1), openLoopOutputPort p.SCR) ∈ UOSCR (feedbackSCR p) ↔
      op ∈ UOSCR p.SCR :=
  Iff.not (mem_coscr_feedbackSCR_iff p op)

/--
  [textbook/theorem3.64/definition/feedback_rsy_param]
  Parameter bundle for `Z@$ = RSY(SCR$)`.
-/
noncomputable def feedbackRSYParam {n : Nat} (p : RSYParam n) : RSYParam 1 where
  SCR := feedbackSCR p
  hOut := fun i =>
    Trajectory.fin_one_eq i 0 ▸ csy_alwaysOutputs p.SCR.VSCR p.hOut

theorem feedbackSCR_CSCR_nonempty {n : Nat} (p : RSYParam n) (h : ¬ IsConjunctive p.SCR) :
    feedbackSCR_CSCR p.SCR ≠ ∅ := by
  dsimp [IsConjunctive] at h
  intro hempty
  rcases Set.nonempty_iff_ne_empty.mpr h with ⟨pair, hp⟩
  rcases pair with ⟨op, ip⟩
  have hnem : (feedbackSCR_CSCR p.SCR).Nonempty :=
    ⟨(⟨0, op⟩, ⟨0, ip⟩), (mem_feedbackSCR_CSCR_iff p.SCR op ip).mpr hp⟩
  exact (Set.nonempty_iff_ne_empty.mp hnem) hempty

/--
  [textbook/theorem3.64/theorem/feedback_scr_pure]
  `SCR$` is a pure feedback coupling recipe.
-/
theorem feedbackSCR_is_pure_feedback {n : Nat} (p : RSYParam n) (h : ¬ IsConjunctive p.SCR) :
    IsPureFeedback (feedbackSCR p) :=
  ⟨rfl, feedbackSCR_CSCR_nonempty p h⟩

/--
  Embed product state into the singleton-vector state for `SCR$`.
-/
def feedbackStateEmb {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR) : rsy_SZ (feedbackSCR p) :=
  fun _ => x

/--
  Project singleton-vector state to the product state of the original recipe.
-/
def feedbackStateVal {n : Nat} (p : RSYParam n) (x : rsy_SZ (feedbackSCR p)) : rsy_SZ p.SCR :=
  x 0

noncomputable def rsyExtIn_to_openLoopInput {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (extIn : rsy_IZ SCR) :
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2 :=
  fun ip => extIn ⟨ip, mem_uiscr_conjunctive SCR h ip⟩

noncomputable def rsyOut_to_openLoopOutput {n : Nat} (SCR : SystemCouplingRecipe n)
    (h : IsConjunctive SCR) (out : rsy_OZ SCR) :
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) → SCR.VSCR.OutPortVal op.1 op.2 :=
  fun op => out ⟨op, mem_uoscr_conjunctive SCR h op⟩

noncomputable def rsyIZ_to_feedbackIZ {n : Nat} (p : RSYParam n) (extIn : rsy_IZ p.SCR) :
    rsy_IZ (feedbackSCR p) :=
  fun ip =>
    extIn ⟨ip.val.2, by
      rcases ip with ⟨val, prop⟩
      rcases val with ⟨i, port⟩
      have hi : i = 0 := Trajectory.fin_one_eq i 0
      have hfb0 : ⟨0, port⟩ ∈ UISCR (feedbackSCR p) := hi ▸ prop
      exact (mem_uiscr_feedbackSCR p port).mp hfb0⟩

noncomputable def conjunctiveRsyExtIn {n : Nat} (SCR : SystemCouplingRecipe n)
    (extIn : rsy_IZ (conjunctiveSCR SCR)) :
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) → SCR.VSCR.PortVal ip.1 ip.2 :=
  fun ip =>
    extIn ⟨ip, mem_uiscr_conjunctive (conjunctiveSCR SCR) (conjunctiveSCR_is_conjunctive SCR) ip⟩

noncomputable def conjunctiveRsyOut {n : Nat} (SCR : SystemCouplingRecipe n)
    (out : rsy_OZ (conjunctiveSCR SCR)) :
    (op : Σ (i : Fin n), SCR.VSCR.OutPort i) → SCR.VSCR.OutPortVal op.1 op.2 :=
  fun op =>
    out ⟨op, mem_uoscr_conjunctive (conjunctiveSCR SCR) (conjunctiveSCR_is_conjunctive SCR) op⟩

theorem rsy_conjunctive_NZ_eq {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (extIn : rsy_IZ (conjunctiveSCR p.SCR)) (i : Fin n) :
    (rsy (conjunctiveSCR p.SCR) p.hOut).NZ x (some extIn) i =
      (csy p.SCR.VSCR p.hOut).NZ x (some (conjunctiveRsyExtIn p.SCR extIn)) i := by
  simp only [conjunctiveSCR, csy]
  congr 1
  apply congr_arg some
  funext port
  have hU := mem_uiscr_conjunctive (conjunctiveSCR p.SCR) (conjunctiveSCR_is_conjunctive p.SCR) ⟨i, port⟩
  dsimp [rsy_component_input_fun, conjunctiveSCR, conjunctiveRsyExtIn]
  simp [UISCR, CISCR]
  rfl

theorem rsy_conjunctive_RZ_eq {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (op : Σ (i : Fin n), p.SCR.VSCR.OutPort i) :
    rsyOutAt (conjunctiveSCR p.SCR) p.hOut x op = csyOut p.SCR.VSCR p.hOut x op := by
  dsimp [rsyOutAt, csyOut, conjunctiveSCR]

theorem rsy_conjunctive_readout_eq {n : Nat} (p : RSYParam n) (_ : rsy_SZ p.SCR)
    (out : rsy_OZ (conjunctiveSCR p.SCR)) (op : Σ (i : Fin n), p.SCR.VSCR.OutPort i) :
    out ⟨op, mem_uoscr_conjunctive (conjunctiveSCR p.SCR)
      (conjunctiveSCR_is_conjunctive p.SCR) op⟩ = conjunctiveRsyOut p.SCR out op := rfl

/--
  [textbook/theorem3.64/theorem/open_loop_conjunctive_rsy]
  `Z&` is the resultant of the conjunctive recipe `(VSCR, ∅)`.
-/
theorem open_loop_is_conjunctive_rsy (p : RSYParam n) :
    InRSY n ⟨conjunctiveSCR p.SCR, p.hOut⟩ (rsy (conjunctiveSCR p.SCR) p.hOut) :=
  rfl

theorem open_loop_eq_conjunctive_rsy_NZ (p : RSYParam n) (x : rsy_SZ p.SCR)
    (extIn : rsy_IZ (conjunctiveSCR p.SCR)) (i : Fin n) :
    (rsy (conjunctiveSCR p.SCR) p.hOut).NZ x (some extIn) i =
      (rsy_open_loop_system p.SCR p.hOut).NZ x (some (conjunctiveRsyExtIn p.SCR extIn)) i :=
  rsy_conjunctive_NZ_eq p x extIn i

theorem open_loop_eq_conjunctive_rsy_readout (p : RSYParam n) (x : rsy_SZ p.SCR)
    (op : Σ (i : Fin n), p.SCR.VSCR.OutPort i) :
    rsyOutAt (conjunctiveSCR p.SCR) p.hOut x op = csyOut p.SCR.VSCR p.hOut x op :=
  rsy_conjunctive_RZ_eq p x op

lemma feedbackSCR_OutPortVal_eq {n : Nat} (p : RSYParam n)
    (op : Σ (i : Fin n), p.SCR.VSCR.OutPort i) :
    (feedbackSCR p).VSCR.OutPortVal 0 op = p.SCR.VSCR.OutPortVal op.1 op.2 := rfl

lemma rsyOutAt_op_transport {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) (x : rsy_SZ SCR)
    {op₁ op₂ : Σ (i : Fin n), SCR.VSCR.OutPort i} (h : op₁ = op₂) :
    h ▸ rsyOutAt SCR hOut x op₁ = rsyOutAt SCR hOut x op₂ := by
  cases op₁
  cases op₂
  cases h
  rfl

lemma rsyOutAt_feedback_op_transport {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    {op₁ op₂ : Σ (i : Fin 1), (openLoopPortVector p).OutPort i} (h : op₁ = op₂) :
    h ▸ rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x) op₁ =
      rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x) op₂ := by
  cases op₁
  cases op₂
  cases h
  rfl

noncomputable def scrRsyOutAtFeedback {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (op_scr : Σ (j : Fin n), p.SCR.VSCR.OutPort j) :
    p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2 :=
  rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x) ⟨0, op_scr⟩

noncomputable def scrPortValFromOutReadout {n : Nat} (p : RSYParam n) (i : Fin n)
    (port : p.SCR.VSCR.Port i) (op_scr : Σ (j : Fin n), p.SCR.VSCR.OutPort j)
    (hcomp_scr : p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2 = p.SCR.VSCR.PortVal i port)
    (out : p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2) : p.SCR.VSCR.PortVal i port :=
  hcomp_scr ▸ out

noncomputable def scrPortValFromFeedbackReadout {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (i : Fin n) (port : p.SCR.VSCR.Port i) (op_scr : Σ (j : Fin n), p.SCR.VSCR.OutPort j)
    (hcomp_scr : p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2 = p.SCR.VSCR.PortVal i port) :
    p.SCR.VSCR.PortVal i port :=
  scrPortValFromOutReadout p i port op_scr hcomp_scr (scrRsyOutAtFeedback p x op_scr)

noncomputable def scrPortValFromFeedbackCiscrInput {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (i : Fin n) (port : p.SCR.VSCR.Port i) (op_scr : Σ (j : Fin n), p.SCR.VSCR.OutPort j)
    (hcomp_scr : p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2 = p.SCR.VSCR.PortVal i port) :
    p.SCR.VSCR.PortVal i port :=
  scrPortValFromFeedbackReadout p x i port op_scr hcomp_scr

lemma rsy_feedback_connected_portVal_eq {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (i : Fin n) (port : p.SCR.VSCR.Port i) (op_scr : Σ (j : Fin n), p.SCR.VSCR.OutPort j)
    (hcomp_scr : p.SCR.VSCR.OutPortVal op_scr.1 op_scr.2 = p.SCR.VSCR.PortVal i port)
    (hout : rsyOutAt p.SCR p.hOut x op_scr = scrRsyOutAtFeedback p x op_scr) :
    scrPortValFromOutReadout p i port op_scr hcomp_scr (rsyOutAt p.SCR p.hOut x op_scr) =
      scrPortValFromFeedbackCiscrInput p x i port op_scr hcomp_scr := by
  dsimp [scrPortValFromOutReadout, scrPortValFromFeedbackCiscrInput, scrPortValFromFeedbackReadout,
    scrRsyOutAtFeedback]
  rw [hout]
  rfl

theorem rsy_feedback_NZ_eq {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (po : Option (rsy_IZ p.SCR)) (i : Fin n) :
    (rsy p.SCR p.hOut).NZ x po i =
      (rsy (feedbackSCR p) (feedbackRSYParam p).hOut).NZ (feedbackStateEmb p x)
        (po.map (rsyIZ_to_feedbackIZ p)) 0 i := by
  cases po with
  | none =>
    rfl
  | some extIn =>
    simp only [Option.map_some]
    congr 1
    apply congr_arg some
    funext port
    dsimp only [rsyIZ_to_feedbackIZ, feedbackSCR]
    by_cases hU : ⟨i, port⟩ ∈ UISCR p.SCR
    · have hU_fb := (mem_uiscr_feedbackSCR p ⟨i, port⟩).mpr hU
      rw [rsy_component_input_uiscr p.SCR p.hOut i extIn x port hU]
      dsimp [rsy_component_input_fun, rsyIZ_to_feedbackIZ, feedbackSCR, openLoopInputPort]
      split_ifs with hl
      · rfl
      · exact absurd hU_fb hl
    · have hC : ⟨i, port⟩ ∈ CISCR p.SCR := by simpa [UISCR, Set.mem_compl_iff] using hU
      have hC_fb := (mem_ciscr_feedbackSCR_iff p ⟨i, port⟩).mpr hC
      have hnot_fb : ⟨0, ⟨i, port⟩⟩ ∉ UISCR (feedbackSCR p) := fun hmem =>
        hU ((mem_uiscr_feedbackSCR p ⟨i, port⟩).mp hmem)
      rw [rsy_component_input_ciscr p.SCR p.hOut i extIn x port hC]
      dsimp [rsy_component_input_fun, rsyIZ_to_feedbackIZ, feedbackSCR, openLoopInputPort]
      split_ifs with h
      · exact absurd h hnot_fb
      let op_scr := connectedOutput p.SCR ⟨i, port⟩ hC
      let op_fb := connectedOutput (feedbackSCR p) ⟨0, ⟨i, port⟩⟩ hC_fb
      have hop_scr := connectedOutput_spec p.SCR ⟨i, port⟩ hC
      have hop_fb := connectedOutput_spec (feedbackSCR p) ⟨0, ⟨i, port⟩⟩ hC_fb
      have hcomp_scr := p.SCR.connectivity.2.2.2 op_scr ⟨i, port⟩ hop_scr
      have hcomp_fb := (feedbackSCR p).connectivity.2.2.2 op_fb ⟨0, ⟨i, port⟩⟩ hop_fb
      have hop_eq : op_fb = ⟨0, op_scr⟩ :=
        (feedbackSCR p).connectivity.1.2 op_fb ⟨0, op_scr⟩ ⟨0, ⟨i, port⟩⟩ hop_fb
          ((mem_feedbackSCR_CSCR_iff p.SCR op_scr ⟨i, port⟩).mpr hop_scr)
      have hop_fb_at : (⟨0, op_scr⟩, ⟨0, ⟨i, port⟩⟩) ∈ (feedbackSCR p).CSCR := hop_eq ▸ hop_fb
      have hcomp_fb_at :=
        (feedbackSCR p).connectivity.2.2.2 ⟨0, op_scr⟩ ⟨0, ⟨i, port⟩⟩ hop_fb_at
      have hchoose := Trajectory.choose_alwaysOutputs ((openLoopPortVector p).Z 0)
        ((feedbackRSYParam p).hOut 0) ((feedbackStateEmb p x) 0) rfl
      have hout : rsyOutAt p.SCR p.hOut x op_scr = scrRsyOutAtFeedback p x op_scr := by
        dsimp [rsyOutAt, scrRsyOutAtFeedback, csyOut, openLoopPortVector, feedbackStateEmb, feedbackSCR]
        exact Eq.symm ((congrArg (fun f => f op_scr) hchoose).trans rfl)
      have step_scr_conn :
          hcomp_scr ▸ rsyOutAt p.SCR p.hOut x (connectedOutput p.SCR ⟨i, port⟩ hC) =
            hcomp_scr ▸ rsyOutAt p.SCR p.hOut x op_scr :=
        congrArg (fun v => hcomp_scr ▸ v) (rsyOutAt_op_transport p.SCR p.hOut x (by rfl :
          connectedOutput p.SCR ⟨i, port⟩ hC = op_scr))
      have step_scr_port :
          hcomp_scr ▸ rsyOutAt p.SCR p.hOut x op_scr =
            scrPortValFromFeedbackCiscrInput p x i port op_scr hcomp_scr :=
        Eq.symm (by simpa [scrPortValFromOutReadout] using
          (rsy_feedback_connected_portVal_eq p x i port op_scr hcomp_scr hout).symm)
      have step_fb_port :
          scrPortValFromFeedbackCiscrInput p x i port op_scr hcomp_scr =
            hcomp_fb_at ▸ rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x)
              ⟨0, op_scr⟩ := by
        simp [scrPortValFromFeedbackCiscrInput, scrPortValFromFeedbackReadout, scrRsyOutAtFeedback,
          scrPortValFromOutReadout, openLoopPortVector, feedbackSCR, rsyOutAt, feedbackStateEmb, csyOut]
      have step_fb_conn :
          hcomp_fb_at ▸ rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x)
              ⟨0, op_scr⟩ =
            hcomp_fb ▸ rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut (feedbackStateEmb p x) op_fb := by
        have hreadout :=
          rsyOutAt_feedback_op_transport p x (op₁ := ⟨0, op_scr⟩) (op₂ := op_fb) hop_eq.symm
        apply Eq.symm
        trans hcomp_fb ▸ (hop_eq.symm ▸ rsyOutAt (feedbackSCR p) (feedbackRSYParam p).hOut
            (feedbackStateEmb p x) ⟨0, op_scr⟩)
        · exact congrArg (fun v => hcomp_fb ▸ v) (Eq.symm hreadout)
        · dsimp [PortCompatibility, openLoopPortVector, rsyOutAt, feedbackSCR, feedbackStateEmb, csyOut,
            hcomp_fb, hcomp_fb_at, hop_fb_at]
          simp only [eqRec_eq_cast, cast_cast]
      exact step_scr_conn.trans (step_scr_port.trans (step_fb_port.trans step_fb_conn))

noncomputable def scrOutValOfFeedback {n : Nat} (p : RSYParam n) (op : UnconnOutPort p.SCR)
    (out : rsy_OZ (feedbackSCR p)) : p.SCR.VSCR.OutPortVal op.val.1 op.val.2 :=
  cast (feedbackSCR_OutPortVal_eq p op.val) <|
    out ⟨⟨0, op.val⟩, (mem_uoscr_feedbackSCR p op.val).mpr op.prop⟩

lemma feedbackSCR_readout_val {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR)
    (op : UnconnOutPort p.SCR) :
    some (rsyOutAt p.SCR p.hOut x op.val) =
      ((rsy (feedbackSCR p) (feedbackRSYParam p).hOut).RZ (feedbackStateEmb p x)).map
        (fun out => scrOutValOfFeedback p op out) := by
  have h_choose : Classical.choose ((feedbackRSYParam p).hOut 0 x) = fun op => csyOut p.SCR.VSCR p.hOut x op :=
    Trajectory.choose_alwaysOutputs ((openLoopPortVector p).Z 0) ((feedbackRSYParam p).hOut 0) x rfl
  change some (rsyOutAt p.SCR p.hOut x op.val) = some (Classical.choose ((feedbackRSYParam p).hOut 0 x) op.val)
  rw [h_choose]
  rfl

theorem rsy_feedback_RZ_eq {n : Nat} (p : RSYParam n) (x : rsy_SZ p.SCR) (op : UnconnOutPort p.SCR) :
    some (rsyOutAt p.SCR p.hOut x op.val) =
      ((rsy (feedbackSCR p) (feedbackRSYParam p).hOut).RZ (feedbackStateEmb p x)).map
        (fun out => scrOutValOfFeedback p op out) := by
  exact feedbackSCR_readout_val p x op

/--
  Closed-loop equality `Z@ = Z@$` on shared product state and external I/O.
-/
def ClosedLoopEqFeedbackClosedLoop (p : RSYParam n) (x : rsy_SZ p.SCR)
    (po : Option (rsy_IZ p.SCR)) : Prop :=
  ((∀ i, (rsy p.SCR p.hOut).NZ x po i =
      (rsy (feedbackSCR p) (feedbackRSYParam p).hOut).NZ (feedbackStateEmb p x)
        (po.map (rsyIZ_to_feedbackIZ p)) 0 i) ∧
    (∀ op : UnconnOutPort p.SCR,
      some (rsyOutAt p.SCR p.hOut x op.val) =
        ((rsy (feedbackSCR p) (feedbackRSYParam p).hOut).RZ (feedbackStateEmb p x)).map
          (fun out => scrOutValOfFeedback p op out)))

/--
  [textbook/theorem3.64/theorem/closed_loop_eq_feedback]
  Closed-loop equality on shared product state and external I/O.
-/
theorem closed_loop_eq_feedback_closed_loop (p : RSYParam n) (x : rsy_SZ p.SCR)
    (po : Option (rsy_IZ p.SCR)) : ClosedLoopEqFeedbackClosedLoop p x po := by
  constructor
  · intro i
    exact rsy_feedback_NZ_eq p x po i
  · intro op
    exact rsy_feedback_RZ_eq p x op

/--
  [textbook/theorem3.64/theorem/open_loop_closed_loop]
  Theorem 3.64 for non-conjunctive recipes.
-/
theorem open_loop_closed_loop_theorem {n : Nat} (p : RSYParam n) (h : ¬ IsConjunctive p.SCR) :
    InRSY n ⟨conjunctiveSCR p.SCR, p.hOut⟩ (rsy (conjunctiveSCR p.SCR) p.hOut) ∧
    IsPureFeedback (feedbackSCR p) ∧
    (∀ (x : rsy_SZ p.SCR) (po : Option (rsy_IZ p.SCR)),
      ClosedLoopEqFeedbackClosedLoop p x po) := by
  refine ⟨open_loop_is_conjunctive_rsy p, feedbackSCR_is_pure_feedback p h, ?_⟩
  intro x po
  exact closed_loop_eq_feedback_closed_loop p x po

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
