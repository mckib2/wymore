import Mbse.Notation
import Mbse.Wymore
import Mbse.TextbookExercises.Predicates

/-!
# Chapter 2 — selected textbook exercises

Curated exercise solutions with textbook traceability tags.
-/

namespace Mbse.TextbookExercises.Ch02

open FSM Mbse.TextbookExercises

/-! ## Exercise 2.117: trivial infinite system with always-active `NZ` -/

/--
  [textbook/exercise2.117/task/trivial_infinite_always_active]
  Infinite state/output counter with constant readout: active on every step but trivial
  (fails varying-output nontriviality).
-/
def ex2_117_system : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal (fun n (_ : Bool) => n + 1) (fun _ => 0) ⟨0⟩

theorem ex2_117_nz_ne_self (n : Nat) (b : Bool) :
    ex2_117_system.NZ n (some b) ≠ n := by
  simp [ex2_117_system, DiscreteSystem.ofTotal]

/-- [textbook/exercise2.117/task/trivial_infinite_always_active] `NZ(x, p) ≠ x` for every state. -/
theorem ex2_117_always_active : alwaysActiveTransition ex2_117_system :=
  fun n b => ex2_117_nz_ne_self n b

theorem ex2_117_not_finite : notFiniteSystem ex2_117_system := by
  intro h
  exact Infinite.not_finite (α := Nat) h.1

theorem ex2_117_not_nontrivial : ¬ IsNontrivial ex2_117_system := by
  rintro ⟨_, _, hvar⟩
  rcases hvar with ⟨o1, o2, s1, s2, ho, hr1, hr2⟩
  simp [ex2_117_system, DiscreteSystem.ofTotal] at hr1 hr2
  exact ho (hr1.symm.trans hr2)

/-- [textbook/exercise2.117/task/trivial_infinite_always_active] The witness is a trivial system. -/
theorem ex2_117_is_trivial : IsTrivial ex2_117_system :=
  ex2_117_not_nontrivial

/-! ## Exercise 2.118: trivial infinite system with pairwise state-dependent `NZ` -/

/--
  [textbook/exercise2.118/task/trivial_infinite_pairwise_state_dependent]
  Identity transition on `Nat` with constant readout: every distinct pair of states yields
  different `NZ` values, but `NZ(x,p) = x` (fails active-transition nontriviality).
-/
def ex2_118_system : DiscreteSystem Nat Bool Nat :=
  DiscreteSystem.ofTotal (fun n (_ : Bool) => n) (fun _ => 0) ⟨0⟩

theorem ex2_118_nz_distinct (n1 n2 : Nat) (b : Bool) (hne : n1 ≠ n2) :
    ex2_118_system.NZ n1 (some b) ≠ ex2_118_system.NZ n2 (some b) := by
  simp [ex2_118_system, DiscreteSystem.ofTotal]
  exact hne

/-- [textbook/exercise2.118/task/trivial_infinite_pairwise_state_dependent] Distinct states always disagree under `NZ`. -/
theorem ex2_118_pairwise_state_dependent :
    pairwiseStateDependentTransition ex2_118_system :=
  fun n1 n2 b hne => ex2_118_nz_distinct n1 n2 b hne

theorem ex2_118_not_finite : notFiniteSystem ex2_118_system := by
  intro h
  exact Infinite.not_finite (α := Nat) h.1

theorem ex2_118_not_nontrivial : ¬ IsNontrivial ex2_118_system := by
  rintro ⟨_, hact, _⟩
  rcases hact with ⟨x, p, hne⟩
  simp [ex2_118_system, DiscreteSystem.ofTotal] at hne

/-- [textbook/exercise2.118/task/trivial_infinite_pairwise_state_dependent] The witness is trivial. -/
theorem ex2_118_is_trivial : IsTrivial ex2_118_system :=
  ex2_118_not_nontrivial

/-- [textbook/exercise2.118/note/literal_quantification_impossible] No system satisfies unpinned `∀ x1 x2`. -/
theorem ex2_118_literal_quantification_impossible :
    ¬ literalUniversalNzDistinct ex2_118_system :=
  literalUniversalNzDistinct_impossible ex2_118_system

/-! ## Exercise 2.121: state trajectory as composition (traceability aliases) -/

/-- [textbook/exercise2.121/part/step_function] Curated alias; definition is `stepAt` in core. -/
def ex2_121_stepAt (Z : DiscreteSystem SZ IZ OZ) (f : ITZW IZ) (s : Time) : SZ → SZ :=
  _root_.stepAt Z f s

/-- [textbook/exercise2.121/part/fns_membership] Curated alias; proof is `stepAtTotal_satisfiesFNS` in core. -/
theorem ex2_121_step_fns (Z : DiscreteSystem SZ IZ OZ) (f : ITZ IZ) (s : Time) :
    SatisfiesFNS (_root_.stepAtTotal Z f s) :=
  _root_.stepAtTotal_satisfiesFNS Z f s

/-- [textbook/exercise2.121/theorem/composition_formula] Curated alias; proof is in `WymoreCore`. -/
theorem ex2_121_composition (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZ IZ) (t : Time) :
    _root_.generateStateTrajectory Z x (_root_.liftInput f) t =
      _root_.composeStepsFrom Z (_root_.liftInput f) t x :=
  _root_.generateStateTrajectory_total_eq_composeSteps Z x f t

/-! ## Exercise 2.122: finite trajectory loops (traceability alias) -/

/-- [textbook/exercise2.122/theorem/state_trajectory_loops] Curated alias; proof is in `WymoreCore`. -/
theorem ex2_122_loops (Z : DiscreteSystem SZ IZ OZ) [Fintype SZ] (_hFin : IsFinite Z) (x : SZ) (f : ITZ IZ) :
    ∃ t1 t2 : Time, t1 < t2 ∧
      t2 ≤ Fintype.card SZ ∧
      _root_.generateStateTrajectory Z x (_root_.liftInput f) t1 =
      _root_.generateStateTrajectory Z x (_root_.liftInput f) t2 :=
  _root_.generateStateTrajectory_loops_within_card Z _hFin x f

/-! ## Exercise 2.138: time invariance via concatenation (traceability alias) -/

/-- [textbook/exercise2.138/theorem/time_invariance_concatenation] Curated alias; proof is in `Trajectory`. -/
theorem ex2_138_time_invariance_concatenation
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZ IZ) (s t : Time) :
    _root_.generateStateTrajectory Z
        (_root_.generateStateTrajectory Z x (_root_.liftInput f) s) (_root_.liftInput g) t =
      _root_.generateStateTrajectory Z x (_root_.liftInput (_root_.concatenate f g s)) (s + t) :=
  _root_.stateTrajectory_time_invariance_concatenation Z x f g s t

/-! ## Exercise 2.142: reachability via concatenation (traceability alias) -/

/-- [textbook/exercise2.142/theorem/reachable_concatenation] Curated alias; proof is in `Trajectory`. -/
theorem ex2_142_reachable_concatenate
    (Z : DiscreteSystem SZ IZ OZ) (x y z : SZ) (f g : ITZ IZ) (s t : Time)
    (hxy : ReachableBy Z x y (_root_.liftInput f) s) (hyz : ReachableBy Z y z (_root_.liftInput g) t) :
    ReachableBy Z x z (_root_.liftInput (_root_.concatenate f g s)) (s + t) :=
  _root_.reachableBy_concatenate Z x y z f g s t hxy hyz

/-! ## Exercise 2.148: properly aligned SFZ/OPZ structure (traceability aliases) -/

/-- [textbook/exercise2.148/theorem/sfz_card_ge_opz] Curated alias; proof is in `Wymore`. -/
theorem ex2_148_sfz_card_ge_opz {Inp : Type} {m n : Nat} (hn : n ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin n) → Val (Fin.castLE hn j)))
    (_h : IsProperlyAlignedProductReadout hn Val Z) :
    Fintype.card (_root_.SFZ (Fin m)) ≥ Fintype.card (_root_.OPZ (Fin n)) :=
  _root_.properly_aligned_sfz_card_ge_opz hn Val Z _h

/-- [textbook/exercise2.148/theorem/osz_eq_fsz] Curated alias; proof is in `Wymore`. -/
theorem ex2_148_osz_eq_fsz {m n : Nat} (hn : n ≤ m) (Val : Fin m → Type) (j : Fin n) :
    _root_.OSZ (_root_.OPZ (Fin n)) (fun k => Val (Fin.castLE hn k)) j =
      _root_.FSZ (_root_.SFZ (Fin m)) Val (Fin.castLE hn j) :=
  _root_.properly_aligned_osz_eq_fsz hn Val j

/-! ## Exercise 2.146: projective readout OSZ/FSZ pairing (traceability alias) -/

/-- [textbook/exercise2.146/theorem/osz_eq_fsz] Curated alias; proof is in `Wymore`. -/
theorem ex2_146_osz_eq_fsz {IZ OutPort StateFactor : Type}
    {OutPortVal : OutPort → Type} {StateFactorVal : StateFactor → Type}
    (Z : DiscreteSystem ((sf : StateFactor) → StateFactorVal sf) IZ ((op : OutPort) → OutPortVal op))
    (i : OutPort) (j : StateFactor)
    (_hproj : IsProjectiveReadout Z)
    (h : OutPortVal i = StateFactorVal j)
    (_hread : PortReadoutIsFactorProjection Z i j h) :
    _root_.OSZ (_root_.OPZ OutPort) OutPortVal i =
      _root_.FSZ (_root_.SFZ StateFactor) StateFactorVal j :=
  _root_.projective_readout_osz_eq_fsz Z i j _hproj h _hread

/-! ## Exercise 2.149: non-product state ⇒ state readout (traceability aliases) -/

/-- [textbook/exercise2.149/theorem/sz_eq_oz] Curated alias; proof is in `Wymore`. -/
theorem ex2_149_sz_eq_oz {Val : Type} :
    ((i : Fin 1) → Val) = ((i : Fin 1) → Val) :=
  _root_.properly_aligned_non_product_sz_eq_oz

/-- [textbook/exercise2.149/theorem/state_readout] Curated alias; proof is in `Wymore`. -/
theorem ex2_149_state_readout {Inp : Type} {n : Nat}
    (_hNotProd : StateIsNotCartesianProduct n) (hnpos : n ≠ 0) (Val : Fin n → Type)
    (Z : DiscreteSystem ((i : Fin n) → Val i) Inp ((i : Fin n) → Val i))
    (h : IsProperlyAlignedReadout Z) :
    HasStateReadout Z :=
  _root_.properly_aligned_non_product_has_state_readout _hNotProd hnpos Val Z h

/-! ## Exercise 2.150: non-product output readout dichotomy (traceability aliases) -/

/-- [textbook/exercise2.150/theorem/oz_eq_s1z] Curated alias; proof is in `Wymore`. -/
theorem ex2_150_oz_eq_s1z {m : Nat} (hn : 1 ≤ m) (Val : Fin m → Type) :
    _root_.OSZ (_root_.OPZ (Fin 1)) (fun k => Val (Fin.castLE hn k)) (0 : Fin 1) =
      _root_.FSZ (_root_.SFZ (Fin m)) Val (⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩ : Fin m) :=
  _root_.properly_aligned_non_product_oz_eq_s1z hn Val

/-- [textbook/exercise2.150/theorem/readout_dichotomy] Curated alias; proof is in `Wymore`. -/
theorem ex2_150_readout_dichotomy {Inp : Type} {m : Nat}
    (_hNotProdOut : OutputIsNotCartesianProduct 1) (_hnpos : (1 : Nat) ≠ 0)
    (hn : 1 ≤ m) (Val : Fin m → Type)
    (Z : DiscreteSystem ((i : Fin m) → Val i) Inp ((j : Fin 1) → Val (Fin.castLE hn j)))
    (h : IsProperlyAlignedProductReadout hn Val Z) :
    (StateIsNotCartesianProduct m → HasAlignedStateReadout hn Val Z) ∨
      (m > 1 ∧ HasFirstFactorBundledReadout hn Val Z) :=
  _root_.properly_aligned_non_product_output_readout_dichotomy
    _hNotProdOut _hnpos hn Val Z h

/-! ## Exercise 2.116: range of `NZ` and `RZ` -/

/-
  [textbook/exercise2.116/part/i_rng_nz_eq_sz]
  Toggle: every state appears as `NZ(_, _)`.
-/
wymore_system Ex2_116_rngNzEqSz = (SZEx2_116_i, IZEx2_116_i, OZEx2_116_i, NZEx2_116_i, RZEx2_116_i) where
  SZEx2_116_i = {1, 2},
  IZEx2_116_i = {3},
  OZEx2_116_i = {5},
  NZEx2_116_i = {((1, 3), 2), ((2, 3), 1)},
  RZEx2_116_i = {(1, 5), (2, 5)}.

/-- [textbook/exercise2.116/part/i_rng_nz_eq_sz] Witness: `RNG(NZ) = SZ`. -/
theorem ex2_116_i : rngNzEqSz Ex2_116_rngNzEqSz := by
  unfold rngNzEqSz transitionRange
  decide

/-
  [textbook/exercise2.116/part/ii_rng_nz_ne_sz]
  Absorbing: `NZ` always maps to state `v1`, so state `v2` is never in `RNG(NZ)`.
-/
wymore_system Ex2_116_rngNzNeSz = (SZEx2_116_ii, IZEx2_116_ii, OZEx2_116_ii, NZEx2_116_ii, RZEx2_116_ii) where
  SZEx2_116_ii = {1, 2},
  IZEx2_116_ii = {3, 4},
  OZEx2_116_ii = {5, 6},
  NZEx2_116_ii = {((1, 3), 1), ((1, 4), 1), ((2, 3), 1), ((2, 4), 1)},
  RZEx2_116_ii = {(1, 5), (2, 6)}.

/-- [textbook/exercise2.116/part/ii_rng_nz_ne_sz] Witness: `RNG(NZ) ≠ SZ`. -/
theorem ex2_116_ii : rngNzNeSz Ex2_116_rngNzNeSz := by
  unfold rngNzNeSz transitionRange
  decide

/-
  [textbook/exercise2.116/part/iii_rng_rz_eq_oz]
  Surjective readout: both outputs appear in `RNG(RZ)`.
-/
wymore_system Ex2_116_rngRzEqOz = (SZEx2_116_iii, IZEx2_116_iii, OZEx2_116_iii, NZEx2_116_iii, RZEx2_116_iii) where
  SZEx2_116_iii = {1, 2},
  IZEx2_116_iii = {3},
  OZEx2_116_iii = {5, 6},
  NZEx2_116_iii = {((1, 3), 1), ((2, 3), 1)},
  RZEx2_116_iii = {(1, 5), (2, 6)}.

/-- [textbook/exercise2.116/part/iii_rng_rz_eq_oz] Witness: `RNG(RZ) = OZ`. -/
theorem ex2_116_iii : rngRzEqOz Ex2_116_rngRzEqOz := by
  unfold rngRzEqOz readoutRange
  decide

/-
  [textbook/exercise2.116/part/iv_rng_rz_ne_oz]
  Constant readout on both states: output `v6` never appears in `RNG(RZ)`.
-/
wymore_system Ex2_116_rngRzNeOz = (SZEx2_116_iv, IZEx2_116_iv, OZEx2_116_iv, NZEx2_116_iv, RZEx2_116_iv) where
  SZEx2_116_iv = {1, 2},
  IZEx2_116_iv = {3},
  OZEx2_116_iv = {5, 6},
  NZEx2_116_iv = {((1, 3), 1), ((2, 3), 2)},
  RZEx2_116_iv = {(1, 5), (2, 5)}.

/-- [textbook/exercise2.116/part/iv_rng_rz_ne_oz] Witness: `RNG(RZ) ≠ OZ`. -/
theorem ex2_116_iv : rngRzNeOz Ex2_116_rngRzNeOz := by
  unfold rngRzNeOz readoutRange
  decide

end Mbse.TextbookExercises.Ch02
