import Mbse.PropertySemantics
import Mbse.CombinationalWymore

/-!
# Property fragments for assertional verification

Minimal temporal-logic connectives beyond execution encoding, scoped to
homomorphism-visible atoms for combinational and finite FSM layers.
-/

namespace PropertyFragment

open TemporalLogic PropertySemantics Combinational

/-! ## Combinational atoms -/

/-- Atoms visible on combinational input/output trajectories. -/
inductive CombAtom (IZ OZ : Type) where
  | input (i : IZ)
  | output (o : OZ)

variable {IZ OZ : Type}

/-- LTL trace induced by a combinational system run. -/
def combTrace (C : CombinationalSystem IZ OZ) (f : ITZ IZ) : Trace (CombAtom IZ OZ) where
  holds := fun t a =>
    match a with
    | .input i => f t = i
    | .output o => C.RZ (f t) = o

@[simp]
theorem combTrace_input (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) (i : IZ) :
    (combTrace C f).holds t (.input i) ↔ f t = i := by
  simp [combTrace]

@[simp]
theorem combTrace_output (C : CombinationalSystem IZ OZ) (f : ITZ IZ) (t : Time) (o : OZ) :
    (combTrace C f).holds t (.output o) ↔ C.RZ (f t) = o := by
  simp [combTrace]

/-- `G(input i → output o)` as a single-tick combinational constraint. -/
def combCell (i : IZ) (o : OZ) : LTL (CombAtom IZ OZ) :=
  LTL.G (LTL.imp (LTL.atom (.input i)) (LTL.atom (.output o)))

/-- Property set encoding a complete function table `F : IZ → OZ`. -/
noncomputable def combFunctionTable (C : CombinationalSystem IZ OZ) (F : IZ → OZ) :
    PropertySet (LTL (CombAtom IZ OZ)) :=
  let _ : Fintype IZ := C.iz_finite
  ⟨Finset.univ.toList.map fun i => combCell i (F i)⟩

theorem mem_combFunctionTable (C : CombinationalSystem IZ OZ) (F : IZ → OZ) (i : IZ) :
    combCell i (F i) ∈ (combFunctionTable C F).formulas := by
  simp [combFunctionTable, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]

theorem mem_combFunctionTable_iff (C : CombinationalSystem IZ OZ) (F : IZ → OZ)
    (φ : LTL (CombAtom IZ OZ)) :
    φ ∈ (combFunctionTable C F).formulas ↔ ∃ i, φ = combCell i (F i) := by
  dsimp [combFunctionTable]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, heq⟩
    exact ⟨i, heq.symm⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, heq.symm⟩

/-- A combinational system satisfies the function-table property set. -/
def CombSatisfiesFunction (C : CombinationalSystem IZ OZ) (F : IZ → OZ) : Prop :=
  ∀ (f : ITZ IZ) (φ : LTL (CombAtom IZ OZ)),
    φ ∈ (combFunctionTable C F).formulas → (combTrace C f).models φ

theorem combSatisfiesFunction_iff (C : CombinationalSystem IZ OZ) (F : IZ → OZ) :
    CombSatisfiesFunction C F ↔ ∀ i, C.RZ i = F i := by
  constructor
  · intro h i
    have hφ := h (fun _ => i) (combCell i (F i)) (mem_combFunctionTable C F i)
    have h0 := hφ 0 (Nat.zero_le 0)
    simp only [satisfiesAt, combTrace] at h0
    exact h0 (by simp)
  · intro hC f φ hmem
    rcases (mem_combFunctionTable_iff C F φ).mp hmem with ⟨i, heq⟩
    subst heq
    simp only [Trace.models, satisfiesAt, combCell]
    intro t' _ hIn
    simp [combTrace] at hIn ⊢
    rw [hIn, hC i]

/-- Combinational satisfaction uses the same trace-modeling pipeline as `SystemSatisfiesLTL`. -/
theorem combSatisfiesFunction_iff_traceModels (C : CombinationalSystem IZ OZ) (F : IZ → OZ) :
    CombSatisfiesFunction C F ↔
      ∀ (f : ITZ IZ) (φ : LTL (CombAtom IZ OZ)),
        φ ∈ (combFunctionTable C F).formulas → (combTrace C f).models φ :=
  Iff.rfl

end PropertyFragment
