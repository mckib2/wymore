import Mbse.DPDAWymore

/-!
# Worked DPDA example: the Dyck-1 language (balanced parentheses)

This file validates the DPDA API in [DPDAWymore](DPDAWymore.lean) end-to-end on the classic
one-counter Dyck-1 machine, the canonical context-free (non-regular) language of balanced
single-bracket strings.

## Encoding

- Input alphabet `IS = Fin 2`: `lp = 0` (an open bracket `(`), `rp = 1` (a close bracket `)`).
- Stack alphabet `Γ = Fin 2`: `zZ = 0` is the bottom marker `z0`, `zA = 1` is the counter symbol
  pushed for each unmatched open bracket.
- Control states `STfin = Fin 1`: a single state `0` suffices (the stack is the memory).

## Transition discipline

- `lp`: push a counter symbol `zA` above the current top (`F 0 (some lp) z = some (0, [zA, z])`).
- `rp` with `zA` on top: pop it (`F 0 (some rp) zA = some (0, [])`).
- `rp` with the bottom marker `zZ` on top: undefined (`none`) — an unmatched close bracket gets
  stuck, so the word is rejected.
- No ε-moves are defined, so the machine is trivially deterministic.

## What is proved

- `dyck1_isDeterministic`, `dyck1_noEps`: the determinism conditions.
- `dyck1_respectsBottom` ⇒ `dyck1_step_wellFormed`: runs preserve the `WellFormedStack`
  invariant (the bottom marker is never popped).
- Membership via empty-stack acceptance: `dyck1_accepts_nil`, `dyck1_accepts_balanced`,
  and a `Reaches`-vs-trajectory bridge witness `dyck1_balanced_via_bridge`.
- Non-membership: `dyck1_rejects_unbalanced` (an unmatched `(` leaves a counter symbol on the
  stack), discharged through the functional `runWordNoEps` runner.
-/

namespace DPDA

namespace Dyck1

/-- Open bracket token `(`. -/
def lp : Fin 2 := 0
/-- Close bracket token `)`. -/
def rp : Fin 2 := 1
/-- Bottom-of-stack marker `z0`. -/
def zZ : Fin 2 := 0
/-- Counter symbol pushed per unmatched open bracket. -/
def zA : Fin 2 := 1

/-- The Dyck-1 transition table (partial, no ε-moves). -/
def dyck1F : Fin 1 → Option (Fin 2) → Fin 2 → Option (Fin 1 × List (Fin 2))
  | _, none, _ => none
  | _, some i, z =>
    if i = lp then some (0, [zA, z])
    else if z = zA then some (0, [])
    else none

/-- The Dyck-1 DPDA system. -/
def dyck1 : DPDASystem (Fin 1) (Fin 2) (Fin 1) (Fin 2) where
  st_nonempty := ⟨0⟩
  st_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  gamma_finite := inferInstance
  st_decidable := inferInstance
  gamma_decidable := inferInstance
  z0 := zZ
  F := dyck1F
  G := fun _ _ => 0

@[simp] theorem dyck1_z0 : dyck1.z0 = zZ := rfl
@[simp] theorem dyck1_F : dyck1.F = dyck1F := rfl

/-! ## Determinism -/

/-- Dyck-1 has no ε-moves. -/
theorem dyck1_noEps : NoEpsilonMoves dyck1 := fun _ _ => rfl

/-- Dyck-1 is deterministic (vacuously: it has no ε-moves to conflict with input moves). -/
theorem dyck1_isDeterministic : IsDeterministic dyck1 := by
  intro q Z h a
  simp [dyck1, dyck1F] at h

/-! ## Well-formed-stack preservation -/

/-- Every Dyck-1 transition keeps the bottom marker `zZ` at the bottom of the stack. -/
theorem dyck1_respectsBottom : RespectsBottomMarker dyck1 := by
  intro q inp s q' new_top hWF hF
  cases s with
  | nil => simp only [WellFormedStack] at hWF; exact absurd hWF (by decide)
  | cons z rest =>
    cases inp with
    | none => simp [dyck1, dyck1F] at hF
    | some i =>
      simp only [dyck1_F, dyck1F, peek] at hF
      by_cases hi : i = lp
      · simp only [if_pos hi] at hF
        rw [Option.some.injEq, Prod.mk.injEq] at hF
        obtain ⟨_, rfl⟩ := hF
        simp only [WellFormedStack, updateStack, List.cons_append, List.nil_append] at hWF ⊢
        exact hWF
      · simp only [if_neg hi] at hF
        by_cases hz : z = zA
        · simp only [if_pos hz] at hF
          rw [Option.some.injEq, Prod.mk.injEq] at hF
          obtain ⟨_, rfl⟩ := hF
          subst hz
          cases rest with
          | nil => simp only [WellFormedStack] at hWF; exact absurd hWF (by decide)
          | cons b rest' =>
            simp only [WellFormedStack, updateStack, List.nil_append] at hWF ⊢
            exact hWF
        · simp [if_neg hz] at hF

/-- A single Dyck-1 step preserves the well-formed-stack invariant. -/
theorem dyck1_step_wellFormed (snap : Snapshot (Fin 1) (Fin 2)) (inp : Option (Fin 2))
    (hWF : WellFormedStack dyck1 snap.2) :
    WellFormedStack dyck1 (stepSnapshot dyck1 snap inp).2 :=
  stepSnapshot_preserves_wellFormed dyck1 dyck1_respectsBottom snap inp hWF

/-! ## Membership: balanced words are accepted by empty stack

The balanced word `( )` drives the stack back to the bottom marker. We certify the run through
the `Reaches` ↔ trajectory bridge (`wordToStream_reaches`): a single trajectory evaluation at
time `|w|` discharges the whole computation. -/

/-- The run on `( )` returns to the bottom marker, certified via the trajectory bridge. -/
theorem dyck1_reaches_balanced : Reaches dyck1 (0, [zZ]) [lp, rp] (0, [zZ]) :=
  wordToStream_reaches dyck1 (0, [zZ]) (0, [zZ]) [lp, rp] (by rfl)

/-- `( )` is in the empty-stack language of Dyck-1. -/
theorem dyck1_accepts_balanced : [lp, rp] ∈ LanguageEmptyStack dyck1 0 :=
  ⟨0, dyck1_reaches_balanced⟩

/-- The empty word is accepted by empty stack (the start stack is already just the marker). -/
theorem dyck1_accepts_nil : [] ∈ LanguageEmptyStack dyck1 0 :=
  ⟨0, Reaches.refl _⟩

/-- Bridge form of acceptance: certified directly from a `generateStateTrajectory` evaluation
    via `acceptsEmptyStack_of_trajectory`. -/
theorem dyck1_balanced_via_trajectory : AcceptsEmptyStack dyck1 0 [lp, rp] :=
  acceptsEmptyStack_of_trajectory dyck1 0 [lp, rp] 0 (by rfl)

/-! ## Non-membership: unbalanced words are rejected

`( ( )` leaves one unmatched counter symbol on the stack, so it never returns to the bottom
marker. We discharge this through the functional `runWordNoEps` runner: since Dyck-1 has no
ε-moves, `runWordNoEps_of_reaches` turns any hypothetical accepting run into a concrete stack
value, which we compute and contradict. -/

/-- `( ( )` is not balanced: it is rejected by empty-stack acceptance. -/
theorem dyck1_rejects_unbalanced : [lp, lp, rp] ∉ LanguageEmptyStack dyck1 0 := by
  rintro ⟨q, hreach⟩
  have hrun := runWordNoEps_of_reaches dyck1 dyck1_noEps (0, [zZ]) (q, [zZ]) [lp, lp, rp] hreach
  rw [show runWordNoEps dyck1 (0, [zZ]) [lp, lp, rp] = some (0, [zA, zZ]) from by rfl] at hrun
  have hpair := Option.some.inj hrun
  have hs : ([zA, zZ] : List (Fin 2)) = [zZ] := congrArg Prod.snd hpair
  exact absurd hs (by decide)

/-! ## Def 2.14: nontrivial / trivial -/

/-- Dyck-1 has constant readout `G := fun _ _ => 0`, so it is Wymore-trivial (fails clause (iii)). -/
theorem dyck1_is_trivial : IsTrivial dyck1 := by
  intro h
  rcases (isNontrivial_iff dyck1).1 h with ⟨_, _, o1, o2, _, _, ho12, ho1, ho2⟩
  simp [DPDASystem.toSnapshotDiscreteSystem, dyck1] at ho1 ho2
  have : o1 = o2 := by rw [← Option.some.inj ho1, Option.some.inj ho2]
  exact ho12 this

/-- Varying readout on stack top: `0` at bottom marker, `1` at counter symbol. -/
def dyck1WithOutputG (_q : Fin 1) (z : Fin 2) : Fin 2 :=
  if z = zA then 1 else 0

/-- Dyck-1 with stack-top-dependent readout (output alphabet `Fin 2`). -/
def dyck1WithOutput : DPDASystem (Fin 1) (Fin 2) (Fin 2) (Fin 2) :=
  { st_nonempty := dyck1.st_nonempty
    st_finite := inferInstance
    iz_finite := inferInstance
    oz_finite := inferInstance
    gamma_finite := inferInstance
    st_decidable := inferInstance
    gamma_decidable := inferInstance
    z0 := zZ
    F := dyck1F
    G := dyck1WithOutputG }

theorem dyck1WithOutput_isNontrivial : IsNontrivial dyck1WithOutput := by
  rw [isNontrivial_iff]
  refine ⟨⟨(0, [zZ]), (0, [zA, zZ]), lp, ?_⟩, ⟨(0, [zZ]), lp, ?_⟩, ⟨1, 0, (0, [zA, zZ]), (0, [zZ]), by decide, ?_, ?_⟩⟩
  · intro heq
    simp [stepSnapshot, dyck1F, dyck1WithOutput, updateStack, lp, zZ, zA, peek] at heq
    cases heq
  · intro heq
    simp [stepSnapshot, dyck1F, dyck1WithOutput, updateStack, lp, zZ, peek] at heq
    cases heq
  · dsimp [DPDASystem.toSnapshotDiscreteSystem, dyck1WithOutputG, zA, peek]
    rfl
  · dsimp [DPDASystem.toSnapshotDiscreteSystem, dyck1WithOutputG, zZ, peek]
    rfl

end Dyck1

end DPDA