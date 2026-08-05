import Mbse.CouplingIsomorphism
import Mbse.TuringCoupling

/-!
# Building the same machine differently

The point of compiling a dynamics-encoding fragment from a reference is that *candidate* designs can
be checked against it.  A single blessed design demonstrates nothing, so this module exhibits a
family of buildables for the zones of `Mbse.TuringCoupling` and settles, for each, whether it
realises the reference zone.

Conforming variants:

* `instrTapeZone` — the tape carrying an internal step count.  Extra internal structure that
  projects away: a homomorphic image relation, not an isomorphism.
* `altCtlZone` — the control over a re-encoded state space (`ctlStateEquiv`).  Same behaviour under
  a different state encoding: an isomorphism.

Rejected variants, each with a *machine-checked impossibility* rather than a failed attempt:

* `frozenTapeZone` — a tape that accepts commands but never actuates them.
* `blindTapeZone` — a tape that actuates correctly but reports a blank window.

Finally `tmElaboration` swaps *both* conforming zones into the coupling recipe at once and lifts
their zone-level conformance to the whole machine through Theorem 4.56, so the resultant is verified
without re-verifying the machine.  That lift is the reason zone-level checking scales.
-/

namespace TuringCoupling

open Homomorphism PartialDynamicsHomFragment

private theorem option_map_id {α : Type} (o : Option α) : o.map _root_.id = o := by
  cases o <;> rfl

/-! ## A conforming variant: the instrumented tape -/

/-- A tape that also counts how many commands it has actuated. -/
abbrev InstrTape (Γ : Type) := TapeState Γ × Nat

/--
The instrumented tape zone.  The counter is internal: it never reaches a port, so the zone is
observationally the plain tape.
-/
def instrTapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (InstrTape Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨(TapeState.blank Γ, 0)⟩
  NZ tn
    | none => tn
    | some inp => (tn.1.apply (inp .cmd), tn.2 + 1)
  RZ tn := some (tapeReadout tn.1)

theorem instrTapeZone_alwaysOutputs (Γ : Type) [Inhabited Γ] :
    AlwaysOutputs (instrTapeZone Γ) :=
  fun _ => ⟨_, rfl⟩

/-- Forgetting the counter is a homomorphism from the instrumented tape onto the plain tape. -/
def instrTapeHom (Γ : Type) [Inhabited Γ] :
    HomomorphicImageWitness (tapeZone Γ) (instrTapeZone Γ) where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun t => ⟨(t, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro tn oi
    cases oi <;> rfl
  preserves_readout := by
    intro tn
    rfl

/-- The instrumented tape is not a copy of the plain tape: the counter is genuinely extra state. -/
theorem instrTapeHom_not_injective (Γ : Type) [Inhabited Γ] :
    ¬ Function.Injective (instrTapeHom Γ).HS := by
  intro hinj
  have h : ((TapeState.blank Γ, 0) : InstrTape Γ) = (TapeState.blank Γ, 1) := hinj rfl
  exact Nat.zero_ne_one (congrArg Prod.snd h)

/-! ## A conforming variant: the re-encoded control -/

/-- The control's state space under a different encoding. -/
abbrev AltCtl (Γ Λ : Type) := Λ ⊕ (Λ × TapeCmd Γ) ⊕ Unit

/-- The control zone over the re-encoded state space, with the dynamics transported along the
encoding. -/
def altCtlZone (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    DiscreteSystem (AltCtl Γ Λ) ((p : CtlIn) → CtlInVal Γ Λ p)
      ((op : CtlOut) → CtlOutVal Γ op) where
  sz_nonempty := ⟨.inr (.inr ())⟩
  NZ s
    | none => s
    | some inp =>
        ctlStateEquiv Γ Λ
          (CtlState.step M ((ctlStateEquiv Γ Λ).symm s) (inp .sym) (inp .load))
  RZ s := some (ctlReadout ((ctlStateEquiv Γ Λ).symm s))

theorem altCtlZone_alwaysOutputs (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    AlwaysOutputs (altCtlZone Γ Λ M) :=
  fun _ => ⟨_, rfl⟩

/-- Decoding the state is an isomorphism from the re-encoded control onto the control. -/
def altCtlIso (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    IsomorphismWitness (ctlZone Γ Λ M) (altCtlZone Γ Λ M) where
  HS := (ctlStateEquiv Γ Λ).symm
  HI := id
  HO := id
  HS_surjective := (ctlStateEquiv Γ Λ).symm.surjective
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro s oi
    cases oi with
    | none => rfl
    | some inp =>
        show (ctlStateEquiv Γ Λ).symm (ctlStateEquiv Γ Λ _) = _
        rw [Equiv.symm_apply_apply]
        rfl
  preserves_readout := by
    intro s
    rfl
  HS_injective := (ctlStateEquiv Γ Λ).symm.injective
  HI_injective := Function.injective_id
  HO_injective := Function.injective_id

/-! ## Rejected variants

These are the instances a checker must reject.  The impossibility is proved from the definition of a
homomorphic image, so no search over candidate maps is involved: *no* choice of `HS`, `HI`, `HO`
works.
-/

/-- A tape that accepts commands and never actuates them. -/
def frozenTapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (TapeState Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨TapeState.blank Γ⟩
  NZ t _ := t
  RZ t := some (tapeReadout t)

theorem frozenTapeZone_alwaysOutputs (Γ : Type) [Inhabited Γ] :
    AlwaysOutputs (frozenTapeZone Γ) :=
  fun _ => ⟨_, rfl⟩

/--
The frozen tape does not realise the tape: whatever the state map, some reachable command would have
to change a state that the frozen tape leaves fixed.
-/
theorem no_hom_frozenTape (Γ : Type) [Inhabited Γ] (a b : Γ) (hab : a ≠ b) :
    ¬ IsHomomorphicImage (tapeZone Γ) (frozenTapeZone Γ) := by
  rintro ⟨w⟩
  obtain ⟨t, ht⟩ := w.HS_surjective ⟨[], a, []⟩
  obtain ⟨c, hc⟩ := w.HI_surjective (fun p => match p with | TapeIn.cmd => TapeCmd.act b .stay)
  have hstep : w.HS t = (tapeZone Γ).NZ (w.HS t) (some (w.HI c)) :=
    w.preserves_transition t (some c)
  rw [ht, hc] at hstep
  exact hab (congrArg TapeState.head hstep)

/-- A tape that actuates correctly but always reports a blank window. -/
def blindTapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (TapeState Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨TapeState.blank Γ⟩
  NZ t
    | none => t
    | some inp => t.apply (inp .cmd)
  RZ _ := some (fun op => match op with | .scan => (default : Γ) | .window => (default : Γ))

theorem blindTapeZone_alwaysOutputs (Γ : Type) [Inhabited Γ] :
    AlwaysOutputs (blindTapeZone Γ) :=
  fun _ => ⟨_, rfl⟩

/--
The blind tape does not realise the tape: its readout is constant, so it cannot cover two states of
the reference that read out differently.
-/
theorem no_hom_blindTape (Γ : Type) [Inhabited Γ] (a b : Γ) (hab : a ≠ b) :
    ¬ IsHomomorphicImage (tapeZone Γ) (blindTapeZone Γ) := by
  rintro ⟨w⟩
  obtain ⟨t1, h1⟩ := w.HS_surjective ⟨[], a, []⟩
  obtain ⟨t2, h2⟩ := w.HS_surjective ⟨[], b, []⟩
  have e1 := w.preserves_readout t1
  have e2 := w.preserves_readout t2
  rw [h1] at e1
  rw [h2] at e2
  have hread : tapeReadout (⟨[], a, []⟩ : TapeState Γ) =
      tapeReadout (⟨[], b, []⟩ : TapeState Γ) :=
    Option.some.inj (e1.symm.trans e2)
  exact hab (congrFun hread TapeOut.scan)

/-! ## A reference with a silent mode

Every zone above reports on every tick, so the *closed readout* clause family of the fragment is
never exercised.  A reference that deliberately withholds its output in one mode does exercise it,
and the resulting verdicts are the interesting way round: an implementation can fail by reporting
too much.
-/

/--
A tape whose window is only valid once the head has moved off the left end: in the initial mode it
reports nothing, which is a reference-level statement that the output is not defined there.
-/
def quietReadout {Γ : Type} (t : TapeState Γ) : Option ((op : TapeOut) → TapeOutVal Γ op) :=
  match t.left with
  | [] => none
  | _ => some (tapeReadout t)

def quietTapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (TapeState Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨TapeState.blank Γ⟩
  NZ t
    | none => t
    | some inp => t.apply (inp .cmd)
  RZ t := quietReadout t

/--
The plain tape does not realise the silent reference: it reports on every tick, so it can never
cover a reference state whose readout is closed.  A build that says more than its reference permits
is a build that fails to conform.
-/
theorem no_hom_quietTape_from_tape (Γ : Type) [Inhabited Γ] :
    ¬ IsHomomorphicImage (quietTapeZone Γ) (tapeZone Γ) := by
  rintro ⟨w⟩
  obtain ⟨t, ht⟩ := w.HS_surjective (TapeState.blank Γ)
  have hread : (some (w.HO (tapeReadout t)) : Option _) = quietReadout (w.HS t) :=
    w.preserves_readout t
  rw [ht] at hread
  have hnone : (some (w.HO (tapeReadout t)) : Option _) = none := hread
  exact Option.some_ne_none _ hnone

/-- The instrumented tape realises the silent reference: instrumentation is not a readout. -/
def instrQuietTapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (InstrTape Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨(TapeState.blank Γ, 0)⟩
  NZ tn
    | none => tn
    | some inp => (tn.1.apply (inp .cmd), tn.2 + 1)
  RZ tn := quietReadout tn.1

def instrQuietTapeHom (Γ : Type) [Inhabited Γ] :
    HomomorphicImageWitness (quietTapeZone Γ) (instrQuietTapeZone Γ) where
  HS := Prod.fst
  HI := id
  HO := id
  HS_surjective := fun t => ⟨(t, 0), rfl⟩
  HI_surjective := Function.surjective_id
  HO_surjective := Function.surjective_id
  preserves_transition := by
    intro tn oi
    cases oi <;> rfl
  preserves_readout := fun tn => option_map_id (quietReadout tn.1)

theorem instrQuietTape_realises (Γ : Type) [Inhabited Γ] :
    IsHomomorphicImage (quietTapeZone Γ) (instrQuietTapeZone Γ) :=
  ⟨instrQuietTapeHom Γ⟩

/-! ## Lifting zone conformance to the machine

Both conforming zones are swapped into the recipe at once.  Theorem 4.56 then gives the resultant of
the new recipe as a port-preserving homomorphic image of the original resultant, so conformance of
the machine follows from conformance of its zones — the machine itself is never re-verified.
-/

section Elaboration

variable (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ)

/-- Component state spaces of the elaborated recipe. -/
def elabSZ : Fin 2 → Type :=
  Fin.cases (InstrTape Γ) (fun _ => AltCtl Γ Λ)

/-- The elaborated components: instrumented tape, re-encoded control. -/
def elabZ (i : Fin 2) :
    DiscreteSystem (elabSZ Γ Λ i) ((p : tmPort i) → tmPortVal Γ Λ i p)
      ((op : tmOutPort i) → tmOutPortVal Γ i op) :=
  Fin.cases (motive := fun i => DiscreteSystem (elabSZ Γ Λ i)
      ((p : tmPort i) → tmPortVal Γ Λ i p) ((op : tmOutPort i) → tmOutPortVal Γ i op))
    (instrTapeZone Γ) (fun _ => altCtlZone Γ Λ M) i

omit [Finite Γ] [Finite Λ] in
theorem elabZ_alwaysOutputs (i : Fin 2) : AlwaysOutputs (elabZ Γ Λ M i) := by
  fin_cases i
  · exact instrTapeZone_alwaysOutputs Γ
  · exact altCtlZone_alwaysOutputs Γ Λ M

/-- The elaborated zones are distinct: the instrumented tape still has unbounded state. -/
theorem elabZ_distinct (i j : Fin 2) (hne : i ≠ j) : ¬ HEq (elabZ Γ Λ M i) (elabZ Γ Λ M j) := by
  have key : ¬ HEq (instrTapeZone Γ) (altCtlZone Γ Λ M) := by
    have : Infinite (DiscreteSystem (InstrTape Γ) ((p : TapeIn) → TapeInVal Γ p)
        ((op : TapeOut) → TapeOutVal Γ op)) := infinite_discreteSystem
    exact not_heq_of_infinite_finite _ _
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · simpa using key
  · simpa using fun h => key (HEq.symm h)
  · exact absurd rfl hne

/-- Componentwise homomorphisms: forget the counter, decode the control state. -/
def elabHom (i : Fin 2) :
    HomomorphicImageWitness ((tmSCR Γ Λ M).VSCR.Z i) (elabZ Γ Λ M i) :=
  Fin.cases (motive := fun i =>
      HomomorphicImageWitness ((tmSCR Γ Λ M).VSCR.Z i) (elabZ Γ Λ M i))
    (instrTapeHom Γ) (fun _ => (altCtlIso Γ Λ M).toHomomorphicImageWitness) i

theorem elabHom_HI_id (i : Fin 2) : (elabHom Γ Λ M i).HI = id := by
  fin_cases i <;> rfl

theorem elabHom_HO_id (i : Fin 2) : (elabHom Γ Λ M i).HO = id := by
  fin_cases i <;> rfl

/-- Both zone homomorphisms leave the ports alone, so they preserve ports trivially. -/
def elabInPorts (i : Fin 2) :
    PreservesPorts (Equiv.refl ((tmSCR Γ Λ M).VSCR.Port i)) (elabHom Γ Λ M i).HI :=
  Fin.cases (motive := fun i =>
      PreservesPorts (Equiv.refl ((tmSCR Γ Λ M).VSCR.Port i)) (elabHom Γ Λ M i).HI)
    PreservesPorts.id (fun _ => PreservesPorts.id) i

def elabOutPorts (i : Fin 2) :
    PreservesPorts (Equiv.refl ((tmSCR Γ Λ M).VSCR.OutPort i)) (elabHom Γ Λ M i).HO :=
  Fin.cases (motive := fun i =>
      PreservesPorts (Equiv.refl ((tmSCR Γ Λ M).VSCR.OutPort i)) (elabHom Γ Λ M i).HO)
    PreservesPorts.id (fun _ => PreservesPorts.id) i

/-- Swapping both zones is a componentwise elaboration of the machine's recipe. -/
def tmElaboration : ComponentwiseElaboration (tmSCR Γ Λ M) where
  SZ := elabSZ Γ Λ
  PortVal := tmPortVal Γ Λ
  OutPortVal := tmOutPortVal Γ
  Z := elabZ Γ Λ M
  distinct := elabZ_distinct Γ Λ M
  hom := elabHom Γ Λ M
  inPorts := elabInPorts Γ Λ M
  outPorts := elabOutPorts Γ Λ M
  compat := fun op ip h => (tmSCR Γ Λ M).connectivity.2.2.2 op ip h
  matched := by
    intro op ip hm
    rcases (mem_tmCSCR_iff _).mp hm with h | h
    · have h1 : op = wireCmd.1 := congrArg Prod.fst h
      have h2 : ip = wireCmd.2 := congrArg Prod.snd h
      subst h1; subst h2; rfl
    · have h1 : op = wireScan.1 := congrArg Prod.fst h
      have h2 : ip = wireScan.2 := congrArg Prod.snd h
      subst h1; subst h2; rfl

theorem tmElaboration_alwaysOutputs (i : Fin 2) :
    AlwaysOutputs ((elabRecipe (tmElaboration Γ Λ M)).VSCR.Z i) :=
  elabZ_alwaysOutputs Γ Λ M i

/-- The machine built from the two alternative zones. -/
noncomputable def tmElaboratedResultant :
    DiscreteSystem (rsy_SZ (elabRecipe (tmElaboration Γ Λ M)))
      (rsy_IZ (elabRecipe (tmElaboration Γ Λ M)))
      (rsy_OZ (elabRecipe (tmElaboration Γ Λ M))) :=
  rsy (elabRecipe (tmElaboration Γ Λ M)) (tmElaboration_alwaysOutputs Γ Λ M)

/-- The boundary is unchanged: swapping zones does not change the machine's interface. -/
theorem tmElaborated_boundary :
    UISCR (elabRecipe (tmElaboration Γ Λ M)) = UISCR (tmSCR Γ Λ M) ∧
      UOSCR (elabRecipe (tmElaboration Γ Λ M)) = UOSCR (tmSCR Γ Λ M) :=
  ⟨(thm4_56_resultant_homomorphic_image (tmElaboration Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)
      (tmElaboration_alwaysOutputs Γ Λ M)).1,
    (thm4_56_resultant_homomorphic_image (tmElaboration Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)
      (tmElaboration_alwaysOutputs Γ Λ M)).2.1⟩

/-- Theorem 4.56 in action: the rebuilt machine realises the original machine. -/
theorem tmElaboratedResultant_realises_resultant :
    IsHomomorphicImage (tmResultant Γ Λ M) (tmElaboratedResultant Γ Λ M) :=
  (thm4_56_resultant_homomorphic_image (tmElaboration Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)
    (tmElaboration_alwaysOutputs Γ Λ M)).2.2.isHomomorphicImage

/--
The payoff: the rebuilt machine realises the *reference*, obtained by composing the zone-level
conformance with the realisation of the reference by the original coupling.  The machine-level
question was never re-opened.
-/
theorem tmElaboratedResultant_realises_reference :
    IsHomomorphicImage (tmReference Γ Λ M) (tmElaboratedResultant Γ Λ M) :=
  isHomomorphicImage_trans (tmReference_isHomomorphicImage Γ Λ M)
    (tmElaboratedResultant_realises_resultant Γ Λ M)

/-- Hence the rebuilt machine satisfies the fragment compiled from the reference. -/
theorem tmElaboratedResultant_satisfies_reference_fragment :
    SystemSatisfiesPartialDynamicsHom (tmReference Γ Λ M) (tmElaboratedResultant Γ Λ M) :=
  partialDynamicsHom_of_hom (tmElaboratedResultant_realises_reference Γ Λ M)

end Elaboration

end TuringCoupling
