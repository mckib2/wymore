import Mbse.Homomorphism
import Mbse.FiniteWymore
import Mbse.SwarmExamples

/-!
# Swarm case study: behavioral SearchSpec and parameterized swarm

Parameterized `Fin n` product swarm, behavioral search specification, homomorphic-image
witness, and Prop-level temporal properties. `swarmSystem` includes RTB dynamics;
`swarmSystemMorph` is the kinematic abstraction used for the constructive homomorphism.
-/

namespace SwarmCaseStudy

open FSM Swarm Homomorphism

abbrev Cell := Fin 10 × Fin 10

def allCells : Finset Cell := Finset.univ

def T_max : Nat := 100

def swarmSize : Nat := 100

abbrev SwarmState (n : Nat) := Fin n → UavState

abbrev SwarmInput (_ : Nat) := Unit

abbrev SearchSpecOut := Fin 101 × Bool

abbrev SwarmOutput (_ : Nat) := SearchSpecOut

abbrev SearchSpecState := Finset Cell

def searchSpecInit : SearchSpecState := ∅

def searchSpecCoverage (st : SearchSpecState) : Finset Cell := st
def searchSpecActive (st : SearchSpecState) : Bool := st.Nonempty

def searchSpecNZ (st : SearchSpecState) (_ : Unit) : SearchSpecState := st

def searchSpecRZ (cov : SearchSpecState) : SearchSpecOut :=
  let pct := min (100 * cov.card / allCells.card) 100
  (⟨pct, by omega⟩, cov.Nonempty)

def searchSpec : FSMSystem SearchSpecState Unit SearchSpecOut where
  sz_nonempty := ⟨searchSpecInit⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := searchSpecNZ
  RZ := searchSpecRZ

def coverageFromSwarm {n : Nat} (s : SwarmState n) : Finset Cell :=
  (ActiveAgents s).image fun i => (UavState.x (s i), UavState.y (s i))

def swarmToSpecHS {n : Nat} (s : SwarmState n) : SearchSpecState :=
  coverageFromSwarm s

def swarmToSpecHI (_ : Unit) : Unit := ()

def swarmToSpecHO (o : SearchSpecOut) : SearchSpecOut := o

def SwarmBatteryOk {n : Nat} (s : SwarmState n) : Prop :=
  ∀ i, (UavState.b (s i)).val ≥ rtbThreshold

theorem stepUav_battery_ok {s : UavState} (h : (UavState.b s).val ≥ rtbThreshold) :
    stepUav s = s := by
  unfold stepUav rtbTransition
  simp only [if_neg (Nat.not_lt_of_ge h)]

def swarmSystem (n : Nat) : FSMSystem (SwarmState n) (SwarmInput n) (SwarmOutput n) where
  sz_nonempty := ⟨fun _ => UavState.init⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => fun i => stepUav (s i)
  RZ := fun s => searchSpecRZ (swarmToSpecHS s)

def swarmSystemMorph (n : Nat) : FSMSystem (SwarmState n) (SwarmInput n) (SwarmOutput n) where
  sz_nonempty := ⟨fun _ => UavState.init⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => s
  RZ := fun s => searchSpecRZ (swarmToSpecHS s)

theorem swarmStep_battery_ok {n : Nat} (s : SwarmState n) (h : SwarmBatteryOk s) :
    (swarmSystem n).NZ s () = s := by
  funext i
  simp [swarmSystem, stepUav_battery_ok (h i)]

theorem swarmStep_morph_id {n : Nat} (s : SwarmState n) :
    (swarmSystemMorph n).NZ s () = s := rfl

theorem swarm_homomorphic_image_morph {n : Nat} (s : SwarmState n) :
    swarmToSpecHS ((swarmSystemMorph n).NZ s ()) = searchSpecNZ (swarmToSpecHS s) () := by
  simp [swarmToSpecHS, searchSpecNZ, swarmStep_morph_id]

theorem swarm_homomorphic_image_battery {n : Nat} (s : SwarmState n) (h : SwarmBatteryOk s) :
    swarmToSpecHS ((swarmSystem n).NZ s ()) = searchSpecNZ (swarmToSpecHS s) () := by
  simp [swarmToSpecHS, searchSpecNZ, swarmStep_battery_ok s h]

def uavAtCell (c : Cell) : UavState :=
  UavState.mk c.1 c.2 ⟨rtbThreshold, by decide⟩ true

def uavInactive : UavState :=
  UavState.mk 0 0 ⟨rtbThreshold, by decide⟩ false

private theorem mem_toList_of_mem {c : Cell} {cov : Finset Cell} (hc : c ∈ cov) :
    c ∈ cov.toList := (Finset.mem_toList).2 hc

private theorem card_toList (cov : Finset Cell) : cov.toList.length = cov.card :=
  Finset.length_toList cov

private theorem card_le_swarmSize (cov : Finset Cell) : cov.card ≤ swarmSize := by
  unfold swarmSize
  have : cov.card ≤ (Finset.univ : Finset Cell).card := Finset.card_le_card (Finset.subset_univ cov)
  simpa [allCells, Fintype.card_prod] using this

/-- Realize coverage `cov` using the first `|cov|` agents; remaining agents inactive. -/
noncomputable def swarmStateForCoverage (cov : Finset Cell) : SwarmState swarmSize :=
  fun i =>
    if h : i.val < cov.card then
      uavAtCell (cov.toList.get ⟨i.val, by rw [card_toList cov]; exact h⟩)
    else
      uavInactive

theorem swarmStateForCoverage_coverage (cov : Finset Cell) :
    coverageFromSwarm (swarmStateForCoverage cov) = cov := by
  ext c
  simp only [coverageFromSwarm, swarmStateForCoverage, ActiveAgents, UavState.active,
    uavAtCell, uavInactive, UavState.mk, UavState.x, UavState.y,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨i, hi, hc⟩
    by_cases hlen : i.val < cov.card
    · have hidx : i.val < cov.toList.length := (card_toList cov).symm ▸ hlen
      simp [uavAtCell, UavState.mk, UavState.x, UavState.y, hlen] at hc
      rw [← hc]
      exact (Finset.mem_toList).1 (List.get_mem cov.toList ⟨i.val, hidx⟩)
    · simp [swarmStateForCoverage, uavInactive, UavState.active, hlen] at hi
  · intro hc
    obtain ⟨j, heq⟩ := List.mem_iff_get.mp (mem_toList_of_mem hc)
    have hjcard : j.val < cov.card := by rw [← card_toList cov]; exact j.2
    have hjFin : j.val < swarmSize := by
      have := card_le_swarmSize cov
      omega
    refine ⟨Fin.mk j.val hjFin, ?_, ?_⟩
    · simp [ActiveAgents, swarmStateForCoverage, UavState.active, uavAtCell, hjcard]
    · simp [swarmStateForCoverage, hjcard, uavAtCell]
      exact heq

theorem swarm_homomorphic_image :
    IsHomomorphicImage searchSpec (swarmSystemMorph swarmSize) :=
  ⟨{
    HS := swarmToSpecHS
    HI := swarmToSpecHI
    HO := swarmToSpecHO
    HS_surjective := by
      intro st
      refine ⟨swarmStateForCoverage st, ?_⟩
      simp [swarmToSpecHS, swarmStateForCoverage_coverage]
    HI_surjective := fun _ => ⟨(), rfl⟩
    HO_surjective := fun o => ⟨o, rfl⟩
    preserves_transition := fun s _ => swarm_homomorphic_image_morph s
    preserves_readout := fun _ => rfl
  }⟩

def SwarmSeparationAlong (n : Nat) (g : STZ (SwarmState n)) (d : Nat) : Prop :=
  ∀ t, SwarmSeparation (g t) d

def SearchCoverageLive (g : STZ SearchSpecState) (T : Nat) : Prop :=
  (∃ t, searchSpecCoverage (g t) = allCells) ∨
    (∀ t, searchSpecActive (g t) → searchSpecCoverage (g t) = allCells ∨ T < T_max)

def SwarmSatisfiesPhi (n : Nat) (d T : Nat) : Prop :=
  ∀ (s0 : SwarmState n) (f : ITZ Unit),
    SwarmSeparationAlong n (generateStateTrajectory (swarmSystem n) s0 f) d →
    SearchCoverageLive (generateStateTrajectory searchSpec (swarmToSpecHS s0) f) T

theorem swarm_satisfies_separation_battery {n : Nat} (d : Nat)
    (s : SwarmState n) (hsep : SwarmSeparation s d) (hbat : SwarmBatteryOk s) :
    SwarmSeparationAlong n (generateStateTrajectory (swarmSystem n) s (fun _ => ())) d := by
  intro t
  have hstep : generateStateTrajectory (swarmSystem n) s (fun _ => ()) t = s := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp [FSM.generateStateTrajectory_succ, swarmStep_battery_ok s hbat, ih]
  rw [hstep]; exact hsep

theorem homomorphic_image_preserves_spec_traces
    (w : FSM.HomomorphicImageWitness searchSpec (swarmSystemMorph swarmSize))
    (s0 : SwarmState swarmSize) (f : ITZ Unit) :
    ∀ t, w.HS (generateStateTrajectory (swarmSystemMorph swarmSize) s0 f t) =
         generateStateTrajectory searchSpec (w.HS s0) (w.HI ∘ f) t :=
  FSM.homomorphicImage_preserves_state_trajectory w s0 f

/-! ## CSY port vector -/

structure AgentState (n : Nat) where
  tag : Fin n
  inner : UavState
  deriving DecidableEq

def agentStateFinset (n : Nat) : Finset (AgentState n) :=
  (Finset.univ : Finset (Fin n × UavState)).map
    ⟨fun p => { tag := p.1, inner := p.2 },
      by
        intro a b h
        cases a
        cases b
        cases h
        rfl⟩

instance {n} : Fintype (AgentState n) where
  elems := agentStateFinset n
  complete := fun x => by
    refine Finset.mem_map.mpr ⟨⟨x.tag, x.inner⟩, Finset.mem_univ _, ?_⟩
    simp

def uavAgent (n : Nat) (i : Fin n) : FSMSystem (AgentState n) (Unit → Unit) (Unit → Unit) where
  sz_nonempty := ⟨{ tag := i, inner := UavState.init }⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := fun s _ => { tag := i, inner := stepUav s.inner }
  RZ := fun _ _ => ()

theorem uavAgent_distinct (n : Nat) {i j : Fin n} (h : i ≠ j) :
    ¬ HEq (uavAgent n i) (uavAgent n j) := by
  intro heq
  apply h
  have heq' : uavAgent n i = uavAgent n j := eq_of_heq heq
  have hs := congrArg
    (fun z => (z.NZ { tag := i, inner := UavState.init } (fun _ => ())).tag) heq'
  simpa [uavAgent] using hs

def swarmVector (n : Nat) : FSM.PortSystemVector n where
  SZ := fun _ => AgentState n
  Port := fun _ => Unit
  PortVal := fun _ _ => Unit
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Unit
  Z := uavAgent n
  Port_finite := fun _ => inferInstance
  PortVal_finite := fun i _ => inferInstance
  OutPort_finite := fun _ => inferInstance
  OutPortVal_finite := fun _ _ => inferInstance
  Port_decidable := fun _ => inferInstance
  OutPort_decidable := fun _ => inferInstance
  distinct := fun i j h => uavAgent_distinct (n := n) (i := i) (j := j) h

def csySwarmSystem (n : Nat) := FSM.csy (swarmVector n)

end SwarmCaseStudy

export SwarmCaseStudy (SearchSpecState SearchSpecOut searchSpec swarmSystem swarmSystemMorph
  swarmVector csySwarmSystem swarm_homomorphic_image SwarmSeparationAlong SearchCoverageLive
  SwarmSatisfiesPhi SwarmBatteryOk swarm_satisfies_separation_battery
  homomorphic_image_preserves_spec_traces)
