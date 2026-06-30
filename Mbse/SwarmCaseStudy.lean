import Mbse.Homomorphism
import Mbse.FiniteWymore
import Mbse.SwarmExamples
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Swarm case study: behavioral SearchSpec and parameterized swarm

Parameterized `Fin n` product swarm with continuous `UavState`, behavioral search specification,
homomorphic-image witness on general `DiscreteSystem`, and CSY port vector with mission I/O.
-/

namespace SwarmCaseStudy

open FSM Swarm Homomorphism

def allCells : Finset Cell := Finset.univ

def T_max : Nat := 100

def swarmSize : Nat := 100

/-! ## Mission port vocabulary (shared by Z_spec and Z_impl) -/

inductive MissionPhase | idle | searching | complete | aborted
  deriving DecidableEq, Fintype

inductive MissionCmd | startSearch | pause | abort | tick
  deriving DecidableEq, Fintype

instance : Inhabited MissionCmd := ⟨MissionCmd.tick⟩

structure SpecState where
  covered : Finset Cell
  clock : Fin (T_max + 1)
  phase : MissionPhase
  deriving DecidableEq, Fintype

@[ext]
theorem SpecState.ext {s s' : SpecState}
    (hCov : s.covered = s'.covered) (hC : s.clock = s'.clock) (hP : s.phase = s'.phase) : s = s' := by
  cases s <;> cases s' <;> simp_all

structure MissionOut where
  coveragePct : Fin 101
  missionActive : Bool
  deadlineMet : Bool
  ack : Bool
  deriving DecidableEq, Fintype

structure AgentStatus where
  active : Bool
  rtbPending : Bool
  deriving DecidableEq, Fintype

abbrev SwarmPositions (n : Nat) := Fin n → UavState

/-- Implementation state: agent positions plus mission clock and phase (observable aggregate). -/
structure SwarmState (n : Nat) where
  agents : SwarmPositions n
  clock : Fin (T_max + 1)
  phase : MissionPhase

@[ext]
theorem SwarmState.ext {n} {s s' : SwarmState n}
    (hA : s.agents = s'.agents) (hC : s.clock = s'.clock) (hP : s.phase = s'.phase) : s = s' := by
  cases s <;> cases s' <;> simp_all

abbrev SwarmInput (_ : Nat) := MissionCmd

abbrev SwarmOutput (_ : Nat) := MissionOut

def searchSpecInit : SpecState :=
  { covered := ∅, clock := 0, phase := MissionPhase.idle }

def searchSpecCoverage (st : SpecState) : Finset Cell := st.covered

def searchSpecActive (st : SpecState) : Bool :=
  decide (st.phase = MissionPhase.searching ∨ st.phase = MissionPhase.idle)

def searchSpecNZ (st : SpecState) (_ : MissionCmd) : SpecState := st

def searchSpecRZ (st : SpecState) : MissionOut :=
  let pct := min (100 * st.covered.card / allCells.card) 100
  { coveragePct := ⟨pct, by
      have : pct ≤ 100 := min_le_right _ _
      omega⟩
    missionActive := decide (st.phase = MissionPhase.searching)
    deadlineMet := decide (st.clock.val ≤ T_max)
    ack := decide (st.phase ≠ MissionPhase.aborted) }

def searchSpec : FSMSystem SpecState MissionCmd MissionOut where
  sz_nonempty := ⟨searchSpecInit⟩
  sz_finite := inferInstance
  iz_finite := inferInstance
  oz_finite := inferInstance
  NZ := searchSpecNZ
  RZ := searchSpecRZ

noncomputable def coverageFromSwarm {n : Nat} (s : SwarmPositions n) : Finset Cell :=
  (ActiveAgents s).image fun i => locateCell (s i).x (s i).y

noncomputable def swarmToSpecHS {n : Nat} (s : SwarmState n) : SpecState :=
  { covered := coverageFromSwarm s.agents
    clock := s.clock
    phase := s.phase }

def swarmToSpecHI (cmd : MissionCmd) : MissionCmd := cmd

def swarmToSpecHO (o : MissionOut) : MissionOut := o

def SwarmBatteryOk {n : Nat} (s : SwarmState n) : Prop :=
  ∀ i, (s.agents i).b ≥ rtbThreshold

theorem stepUav_battery_ok {s : UavState} (h : s.b ≥ rtbThreshold) :
    stepUav s = s := by
  simp [stepUav, rtbTransition, if_neg (not_lt_of_ge h)]

def swarmInit (n : Nat) : SwarmState n :=
  { agents := fun _ => UavState.init, clock := 0, phase := MissionPhase.idle }

noncomputable def swarmSystem (n : Nat) : DiscreteSystem (SwarmState n) (SwarmInput n) (SwarmOutput n) :=
  DiscreteSystem.ofTotal
    (fun s _ => { s with agents := fun i => stepUav (s.agents i) })
    (fun s => searchSpecRZ (swarmToSpecHS s))
    ⟨swarmInit n⟩

noncomputable def swarmSystemMorph (n : Nat) : DiscreteSystem (SwarmState n) (SwarmInput n) (SwarmOutput n) :=
  DiscreteSystem.ofTotal
    (fun s _ => s)
    (fun s => searchSpecRZ (swarmToSpecHS s))
    ⟨swarmInit n⟩

theorem swarmSystem_alwaysOutputs (n : Nat) : AlwaysOutputs (swarmSystem n) :=
  ofTotal_alwaysOutputs _ _ _

theorem swarmSystemMorph_alwaysOutputs (n : Nat) : AlwaysOutputs (swarmSystemMorph n) :=
  ofTotal_alwaysOutputs _ _ _

theorem swarmStep_battery_ok {n : Nat} (s : SwarmState n) (h : SwarmBatteryOk s) (cmd : MissionCmd) :
    (swarmSystem n).NZ s (some cmd) = s := by
  simp only [swarmSystem, DiscreteSystem.ofTotal]
  refine SwarmState.ext (funext fun i => stepUav_battery_ok (h i)) rfl rfl

theorem swarmStep_none {n : Nat} (s : SwarmState n) :
    (swarmSystem n).NZ s none = s := by
  simp [swarmSystem, DiscreteSystem.ofTotal]

theorem swarmStep_morph_id {n : Nat} (s : SwarmState n) (cmd : MissionCmd) :
    (swarmSystemMorph n).NZ s (some cmd) = s := by
  simp [swarmSystemMorph, DiscreteSystem.ofTotal]

theorem swarm_homomorphic_image_morph {n : Nat} (s : SwarmState n) (cmd : MissionCmd) :
    swarmToSpecHS ((swarmSystemMorph n).NZ s (some cmd)) =
      searchSpecNZ (swarmToSpecHS s) cmd := by
  simp [swarmToSpecHS, searchSpecNZ, swarmStep_morph_id]

theorem swarm_homomorphic_image_battery {n : Nat} (s : SwarmState n) (h : SwarmBatteryOk s)
    (cmd : MissionCmd) :
    swarmToSpecHS ((swarmSystem n).NZ s (some cmd)) =
      searchSpecNZ (swarmToSpecHS s) cmd := by
  simp [swarmToSpecHS, searchSpecNZ, swarmStep_battery_ok s h cmd]

noncomputable def uavAtCell (c : Cell) : UavState :=
  { x := cellCenterX c, y := cellCenterY c, psi := 0, v := 0, b := rtbThreshold + 1, active := true }

noncomputable def uavInactive : UavState :=
  { x := -1, y := -1, psi := 0, v := 0, b := rtbThreshold + 1, active := false }

theorem uavAtCell_locate (c : Cell) :
    locateCell (uavAtCell c).x (uavAtCell c).y = c := by
  unfold uavAtCell
  exact locateCell_cellCenter c

private theorem mem_toList_of_mem {c : Cell} {cov : Finset Cell} (hc : c ∈ cov) :
    c ∈ cov.toList := (Finset.mem_toList).2 hc

private theorem card_toList (cov : Finset Cell) : cov.toList.length = cov.card :=
  Finset.length_toList cov

private theorem card_le_swarmSize (cov : Finset Cell) : cov.card ≤ swarmSize := by
  unfold swarmSize
  have : cov.card ≤ (Finset.univ : Finset Cell).card := Finset.card_le_card (Finset.subset_univ cov)
  simpa [allCells, Fintype.card_prod] using this

/-- Realize spec state `st` using the first `|covered|` agents at cell centers; rest inactive. -/
noncomputable def swarmStateForSpec (st : SpecState) : SwarmState swarmSize :=
  { agents := fun i =>
      if h : i.val < st.covered.card then
        uavAtCell (st.covered.toList.get ⟨i.val, by rw [card_toList st.covered]; exact h⟩)
      else
        uavInactive
    clock := st.clock
    phase := st.phase }

private theorem swarmStateForSpec_agents_uav {st : SpecState} {i : Fin swarmSize}
    (h : i.val < st.covered.card) :
    (swarmStateForSpec st).agents i =
      uavAtCell (st.covered.toList.get ⟨i.val, by rw [card_toList st.covered]; exact h⟩) := by
  simp [swarmStateForSpec, dif_pos h]

theorem swarmStateForSpec_coverage (st : SpecState) :
    coverageFromSwarm (swarmStateForSpec st).agents = st.covered := by
  let cov := st.covered
  ext c
  simp only [coverageFromSwarm, ActiveAgents, uavAtCell, uavInactive,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨i, hi, hc⟩
    by_cases hlen : i.val < cov.card
    · have hidx : i.val < cov.toList.length := (card_toList cov).symm ▸ hlen
      have hagent := swarmStateForSpec_agents_uav (st := st) hlen
      rw [hagent] at hc
      have heq : cov.toList.get ⟨i.val, hidx⟩ = c :=
        (uavAtCell_locate (cov.toList.get ⟨i.val, hidx⟩)).symm.trans (by convert hc)
      exact heq ▸ (Finset.mem_toList).1 (List.get_mem cov.toList ⟨i.val, hidx⟩)
    · have hdef : (swarmStateForSpec st).agents i = uavInactive := by
        dsimp [swarmStateForSpec]
        split_ifs with hlt
        · exfalso; exact hlen (by simpa [cov] using hlt)
        · rfl
      rw [hdef] at hi
      simp [uavInactive] at hi
  · intro hc
    obtain ⟨j, heq⟩ := List.mem_iff_get.mp (mem_toList_of_mem hc)
    have hjcard : j.val < st.covered.card := by rw [← card_toList cov]; exact j.2
    have hjFin : j.val < swarmSize :=
      Nat.lt_of_lt_of_le j.2 (by simpa [cov] using card_le_swarmSize cov)
    refine ⟨Fin.mk j.val hjFin, ?_, ?_⟩
    · simp only [ActiveAgents, Finset.mem_filter, Finset.mem_univ, true_and,
        @swarmStateForSpec_agents_uav st (Fin.mk j.val hjFin) hjcard, uavAtCell]
    · rw [@swarmStateForSpec_agents_uav st (Fin.mk j.val hjFin) hjcard, uavAtCell_locate, heq]

theorem swarm_homomorphic_image :
    IsHomomorphicImage searchSpec.toDiscreteSystem (swarmSystemMorph swarmSize) :=
  ⟨{
    HS := swarmToSpecHS
    HI := swarmToSpecHI
    HO := swarmToSpecHO
    HS_surjective := by
      intro st
      refine ⟨swarmStateForSpec st, ?_⟩
      apply SpecState.ext
      · exact swarmStateForSpec_coverage st
      · rfl
      · rfl
    HI_surjective := fun cmd => ⟨cmd, rfl⟩
    HO_surjective := fun o => ⟨o, rfl⟩
    preserves_transition := fun s oi => by
      cases oi with
      | none =>
        simp only [swarmSystemMorph, DiscreteSystem.ofTotal, FSMSystem.toDiscreteSystem,
          searchSpec, searchSpecNZ, swarmToSpecHS, Option.map_none]
      | some cmd => exact swarm_homomorphic_image_morph s cmd
    preserves_readout := fun s => by
      simp [swarmSystemMorph, DiscreteSystem.ofTotal, FSMSystem.toDiscreteSystem,
        searchSpec, swarmToSpecHO, Option.map_some]
  }⟩

def SwarmSeparationAlong (n : Nat) (g : STZ (SwarmState n)) (d : ℝ) : Prop :=
  ∀ t, SwarmSeparation (g t).agents d

def SearchCoverageLive (g : STZ SpecState) (T : Nat) : Prop :=
  (∃ t, searchSpecCoverage (g t) = allCells) ∨
    (∀ t, searchSpecActive (g t) → searchSpecCoverage (g t) = allCells ∨ T < T_max)

def SwarmSatisfiesPhi (n : Nat) (d : ℝ) (T : Nat) : Prop :=
  ∀ (s0 : SwarmState n) (f : ITZW MissionCmd),
    SwarmSeparationAlong n (generateStateTrajectory (swarmSystem n) s0 f) d →
    SearchCoverageLive
      (generateStateTrajectory searchSpec.toDiscreteSystem (swarmToSpecHS s0) f) T

theorem swarm_satisfies_separation_battery {n : Nat} (d : ℝ)
    (s : SwarmState n) (hsep : SwarmSeparation s.agents d) (hbat : SwarmBatteryOk s) :
    SwarmSeparationAlong n
      (generateStateTrajectory (swarmSystem n) s (fun _ => none)) d := by
  intro t
  have hstep : generateStateTrajectory (swarmSystem n) s (fun _ => none) t = s := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [_root_.generateStateTrajectory_succ, ih]
      exact swarmStep_none s
  rw [hstep]; exact hsep

theorem homomorphic_image_preserves_spec_traces
    (w : HomomorphicImageWitness searchSpec.toDiscreteSystem (swarmSystemMorph swarmSize))
    (s0 : SwarmState swarmSize) (f : ITZW MissionCmd) :
    ∀ t, w.HS (generateStateTrajectory (swarmSystemMorph swarmSize) s0 f t) =
         generateStateTrajectory searchSpec.toDiscreteSystem (w.HS s0)
           (fun τ => (f τ).map w.HI) t :=
  homomorphicImage_preserves_state_trajectory w s0 f

/-! ## CSY port vector with mission bus and agent status -/

structure AgentState (n : Nat) where
  tag : Fin n
  inner : UavState

noncomputable def agentStatusReadout (s : UavState) : AgentStatus :=
  { active := s.active, rtbPending := decide (s.b < rtbThreshold) }

abbrev MissionPort := Unit → MissionCmd
abbrev StatusPort := Unit → AgentStatus

noncomputable def uavAgent (n : Nat) (i : Fin n) :
    DiscreteSystem (AgentState n) MissionPort StatusPort :=
  DiscreteSystem.ofTotal
    (fun st _ => { tag := i, inner := stepUav st.inner })
    (fun st _ => agentStatusReadout st.inner)
    ⟨{ tag := i, inner := UavState.init }⟩

theorem uavAgent_alwaysOutputs (n : Nat) (i : Fin n) :
    AlwaysOutputs (uavAgent n i) :=
  ofTotal_alwaysOutputs _ _ _

theorem uavAgent_distinct (n : Nat) {i j : Fin n} (h : i ≠ j) :
    ¬ HEq (uavAgent n i) (uavAgent n j) := by
  intro heq
  apply h
  have heq' : uavAgent n i = uavAgent n j := eq_of_heq heq
  have hs := congrArg
    (fun z =>
      (z.NZ { tag := i, inner := UavState.init } (some (fun _ => MissionCmd.tick))).tag) heq'
  simpa [uavAgent, DiscreteSystem.ofTotal] using hs

noncomputable def swarmVector (n : Nat) : _root_.PortSystemVector n where
  SZ := fun _ => AgentState n
  Port := fun _ => Unit
  PortVal := fun _ _ => MissionCmd
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => AgentStatus
  Z := uavAgent n
  distinct := fun i j h => uavAgent_distinct (n := n) (i := i) (j := j) h

theorem swarmVector_alwaysOutputs (n : Nat) (i : Fin n) :
    AlwaysOutputs ((swarmVector n).Z i) :=
  uavAgent_alwaysOutputs n i

noncomputable def csySwarmSystem (n : Nat) :=
  csy (swarmVector n) (swarmVector_alwaysOutputs n)

theorem csySwarm_component_homomorphic (n : Nat) (i : Fin n) :
    Homomorphism.IsHomomorphicImage ((swarmVector n).Z i) (csySwarmSystem n) :=
  Homomorphism.csy_component_homomorphic_image (swarmVector n)
    (swarmVector_alwaysOutputs n)
    (fun j _ => ⟨MissionCmd.tick⟩)
    (fun j _ => ⟨agentStatusReadout UavState.init⟩)
    i

end SwarmCaseStudy

export SwarmCaseStudy (SpecState MissionCmd MissionOut MissionPhase AgentStatus
  searchSpec swarmSystem swarmSystemMorph swarmVector csySwarmSystem
  swarm_homomorphic_image SwarmSeparationAlong SearchCoverageLive SwarmSatisfiesPhi
  SwarmBatteryOk swarm_satisfies_separation_battery homomorphic_image_preserves_spec_traces
  csySwarm_component_homomorphic)
