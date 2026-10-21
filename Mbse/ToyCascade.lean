import Mbse.Homomorphism
import Mbse.IORTemporalFragment
import Mbse.TechdocAttr
import Mbse.Wymore
import Mbse.WymoreImplementation
import Mbse.WymoreRequirements
import Mbse.WymoreSystemModes
import Mbse.WymoreTechnology
import Mbse.WymoreTechnologyImpl
import Mathlib.Tactic.FinCases

/-!
# Toy two-component cascade (techdoc fixture)

A minimal buildable technology with a one-wire cascade coupling and an explicit
`ImplementableSystemDesign` packaged like SAINT's `saint_in_isr`. Used as the
primary playground for `scripts/techdoc` without depending on saint-mbse.

Component indices: 0 sensor · 1 actor. Wire: sensor.out → actor.in.
Boundary: sensor load (Bool) and actor output (Bool).
-/

namespace ToyCascade

open Classical
open Homomorphism
open IORTemporalFragment
open WymoreImplementation
open WymoreRequirements
open WymoreSystemModes
open WymoreTechnology
open Mbse.Wymore

/-! ## Uniform cells (shared types → `eq_of_heq` distinctness) -/

structure CellState where
  value : Bool
  lastTouched : Fin 2 := 0
  deriving DecidableEq, Repr

def cellInit : CellState := ⟨false, 0⟩

def cellStep (slot : Fin 2) (_s : CellState) (i : Unit → Bool) : CellState :=
  ⟨i (), slot⟩

def cellRead (_slot : Fin 2) (s : CellState) : Unit → Bool :=
  fun _ => s.value

def toyCell (slot : Fin 2) :
    DiscreteSystem CellState (Unit → Bool) (Unit → Bool) :=
  DiscreteSystem.ofTotal (cellStep slot) (cellRead slot) ⟨cellInit⟩

theorem toyCell_alwaysOutputs (slot : Fin 2) : AlwaysOutputs (toyCell slot) :=
  ofTotal_alwaysOutputs (cellStep slot) (cellRead slot) ⟨cellInit⟩

def sensor : DiscreteSystem CellState (Unit → Bool) (Unit → Bool) := toyCell 0
def actor : DiscreteSystem CellState (Unit → Bool) (Unit → Bool) := toyCell 1

/-- Idle stim; still enters `ofTotal`'s `some` branch. -/
def cellIdle : Unit → Bool := fun _ => false

/-- Behavioral signature: idle step from shared init reports `lastTouched`. -/
def cellSig (slot : Fin 2) : Fin 2 :=
  ((toyCell slot).NZ cellInit (some cellIdle)).lastTouched

theorem cellSig_val (slot : Fin 2) : cellSig slot = slot := by
  fin_cases slot <;> simp [cellSig, toyCell, DiscreteSystem.ofTotal, cellStep, cellInit, cellIdle]

theorem toyCell_distinct (i j : Fin 2) (hne : i ≠ j) : ¬ HEq (toyCell i) (toyCell j) := by
  intro h
  have he : cellSig i = cellSig j := by
    have hsys : toyCell i = toyCell j := eq_of_heq h
    simp [cellSig, hsys]
  rw [cellSig_val, cellSig_val] at he
  exact hne he

/-! ## Coupling: one cascade wire -/

def toyVSCR : PortSystemVector 2 where
  SZ := fun _ => CellState
  Port := fun _ => Unit
  PortVal := fun _ _ => Bool
  OutPort := fun _ => Unit
  OutPortVal := fun _ _ => Bool
  Z := toyCell
  distinct := toyCell_distinct

private abbrev ToyEdge :=
  (Σ i : Fin 2, toyVSCR.OutPort i) × (Σ i : Fin 2, toyVSCR.Port i)

/-- Sensor output feeds the actor. -/
def sensorToActor : ToyEdge := (⟨0, ()⟩, ⟨1, ()⟩)

def toyCSCR : Set ToyEdge := {sensorToActor}

lemma toy_oneToOne : IsOneToOneRelation toyCSCR := by
  constructor
  · intro x y1 y2 h1 h2
    simp only [toyCSCR, Set.mem_singleton_iff] at h1 h2
    exact (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm
  · intro x1 x2 y h1 h2
    simp only [toyCSCR, Set.mem_singleton_iff] at h1 h2
    exact (Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm

lemma toy_properDomain : IsProperDomain toyCSCR := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy⟩ := h (⟨1, ()⟩ : Σ i, toyVSCR.OutPort i)
  simp only [toyCSCR, Set.mem_singleton_iff] at hy
  nomatch (Prod.mk.inj hy).1

lemma toy_properRange : IsProperRange toyCSCR := by
  intro h
  rw [Set.eq_univ_iff_forall] at h
  obtain ⟨x, hx⟩ := h (⟨0, ()⟩ : Σ i, toyVSCR.Port i)
  simp only [toyCSCR, Set.mem_singleton_iff] at hx
  nomatch (Prod.mk.inj hx).2

lemma toy_compat : PortCompatibility toyVSCR toyCSCR := by
  intro _ _ hop
  simp only [toyCSCR, Set.mem_singleton_iff] at hop
  cases hop; rfl

lemma toy_connectivity : IsSystemConnectivity toyVSCR toyCSCR :=
  ⟨toy_oneToOne, toy_properDomain, toy_properRange, toy_compat⟩

def toySCR : SystemCouplingRecipe 2 where
  VSCR := toyVSCR
  CSCR := toyCSCR
  connectivity := toy_connectivity

theorem sensor_load_unconnected :
    (⟨0, ()⟩ : Σ i, toySCR.VSCR.Port i) ∉ CISCR toySCR := by
  rw [mem_ciscr_iff]
  rintro ⟨op, hop⟩
  simp only [toySCR, toyCSCR] at hop
  nomatch (Prod.mk.inj hop).2

theorem actor_output_unconnected :
    (⟨1, ()⟩ : Σ i, toySCR.VSCR.OutPort i) ∉ COSCR toySCR := by
  rintro ⟨ip, hip⟩
  simp only [toySCR, toyCSCR] at hip
  nomatch (Prod.mk.inj hip).1

theorem sensor_out_connected :
    (⟨0, ()⟩ : Σ i, toySCR.VSCR.OutPort i) ∈ COSCR toySCR :=
  ⟨⟨1, ()⟩, by
    change (⟨0, ()⟩, ⟨1, ()⟩) ∈ toyCSCR
    exact Set.mem_singleton _⟩

theorem actor_in_connected :
    (⟨1, ()⟩ : Σ i, toySCR.VSCR.Port i) ∈ CISCR toySCR :=
  ⟨⟨0, ()⟩, by
    change (⟨0, ()⟩, ⟨1, ()⟩) ∈ toyCSCR
    exact Set.mem_singleton _⟩

/-! ## Technology + buildable resultant -/

def toyTechnology : Technology :=
  Technology.mk
    { AnyDiscreteSystem.of sensor, AnyDiscreteSystem.of actor }
    ⟨AnyDiscreteSystem.of sensor, by simp⟩

theorem sensor_mem : memTechnology toyTechnology sensor := by
  refine memTechnology_of _ _ ?_
  simp [toyTechnology, Technology.mk, Technology.carrier]

theorem actor_mem : memTechnology toyTechnology actor := by
  refine memTechnology_of _ _ ?_
  simp [toyTechnology, Technology.mk, Technology.carrier]

theorem toy_vscr_subset : VSCRSubsetTechnology toySCR.VSCR toyTechnology := by
  intro i
  refine memTechnology_of _ _ ?_
  fin_cases i
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [Set.mem_singleton_iff]
    rfl

abbrev toy_hOut : ∀ k, AlwaysOutputs (toySCR.VSCR.Z k) :=
  fun k => toyCell_alwaysOutputs k

theorem toy_resultant_is_buildable :
    IsBuildableWith toyTechnology toySCR toy_hOut (rsy toySCR toy_hOut) :=
  ⟨toy_vscr_subset, IsResultantOf.of_rsy toySCR toy_hOut⟩

noncomputable def toyResultant :
    DiscreteSystem (rsy_SZ toySCR) (rsy_IZ toySCR) (rsy_OZ toySCR) :=
  rsy toySCR toy_hOut

noncomputable def toy_design : BuildableSystemDesign toyTechnology where
  n := 2
  SCR := toySCR
  hOut := toy_hOut
  SZ := rsy_SZ toySCR
  IZ := rsy_IZ toySCR
  OZ := rsy_OZ toySCR
  Z := toyResultant
  buildable := toy_resultant_is_buildable

/-! ## Boundary ports and embeds -/

theorem sensor_in_uiscr :
    (⟨0, ()⟩ : Σ i, toySCR.VSCR.Port i) ∈ UISCR toySCR :=
  sensor_load_unconnected

theorem actor_out_uoscr :
    (⟨1, ()⟩ : Σ i, toySCR.VSCR.OutPort i) ∈ UOSCR toySCR :=
  actor_output_unconnected

def toyLoadIn : UnconnInPort toySCR := ⟨⟨0, ()⟩, sensor_in_uiscr⟩
def toyActOut : UnconnOutPort toySCR := ⟨⟨1, ()⟩, actor_out_uoscr⟩

noncomputable def toyInEmbed (b : Bool) : rsy_IZ toySCR := fun ip =>
  if h : ip = toyLoadIn then by subst h; exact b
  else false

noncomputable def toyOutEmbed (b : Bool) : rsy_OZ toySCR := fun op =>
  if h : op = toyActOut then by subst h; exact b
  else false

theorem toyInEmbed_injective : Function.Injective toyInEmbed := by
  intro a b hab
  have h := congrFun hab toyLoadIn
  simp only [toyInEmbed, ↓reduceDIte] at h
  exact h

theorem toyOutEmbed_injective : Function.Injective toyOutEmbed := by
  intro a b hab
  have h := congrFun hab toyActOut
  simp only [toyOutEmbed, ↓reduceDIte] at h
  exact h

/-! ## Boundary model + IOR + FSD -/

def toyFedInit : rsy_SZ toySCR
  | 0 => { cellInit with lastTouched := 0 }
  | 1 => { cellInit with lastTouched := 1 }

noncomputable def toyMissionReadout (x : rsy_SZ toySCR) : Bool :=
  let out := Classical.choose (rsy_alwaysOutputs toySCR toy_hOut x)
  out toyActOut

noncomputable def toyMissionSpec :
    DiscreteSystem (rsy_SZ toySCR) Bool Bool :=
  DiscreteSystem.ofTotal
    (fun s m => toyResultant.NZ s (some (toyInEmbed m)))
    toyMissionReadout
    ⟨toyFedInit⟩

noncomputable def toyMissionOut (f : ITZ Bool) : ITZ Bool := fun t =>
  toyMissionReadout
    (generateStateTrajectory toyMissionSpec toyFedInit (liftInput f) t)

noncomputable def toyMissionIOR : InputOutputRequirement Bool Bool :=
  functionalIOR toyMissionOut

theorem toyMissionSpec_out (f : ITZ Bool) (t : Time) :
    generateOutputTrajectory toyMissionSpec toyFedInit (liftInput f) t =
      some (toyMissionOut f t) := by
  simp [toyMissionOut, generateOutputTrajectory, toyMissionSpec, DiscreteSystem.ofTotal]

theorem toyMissionSpec_satisfies :
    SatisfiesIOR toyMissionSpec toyMissionIOR toyFedInit Set.univ :=
  (satisfies_functionalIOR_iff (IR := Bool) (OR := Bool)
    toyMissionSpec toyMissionOut toyFedInit).mpr toyMissionSpec_out

noncomputable def toyMission_fsd : FunctionalSystemDesign toyMissionIOR where
  S := rsy_SZ toySCR
  Z := toyMissionSpec
  DSZ := toyFedInit
  TSZ := Set.univ
  satisfies := toyMissionSpec_satisfies

/-! ## Implements: boundary model ↪ resultant -/

noncomputable def projectToyOut (o : rsy_OZ toySCR) : Bool :=
  o toyActOut

theorem projectToyOut_readout (x : rsy_SZ toySCR) :
    projectToyOut (Classical.choose (rsy_alwaysOutputs toySCR toy_hOut x)) =
      toyMissionReadout x :=
  rfl

theorem project_toyOutEmbed (b : Bool) : projectToyOut (toyOutEmbed b) = b := by
  simp [projectToyOut, toyOutEmbed]

noncomputable def toyMissionSpecFull :
    DiscreteSystem (rsy_SZ toySCR) Bool (rsy_OZ toySCR) :=
  DiscreteSystem.ofTotal
    (fun s m => toyResultant.NZ s (some (toyInEmbed m)))
    (fun s => Classical.choose (rsy_alwaysOutputs toySCR toy_hOut s))
    ⟨toyFedInit⟩

theorem toyMissionFull_readout_commute (x : rsy_SZ toySCR) :
    (toyMissionSpecFull.RZ x).map id = toyResultant.RZ x := by
  simp [toyMissionSpecFull, DiscreteSystem.ofTotal]
  exact (Classical.choose_spec (rsy_alwaysOutputs toySCR toy_hOut x)).symm

noncomputable def toyMissionFull_mode : SystemMode toyMissionSpecFull toyResultant :=
  primaryModeOfMaps toyMissionSpecFull toyResultant
    id toyInEmbed id
    Function.injective_id toyInEmbed_injective Function.injective_id
    (fun _ _ => rfl)
    toyMissionFull_readout_commute

noncomputable def toyMission_hom :
    HomomorphicImageWitness toyMissionSpec toyMissionSpecFull where
  HS := id
  HI := id
  HO := projectToyOut
  HS_surjective := Function.surjective_id
  HI_surjective := Function.surjective_id
  HO_surjective := fun b => ⟨toyOutEmbed b, project_toyOutEmbed b⟩
  preserves_transition := by
    intro x oi
    cases oi <;> simp [toyMissionSpec, toyMissionSpecFull, DiscreteSystem.ofTotal]
  preserves_readout := by
    intro x
    simp [toyMissionSpec, toyMissionSpecFull, DiscreteSystem.ofTotal, Option.map,
      projectToyOut_readout]

noncomputable def toyMission_impl : Implements toyMissionSpec toyResultant where
  ModeState := rsy_SZ toySCR
  ModeInput := Bool
  ModeOutput := rsy_OZ toySCR
  modeSystem := toyMissionSpecFull
  mode := toyMissionFull_mode
  hom := toyMission_hom

/--
Toy two-component cascade.
Minimal technology with a one-wire sensor→actor cascade, functional IOR on the
Bool boundary, and an explicit ImplementableSystemDesign (ISR / PoI).
-/
@[techdoc "toy"]
noncomputable def toy_in_isr :
    ImplementableSystemDesign toyMissionIOR toyTechnology where
  fsd := toyMission_fsd
  n := 2
  SCR := toySCR
  hOut := toy_hOut
  SZ2 := rsy_SZ toySCR
  IZ2 := rsy_IZ toySCR
  OZ2 := rsy_OZ toySCR
  Z2 := toyResultant
  buildable := toy_resultant_is_buildable
  impl := toyMission_impl

theorem toy_gallery_ok :
    toy_design.n = 2 ∧ toy_in_isr.n = 2 ∧
      memTechnology toyTechnology sensor ∧ memTechnology toyTechnology actor :=
  ⟨rfl, rfl, sensor_mem, actor_mem⟩

end ToyCascade
