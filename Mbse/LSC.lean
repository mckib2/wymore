import Mbse.WymoreCore
import Mbse.WymoreRequirements

/-!
# Minimal Universal Live Sequence Charts (assertional)

A compact Universal LSC fragment for encoding Wymore input/output requirements
graphically.  Semantics are **assertional** (pre-chart trigger ⇒ main-chart
guarantee), not an operational play-out / Play-Engine.

**In scope:** two lifelines (`Env`, `Sys`), cold pre-chart / hot main-chart,
messages, conditions, discrete tick sync, silence (no message at a tick).

**Out of scope (v1):** play-out, anti-scenario engines, alt/loop operators,
multi-instance systems, continuous time.

Satisfaction is defined on the semantic kernel (`times`, `preInputs`, `allows`).
`preChart` / `mainChart` are optional diagrammatic presentations for graphics;
they do not alter the assertional reading.
-/

namespace LSC

open WymoreRequirements

/-! ## Syntax -/

/-- Boundary lifelines used by the IOR encoding.  Extensible later for multi-instance charts. -/
inductive Lifeline where
  | env
  | sys
  deriving DecidableEq, Repr

/-- LSC temperature: cold (may fail without breach) vs hot (failure is a requirement breach). -/
inductive Temperature where
  | cold
  | hot
  deriving DecidableEq, Repr

/--
  Diagrammatic chart element.  Presentation only: assertional satisfaction does
  not interpret these constructors.  Silence is the absence of a message at a
  tick (no alphabet idle token).
-/
inductive Element (IR OR : Type) where
  | inMsg (temp : Temperature) (tick : Time) (val : IR)
  | outMsg (temp : Temperature) (tick : Time) (val : OR)
  | outSymbolic (temp : Temperature) (tick : Time) (binder : String)
  | condition (temp : Temperature) (tick : Option Time) (label : String)
  | tickSync (tick : Time)
  | silenceOut (temp : Temperature) (tick : Time)
  deriving Repr

/-- Ordered diagrammatic body (location index = list index). -/
structure ChartBody (IR OR : Type) where
  elements : List (Element IR OR)
  deriving Repr

/-- Empty diagrammatic body. -/
def ChartBody.empty {IR OR : Type} : ChartBody IR OR :=
  ⟨[]⟩

/--
  Universal Live Sequence Chart.

  * `times` — discrete horizon (`TSR` when compiled from an IOR).
  * `preInputs` — cold pre-chart: eligible input trajectories (trigger).
  * `allows` — hot main-chart: admissible input/output pairs (guarantee).
  * `preChart` / `mainChart` — optional drawable expansion.
-/
structure UniversalLSC (IR OR : Type) where
  name : String
  times : Set Time
  preInputs : Set (ITZ IR)
  allows : ITZ IR → ITZ OR → Prop
  preChart : ChartBody IR OR := ChartBody.empty
  mainChart : ChartBody IR OR := ChartBody.empty

/-! ## Assertional semantics -/

/--
  A discrete system satisfies a Universal LSC on timescale `T` when every
  pre-chart match (eligible input, possibly extended by `agreesOn` on
  `chart.times`) forces some main-chart fulfillment: an allowed output
  trajectory matching the system's generated outputs on `T`.

  Hot breach is the failure of this implication (a `Prop`, not a simulator).
-/
def Satisfies {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (chart : UniversalLSC IR OR) (s0 : S) (T : Set Time) : Prop :=
  T.Nonempty ∧
  T ⊆ chart.times ∧
  ∀ f ∈ chart.preInputs,
    ∀ h : ITZ IR, agreesOn h f chart.times →
      ∃ g, chart.allows f g ∧
        ∀ t ∈ T, generateOutputTrajectory Z s0 (liftInput h) t = some (g t)

/-- Satisfaction of a finite set of Universal LSCs (all charts). -/
def SatisfiesChartSet {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (charts : List (UniversalLSC IR OR)) (s0 : S) (T : Set Time) : Prop :=
  ∀ chart ∈ charts, Satisfies Z chart s0 T

/-- Quiet-output obligation at tick `t`: system readout is `none` (no alphabet idle). -/
def SilenceOutAt {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (s0 : S) (h : ITZ IR) (t : Time) : Prop :=
  generateOutputTrajectory Z s0 (liftInput h) t = none

/--
  Diagrammatic `silenceOut` corresponds to `Option.none` readout, not a token in `OR`.
-/
theorem silenceOut_iff_none {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (s0 : S) (h : ITZ IR) (t : Time) :
    SilenceOutAt Z s0 h t ↔
      generateOutputTrajectory Z s0 (liftInput h) t = none :=
  Iff.rfl

/-- Hot breach: pre-chart matched but no allowed output agrees with the system on `T`. -/
def HotBreach {S IR OR : Type} (Z : DiscreteSystem S IR OR)
    (chart : UniversalLSC IR OR) (s0 : S) (T : Set Time)
    (f : ITZ IR) (h : ITZ IR) : Prop :=
  f ∈ chart.preInputs ∧
  agreesOn h f chart.times ∧
  ¬ ∃ g, chart.allows f g ∧
    ∀ t ∈ T, generateOutputTrajectory Z s0 (liftInput h) t = some (g t)

theorem hotBreach_negates_satisfies {S IR OR : Type}
    (Z : DiscreteSystem S IR OR) (chart : UniversalLSC IR OR)
    (s0 : S) (T : Set Time) (f h : ITZ IR)
    (hSat : Satisfies Z chart s0 T) (hBreach : HotBreach Z chart s0 T f h) :
    False := by
  obtain ⟨_, _, hAll⟩ := hSat
  obtain ⟨hf, hAgr, hNo⟩ := hBreach
  exact hNo (hAll f hf h hAgr)

end LSC
