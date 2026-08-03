import Mbse.Wymore

/-!
# Chapter 3 — coupling function (`CFSCR`) and dynamic resultant behavior

Closed-loop / open-loop trajectory infrastructure plus Wymore Ch. 3 Def. 3.68, Scholium 3.73,
and Thms 3.71–3.81.
-/

namespace Mbse.Wymore


/-! ## Step 0b: closed-loop / open-loop trajectory infrastructure -/

/--
  Textbook closed-loop system `Z@ = RSY(SCR)`.
-/
noncomputable abbrev rsyClosedLoopSystem {n : Nat} (p : RSYParam n) :=
  rsy_closed_loop_system p

/--
  Textbook open-loop system `Z& = CSY(VSCR)`.
-/
noncomputable abbrev rsyOpenLoopSystem {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)) :=
  rsy_open_loop_system SCR hOut

/--
  Open-loop input port type `IPZ&` (tagged union of component input ports).
-/
abbrev openLoopInputPort {n : Nat} (SCR : SystemCouplingRecipe n) :=
  Σ (i : Fin n), SCR.VSCR.Port i

/--
  Open-loop input space `IZ&`.
-/
abbrev rsyOpenLoopIZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  (ip : openLoopInputPort SCR) → SCR.VSCR.PortVal ip.1 ip.2

/--
  Closed-loop external input space `IZ@`.
-/
abbrev rsyClosedLoopIZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  rsy_IZ SCR

abbrev rsyClosedLoopSZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  rsy_SZ SCR

abbrev rsyClosedLoopOZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  rsy_OZ SCR

/-- Complete input trajectory `ITZ@`. -/
abbrev rsyClosedLoopITZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  ITZ (rsyClosedLoopIZ SCR)

/-- Complete input trajectory `ITZ&`. -/
abbrev rsyOpenLoopITZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  ITZ (rsyOpenLoopIZ SCR)

/-- Generalized closed-loop input trajectory (`ITZW` over external inputs). -/
abbrev rsyClosedLoopITZW {n : Nat} (SCR : SystemCouplingRecipe n) :=
  ITZW (rsyClosedLoopIZ SCR)

/-- Lift total closed-loop input to generalized trajectory. -/
abbrev rsyClosedLoopLiftInput {n : Nat} (SCR : SystemCouplingRecipe n)
    (f : rsyClosedLoopITZ SCR) : rsyClosedLoopITZW SCR :=
  liftInput f

/-- Experiment triple `EXZ@`. -/
def rsyClosedLoopEXZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  EXZ (rsyClosedLoopSZ SCR) (rsyClosedLoopIZ SCR)

/-- Experiment triple `EXZ&` (open-loop state is shared product `SZ&`). -/
def rsyOpenLoopEXZ {n : Nat} (SCR : SystemCouplingRecipe n) :=
  EXZ (rsy_SZ SCR) (rsyOpenLoopIZ SCR)

/--
  Textbook `IP&(VSCR, Z&)`: embed component input port into open-loop tagged union.
-/
def openLoopIP_map {n : Nat} (SCR : SystemCouplingRecipe n) :
    openLoopInputPort SCR → openLoopInputPort SCR :=
  csy_IP_map SCR.VSCR

/--
  Textbook `INIP&(VSCR, Z&)`: inverse of `IP&` on open-loop ports.
-/
def openLoopINIP_map {n : Nat} (SCR : SystemCouplingRecipe n) :
    openLoopInputPort SCR → openLoopInputPort SCR :=
  csy_INIP_map SCR.VSCR

lemma openLoopIP_map_apply {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : openLoopInputPort SCR) : openLoopIP_map SCR ip = ip := rfl

lemma openLoopINIP_map_apply {n : Nat} (SCR : SystemCouplingRecipe n)
    (ip : openLoopInputPort SCR) : openLoopINIP_map SCR ip = ip := rfl

/-- Component `i` input trajectory induced by closed-loop run `(f, x)`. -/
noncomputable def rsy_component_input_trajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n)
    (f : rsyClosedLoopITZ SCR) (x : rsyClosedLoopSZ SCR) : ITZW ((p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p) :=
  fun τ => some (rsy_component_input_fun SCR hOut i (f τ)
    (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) τ))

/--
  Resolved component input at time `t` for closed-loop trajectory `(f, x)`.
-/
noncomputable def rsy_component_input_at {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n)
    (f : rsyClosedLoopITZ SCR) (x : rsyClosedLoopSZ SCR) (t : Time) :
    (p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p :=
  rsy_component_input_fun SCR hOut i (f t)
    (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t)

lemma rsy_component_input_at_eq_trajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n)
    (f : rsyClosedLoopITZ SCR) (x : rsyClosedLoopSZ SCR) (t : Time)
    (port : SCR.VSCR.Port i) :
    rsy_component_input_at SCR hOut i f x t port =
      (rsy_component_input_trajectory SCR hOut i f x t).get rfl port := by
  dsimp [rsy_component_input_at, rsy_component_input_trajectory, rsyClosedLoopLiftInput, liftInput]

theorem rsy_state_trajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsyClosedLoopSZ SCR)
    (f : rsyClosedLoopITZ SCR) (t : Time) (i : Fin n) :
    (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t i) =
      generateStateTrajectory (SCR.VSCR.Z i) (x i)
        (rsy_component_input_trajectory SCR hOut i f x) t := by
  induction t generalizing i with
  | zero => simp [generateStateTrajectory_zero]
  | succ t ih =>
    rw [generateStateTrajectory_succ]
    simp only [rsy, rsy_NZ, rsyClosedLoopLiftInput, liftInput]
    exact congr_arg (fun s =>
      (SCR.VSCR.Z i).NZ s (some (rsy_component_input_fun SCR hOut i (f t)
        (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t)))) (ih i)

theorem rsyOutAt_eq_component_output_trajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsyClosedLoopSZ SCR)
    (f : rsyClosedLoopITZ SCR) (t : Time) (i : Fin n) (B' : SCR.VSCR.OutPort i) :
    rsyOutAt SCR hOut (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t) ⟨i, B'⟩ =
      Classical.choose (hOut i (generateStateTrajectory (SCR.VSCR.Z i) (x i)
        (rsy_component_input_trajectory SCR hOut i f x) t)) B' := by
  have hst := rsy_state_trajectory SCR hOut x f t i
  let s := generateStateTrajectory (SCR.VSCR.Z i) (x i)
    (rsy_component_input_trajectory SCR hOut i f x) t
  obtain ⟨o, ho⟩ := hOut i s
  have hchoose : Classical.choose (hOut i s) B' = o B' :=
    congrArg (fun g => g B') (Trajectory.choose_alwaysOutputs (SCR.VSCR.Z i) (hOut i) s ho)
  have hchoose_at :
      Classical.choose (hOut i (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t i)) B' =
        Classical.choose (hOut i s) B' :=
    congrArg (fun st => Classical.choose (hOut i st) B') hst
  dsimp [rsyOutAt, csyOut]
  rw [hchoose_at, hchoose]

theorem rsy_output_trajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsyClosedLoopSZ SCR)
    (f : rsyClosedLoopITZ SCR) (t : Time) (i : Fin n) (B' : SCR.VSCR.OutPort i)
    (hU : ⟨i, B'⟩ ∈ UOSCR SCR) :
    (generateOutputTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t).map (fun r => r ⟨⟨i, B'⟩, hU⟩) =
      (generateOutputTrajectory (SCR.VSCR.Z i) (x i)
        (rsy_component_input_trajectory SCR hOut i f x) t).map (fun r => r B') := by
  have hout := rsyOutAt_eq_component_output_trajectory SCR hOut x f t i B'
  let s := generateStateTrajectory (SCR.VSCR.Z i) (x i)
    (rsy_component_input_trajectory SCR hOut i f x) t
  obtain ⟨o, ho⟩ := hOut i s
  have hchoose : Classical.choose (hOut i s) B' = o B' :=
    congrArg (fun g => g B') (Trajectory.choose_alwaysOutputs (SCR.VSCR.Z i) (hOut i) s ho)
  have hfinal : rsyOutAt SCR hOut (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t) ⟨i, B'⟩ = o B' :=
    hout.trans hchoose
  dsimp [rsy] at hfinal
  simp only [generateOutputTrajectory, rsy, rsy_RZ, Option.map_some, ho, Subtype.coe_mk, s]
  rw [hfinal]

theorem rsy_closed_loop_state_trajectory {n : Nat} (p : RSYParam n)
    (x : rsyClosedLoopSZ p.SCR) (f : rsyClosedLoopITZ p.SCR) (t : Time) :
    generateStateTrajectory (rsyClosedLoopSystem p) x (rsyClosedLoopLiftInput p.SCR f) t =
      generateStateTrajectory (rsy p.SCR p.hOut) x (rsyClosedLoopLiftInput p.SCR f) t := rfl

/-- Any closed-loop experiment triple lies in `EXZ@`. -/
def rsyClosedLoopExperiment {n : Nat} (SCR : SystemCouplingRecipe n)
    (f : ITZW (rsyClosedLoopIZ SCR)) (x : rsyClosedLoopSZ SCR) (t : Time) :
    rsyClosedLoopEXZ SCR :=
  (f, x, t)

/-- Lift total open-loop input to generalized trajectory. -/
abbrev rsyOpenLoopLiftInput {n : Nat} (SCR : SystemCouplingRecipe n)
    (g : rsyOpenLoopITZ SCR) : ITZW (rsyOpenLoopIZ SCR) :=
  liftInput g

/-- Any open-loop experiment triple lies in `EXZ&`. -/
def rsyOpenLoopExperiment {n : Nat} (SCR : SystemCouplingRecipe n)
    (g : ITZW (rsyOpenLoopIZ SCR)) (x : rsyClosedLoopSZ SCR) (t : Time) :
    rsyOpenLoopEXZ SCR :=
  (g, x, t)


open Classical

/-! ## Definition 3.68: coupling function `CFSCR` -/

noncomputable def openLoopComponentInputAt {n : Nat} (SCR : SystemCouplingRecipe n)
    (i : Fin n) (g : rsyOpenLoopITZ SCR) (_x : rsyClosedLoopSZ SCR) (t : Time) :
    (p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p :=
  fun port => g t ⟨i, port⟩

noncomputable def openLoopComponentInputTrajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (i : Fin n) (g : rsyOpenLoopITZ SCR) (x : rsyClosedLoopSZ SCR) :
    ITZW ((p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p) :=
  fun τ => some (openLoopComponentInputAt SCR i g x τ)

noncomputable def rsy_ciscr_port_val_at {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (st : rsy_SZ SCR)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    SCR.VSCR.PortVal ip.1 ip.2 :=
  let op := connectedOutput SCR ip hC
  have hop := connectedOutput_spec SCR ip hC
  have hcomp := SCR.connectivity.2.2.2 op ip hop
  hcomp ▸ rsyOutAt SCR hOut st op

noncomputable def couplingFunctionCiscrInputAt {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (τ : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    SCR.VSCR.PortVal ip.1 ip.2 :=
  rsy_ciscr_port_val_at SCR hOut
    (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) τ) ip hC

/-- Scholium 3.73 (a): connected input at time zero from initial readout. -/
noncomputable def couplingFunctionCiscrInputAtZero {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    SCR.VSCR.PortVal ip.1 ip.2 :=
  rsy_ciscr_port_val_at SCR hOut x ip hC

/-- Scholium 3.73 (b): connected input at `t+1` from readout after transition. -/
noncomputable def couplingFunctionCiscrInputAtSucc {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    SCR.VSCR.PortVal ip.1 ip.2 :=
  couplingFunctionCiscrInputAt SCR hOut f x (t + 1) ip hC

/-- Constructive open-loop input vector at time `t` (Scholium 3.73). -/
noncomputable def cfscrInputAt {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) (t : Time) : rsyOpenLoopIZ SCR :=
  fun ip =>
    if hU : ip ∈ UISCR SCR then
      f t ⟨⟨ip.1, ip.2⟩, hU⟩
    else
      have hC : ip ∈ CISCR SCR := by simpa [UISCR, CISCR, Set.mem_compl_iff] using hU
      couplingFunctionCiscrInputAt SCR hOut f x t ip hC

/-- State built from `CFSCR` inputs (matches closed-loop state trajectory). -/
noncomputable def cfscrBuild {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) : Time → rsy_SZ SCR :=
  Nat.rec x fun t prev => (rsy SCR hOut).NZ prev (some (f t))

/--
  [textbook/definition3.68/definition/coupling_function]
  Coupling function `CFSCR`: open-loop input trajectory from closed-loop run `(f, x)`.
-/
noncomputable def cfscr {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) : rsyOpenLoopITZ SCR :=
  fun t => cfscrInputAt SCR hOut f x t

lemma couplingFunctionCiscrInputAtZero_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    couplingFunctionCiscrInputAtZero SCR hOut x ip hC =
      couplingFunctionCiscrInputAt SCR hOut f x 0 ip hC :=
  rfl

lemma couplingFunctionCiscrInputAtSucc_eq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    couplingFunctionCiscrInputAtSucc SCR hOut f x t ip hC =
      couplingFunctionCiscrInputAt SCR hOut f x (t + 1) ip hC := rfl

lemma cfscrInputAt_uiscr {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hU : ip ∈ UISCR SCR) :
    cfscrInputAt SCR hOut f x t ip = f t ⟨⟨ip.1, ip.2⟩, hU⟩ := by
  dsimp [cfscrInputAt]
  simp [hU]

lemma cfscrInputAt_ciscr {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (τ : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    cfscrInputAt SCR hOut f x τ ip = couplingFunctionCiscrInputAt SCR hOut f x τ ip hC := by
  dsimp [cfscrInputAt]
  have hU : ip ∉ UISCR SCR := by simpa [UISCR, CISCR] using hC
  simp [hU]

lemma cfscrBuild_zero {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) :
    cfscrBuild SCR hOut f x 0 = x := rfl

lemma cfscrBuild_succ {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    cfscrBuild SCR hOut f x (t + 1) =
      (rsy SCR hOut).NZ (cfscrBuild SCR hOut f x t) (some (f t)) := rfl

lemma cfscrBuild_eq_closed_loop_state {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    cfscrBuild SCR hOut f x t =
      generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t := by
  induction t with
  | zero => simp [cfscrBuild, generateStateTrajectory_zero]
  | succ t ih =>
    rw [cfscrBuild_succ, generateStateTrajectory_succ, ih]


lemma rsy_component_input_at_ciscr_state {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (st : rsy_SZ SCR) (port : SCR.VSCR.Port i) (hC : ⟨i, port⟩ ∈ CISCR SCR) :
    rsy_component_input_fun SCR hOut i extIn st port =
      rsy_ciscr_port_val_at SCR hOut st ⟨i, port⟩ hC := by
  dsimp [rsy_ciscr_port_val_at]
  exact rsy_component_input_ciscr SCR hOut i extIn st port hC

lemma couplingFunctionCiscrInputAt_eq_rsy_component_input_at {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (τ : Time) (i : Fin n) (port : SCR.VSCR.Port i) (hC : ⟨i, port⟩ ∈ CISCR SCR) :
    couplingFunctionCiscrInputAt SCR hOut f x τ ⟨i, port⟩ hC =
      rsy_component_input_at SCR hOut i f x τ port := by
  dsimp [couplingFunctionCiscrInputAt, rsy_component_input_at]
  rw [rsy_component_input_at_ciscr_state SCR hOut i (f τ)
    (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) τ) port hC]

lemma cfscr_input_eq_rsy_component_input_at {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (τ : Time) (i : Fin n) (port : SCR.VSCR.Port i) :
    (cfscr SCR hOut f x τ) ⟨i, port⟩ = rsy_component_input_at SCR hOut i f x τ port := by
  by_cases hU : ⟨i, port⟩ ∈ UISCR SCR
  · simp [cfscr, cfscrInputAt, hU, rsy_component_input_at, rsy_component_input_uiscr]
  · have hC : ⟨i, port⟩ ∈ CISCR SCR := by simpa [UISCR, Set.mem_compl_iff, CISCR] using hU
    simp [cfscr, cfscrInputAt, hU, rsy_component_input_at,
      couplingFunctionCiscrInputAt_eq_rsy_component_input_at SCR hOut f x τ i port hC]

lemma couplingFunctionCiscrInputAtSucc_eq_rsyOutAt {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) (t : Time)
    (hstate :
      generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) (t + 1) =
        generateStateTrajectory (rsy_open_loop_system SCR hOut) x (rsyOpenLoopLiftInput SCR g) (t + 1))
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    couplingFunctionCiscrInputAtSucc SCR hOut f x t ip hC =
      rsy_ciscr_port_val_at SCR hOut
        (generateStateTrajectory (rsy_open_loop_system SCR hOut) x (rsyOpenLoopLiftInput SCR g) (t + 1)) ip hC := by
  exact congrArg (fun st => rsy_ciscr_port_val_at SCR hOut st ip hC) hstate

/--
  [textbook/definition3.68/definition/coupling_function_scr]
  Relational coupling-function specification `CouplingFunctionSCR`.
-/
def CouplingFunctionSCR {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) : Prop :=
  (∀ (t : Time) (ip : openLoopInputPort SCR) (hU : ip ∈ UISCR SCR),
      g t ip = f t ⟨⟨ip.1, ip.2⟩, hU⟩) ∧
  (∀ (t : Time) (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR),
      g t ip = couplingFunctionCiscrInputAt SCR hOut f x t ip hC)

lemma CouplingFunctionSCR_uiscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) (h : CouplingFunctionSCR SCR hOut f x g) (t : Time)
    (ip : openLoopInputPort SCR) (hU : ip ∈ UISCR SCR) :
    g t ip = f t ⟨⟨ip.1, ip.2⟩, hU⟩ :=
  h.1 t ip hU

lemma CouplingFunctionSCR_ciscr {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) (h : CouplingFunctionSCR SCR hOut f x g) (t : Time)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    g t ip = couplingFunctionCiscrInputAt SCR hOut f x t ip hC :=
  h.2 t ip hC

/--
  [textbook/scholium3.73/theorem/characterization]
  The constructive `cfscr` satisfies Definition 3.68.
-/
theorem scholium_3_73_characterization {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) :
    CouplingFunctionSCR SCR hOut f x (cfscr SCR hOut f x) := by
  constructor
  · intro t ip hU
    dsimp [cfscr, cfscrInputAt]
    simp [hU]
  · intro t ip hC
    dsimp [cfscr, cfscrInputAt]
    have hU : ip ∉ UISCR SCR := by simpa [UISCR, CISCR] using hC
    simp [hU]

lemma couplingFunctionSCR_input_eq_at {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    {g₁ g₂ : rsyOpenLoopITZ SCR} (h₁ : CouplingFunctionSCR SCR hOut f x g₁)
    (h₂ : CouplingFunctionSCR SCR hOut f x g₂) (t : Time) (ip : openLoopInputPort SCR) :
    g₁ t ip = g₂ t ip := by
  by_cases hU : ip ∈ UISCR SCR
  · rw [CouplingFunctionSCR_uiscr SCR hOut f x g₁ h₁ t ip hU,
      CouplingFunctionSCR_uiscr SCR hOut f x g₂ h₂ t ip hU]
  · have hC : ip ∈ CISCR SCR := by simpa [UISCR, CISCR, Set.mem_compl_iff] using hU
    rw [CouplingFunctionSCR_ciscr SCR hOut f x g₁ h₁ t ip hC,
      CouplingFunctionSCR_ciscr SCR hOut f x g₂ h₂ t ip hC]

/--
  [textbook/scholium3.73/theorem/uniqueness]
  The coupling-function equations determine `g` uniquely.
-/
theorem scholium_3_73_uniqueness {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    {g : rsyOpenLoopITZ SCR} (h : CouplingFunctionSCR SCR hOut f x g) :
    g = cfscr SCR hOut f x := by
  funext t ip
  exact couplingFunctionSCR_input_eq_at SCR hOut f x h (scholium_3_73_characterization SCR hOut f x) t ip


noncomputable def couplingFunctionMap {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    rsyClosedLoopITZ SCR × rsy_SZ SCR → rsyOpenLoopITZ SCR :=
  fun ⟨f, x⟩ => cfscr SCR hOut f x

/--
  [textbook/theorem3.71/theorem/coupling_function_exists]
  A coupling function exists for every closed-loop experiment.
-/
theorem coupling_function_exists {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) :
    CouplingFunctionSCR SCR hOut f x (cfscr SCR hOut f x) :=
  scholium_3_73_characterization SCR hOut f x

/--
  [textbook/theorem3.71/theorem/coupling_function_in_FNS]
  The coupling function is a total single-valued map on `ITZ@ × SZ@`.
-/
theorem coupling_function_in_FNS {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) :
    SatisfiesFNS (couplingFunctionMap SCR hOut) :=
  satisfiesFNS_of_function _

lemma cfscrInputAt_translate {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (r t : Time) (ip : openLoopInputPort SCR) :
    cfscrInputAt SCR hOut (translate f r)
      (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) r) t ip =
      cfscrInputAt SCR hOut f x (r + t) ip := by
  dsimp [cfscrInputAt, translate, couplingFunctionCiscrInputAt]
  by_cases hU : ip ∈ UISCR SCR
  · simp [hU, Nat.add_comm]
  · have hC : ip ∈ CISCR SCR := by simpa [UISCR, CISCR, Set.mem_compl_iff] using hU
    simp [hU, rsy_ciscr_port_val_at]
    rw [← stateTrajectory_time_invariance (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) r t]
    rfl

/--
  [textbook/theorem3.75/theorem/cfscr_translate]
  Translation commutes with the coupling function.
-/
theorem cfscr_translate {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (r : Time) (t : Time) (ip : openLoopInputPort SCR) :
    (cfscr SCR hOut (translate f r)
        (generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) r) t ip) =
      cfscr SCR hOut f x (r + t) ip :=
  cfscrInputAt_translate SCR hOut f x r t ip

lemma cfscr_open_loop_state_eq_build {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    generateStateTrajectory (rsy_open_loop_system SCR hOut) x
        (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t =
      cfscrBuild SCR hOut f x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [generateStateTrajectory_succ, cfscrBuild_succ, ih, rsy_open_loop_is_csy SCR hOut]
    funext i
    simp only [csy, rsyOpenLoopLiftInput, liftInput, Option.map_some, cfscr]
    refine congr_arg (fun opt => (SCR.VSCR.Z i).NZ (cfscrBuild SCR hOut f x t i) opt) (congrArg some ?_)
    funext port
    dsimp [rsy_component_input_fun, rsy_component_input_at]
    by_cases hU : ⟨i, port⟩ ∈ UISCR SCR
    · simp [cfscrInputAt, hU]
    · have hC : ⟨i, port⟩ ∈ CISCR SCR := by simpa [UISCR, CISCR, Set.mem_compl_iff] using hU
      simp [cfscrInputAt, hU, couplingFunctionCiscrInputAt]
      congr 1
      exact (cfscrBuild_eq_closed_loop_state SCR hOut f x t).symm

theorem cfscr_open_loop_state_eq_closed_loop {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    generateStateTrajectory (rsy_open_loop_system SCR hOut) x
        (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t =
      generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t := by
  rw [cfscr_open_loop_state_eq_build, cfscrBuild_eq_closed_loop_state]

/--
  [textbook/lemma3.76/lemma/coupling_function_projection]
  Projection identities for `cfscr` on component inputs and trajectories.
-/
theorem coupling_function_projection_lemma {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (i : Fin n) (t : Time) (port : SCR.VSCR.Port i) :
    (openLoopComponentInputAt SCR i (cfscr SCR hOut f x) x t port =
        rsy_component_input_at SCR hOut i f x t port) ∧
    ((generateStateTrajectory (rsy_open_loop_system SCR hOut) x
          (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t i) =
        generateStateTrajectory (SCR.VSCR.Z i) (x i)
          (rsy_component_input_trajectory SCR hOut i f x) t) ∧
    (generateStateTrajectory (rsy_open_loop_system SCR hOut) x
        (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t =
      generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t) := by
  exact ⟨cfscr_input_eq_rsy_component_input_at SCR hOut f x t i port,
    by dsimp [rsy_open_loop_system]; exact csy_state_trajectory SCR.VSCR hOut x (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t i,
    cfscr_open_loop_state_eq_closed_loop SCR hOut f x t⟩

theorem cfscr_open_loop_state_eq_closed_loop_csy {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    generateStateTrajectory (rsy_open_loop_system SCR hOut) x
        (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t =
      cfscrBuild SCR hOut f x t :=
  cfscr_open_loop_state_eq_build SCR hOut f x t

theorem cfscr_open_loop_output_eq_closed_loop {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) (i : Fin n) (B' : SCR.VSCR.OutPort i) (hU : ⟨i, B'⟩ ∈ UOSCR SCR) :
    (generateOutputTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t).map (fun r => r ⟨⟨i, B'⟩, hU⟩) =
      (generateOutputTrajectory (rsy_open_loop_system SCR hOut) x
          (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t).map (fun r => r ⟨i, B'⟩) := by
  dsimp [rsy_open_loop_system, rsyOpenLoopLiftInput, liftInput]
  exact (rsy_output_trajectory SCR hOut x f t i B' hU).trans
    (csy_output_trajectory SCR.VSCR hOut x (liftInput (cfscr SCR hOut f x)) t i B').symm

/--
  [textbook/theorem3.78/theorem/second_open_loop_closed_loop]
  Open-loop and closed-loop trajectories coincide under `cfscr`.
-/
theorem second_open_loop_closed_loop_theorem {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) :
    (generateStateTrajectory (rsy_open_loop_system SCR hOut) x
          (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t =
        generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t ∧
      ∀ (i : Fin n) (B' : SCR.VSCR.OutPort i) (hU : ⟨i, B'⟩ ∈ UOSCR SCR),
        (generateOutputTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t).map
            (fun r => r ⟨⟨i, B'⟩, hU⟩) =
          (generateOutputTrajectory (rsy_open_loop_system SCR hOut) x
              (rsyOpenLoopLiftInput SCR (cfscr SCR hOut f x)) t).map (fun r => r ⟨i, B'⟩)) := by
  refine ⟨cfscr_open_loop_state_eq_closed_loop SCR hOut f x t, ?_⟩
  intro i B' hU
  exact cfscr_open_loop_output_eq_closed_loop SCR hOut f x t i B' hU

/--
  [textbook/theorem3.80/theorem/resultant_behavior_from_open_loop]
  Closed-loop resultant behavior arises from a suitable open-loop run.
-/
theorem resultant_behavior_from_open_loop {n : Nat} (SCR : SystemCouplingRecipe n)
    [∀ i p, Inhabited (SCR.VSCR.PortVal i p)]
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR) :
    ∃ g : rsyOpenLoopITZ SCR,
      CouplingFunctionSCR SCR hOut f x g ∧
      (∀ t, generateStateTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t =
        generateStateTrajectory (rsy_open_loop_system SCR hOut) x (rsyOpenLoopLiftInput SCR g) t) := by
  refine ⟨cfscr SCR hOut f x, coupling_function_exists SCR hOut f x, ?_⟩
  intro t
  exact Eq.symm (cfscr_open_loop_state_eq_closed_loop SCR hOut f x t)

/--
  [textbook/theorem3.81/theorem/resultant_output_component_decomposition]
  Closed-loop output port trajectories factor through component systems.
-/
theorem resultant_output_component_decomposition {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (t : Time) (i : Fin n) (B' : SCR.VSCR.OutPort i) (hU : ⟨i, B'⟩ ∈ UOSCR SCR) :
    (generateOutputTrajectory (rsy SCR hOut) x (rsyClosedLoopLiftInput SCR f) t).map (fun r => r ⟨⟨i, B'⟩, hU⟩) =
      (generateOutputTrajectory (SCR.VSCR.Z i) (x i)
          (rsy_component_input_trajectory SCR hOut i f x) t).map (fun r => r B') :=
  rsy_output_trajectory SCR hOut x f t i B' hU

end Mbse.Wymore
