from pathlib import Path

bak = Path("/home/nicholas/uoa/sie699/Mbse/WymoreCouplingDynamic.lean.bak").read_text()
if not bak.rstrip().endswith("end Mbse.Wymore"):
    raise SystemExit("unexpected backup ending")
prefix = bak.rstrip()[:-len("end Mbse.Wymore")]

ext = Path("/home/nicholas/uoa/sie699/Mbse/_cfscr_body.lean")
ext.write_text("""open Classical

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
  couplingFunctionCiscrInputAt SCR hOut (fun _ => (fun ip => default)) x 0 ip hC

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
  Nat.rec x fun t prev => (rsy SCR hOut).NZ prev (some (cfscrInputAt SCR hOut f x t))

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
      couplingFunctionCiscrInputAt SCR hOut f x 0 ip hC := by
  dsimp [couplingFunctionCiscrInputAtZero, couplingFunctionCiscrInputAt]
  simp [generateStateTrajectory_zero]

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
      (rsy SCR hOut).NZ (cfscrBuild SCR hOut f x t) (some (cfscrInputAt SCR hOut f x t)) := rfl

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
    congr 1
    funext i
    simp only [rsy, rsy_NZ, rsyClosedLoopLiftInput, liftInput, Option.map_some]
    congr 1
    funext port
    dsimp [rsy_component_input_fun]
    by_cases hU : ⟨i, port⟩ ∈ UISCR SCR
    · simp [rsy_component_input_uiscr, cfscrInputAt_uiscr SCR hOut f x t ⟨i, port⟩ hU]
    · have hC : ⟨i, port⟩ ∈ CISCR SCR := by simpa [UISCR, Set.mem_compl_iff, CISCR] using hU
      simp [rsy_component_input_ciscr, cfscrInputAt_ciscr SCR hOut f x (t + 1) ⟨i, port⟩ hC,
        couplingFunctionCiscrInputAt, rsy_ciscr_port_val_at]

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
  dsimp [couplingFunctionCiscrInputAtSucc, couplingFunctionCiscrInputAt]
  rw [cfscrBuild_eq_closed_loop_state, hstate]

noncomputable def closedLoopUnconnPortTrajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (f : rsyClosedLoopITZW SCR) (ip : UnconnInPort SCR) : Time → Option (rsy_IS_map SCR ip) :=
  portTrajectory f ip

noncomputable def openLoopPortTrajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (g : rsyOpenLoopITZW SCR) (ip : openLoopInputPort SCR) : Time → Option (SCR.VSCR.PortVal ip.1 ip.2) :=
  portTrajectory g ip

noncomputable def openLoopFeederOutputTrajectory {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR) (g : rsyOpenLoopITZ SCR)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) :
    Time → Option (SCR.VSCR.OutPortVal (connectedOutput SCR ip hC).1 (connectedOutput SCR ip hC).2) :=
  let op := connectedOutput SCR ip hC
  portOutputTrajectory
    (generateOutputTrajectory (SCR.VSCR.Z op.1) (x op.1)
      (openLoopComponentInputTrajectory SCR op.1 g x)) op.2

/--
  [textbook/definition3.68/definition/coupling_function_scr]
  Relational specification of the coupling function on port trajectories.
-/
def CouplingFunctionSCR {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) : Prop :=
  (∀ (ip : openLoopInputPort SCR) (hU : ip ∈ UISCR SCR) (t : Time),
      openLoopPortTrajectory SCR (rsyOpenLoopLiftInput SCR g) ip t =
        closedLoopUnconnPortTrajectory SCR (rsyClosedLoopLiftInput SCR f) ⟨⟨ip.1, ip.2⟩, hU⟩ t) ∧
    (∀ (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) (t : Time),
      openLoopPortTrajectory SCR (rsyOpenLoopLiftInput SCR g) ip t =
        openLoopFeederOutputTrajectory SCR hOut x g ip hC t)

lemma couplingFunctionSCR_uiscr_port {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) (h : CouplingFunctionSCR SCR hOut f x g)
    (ip : openLoopInputPort SCR) (hU : ip ∈ UISCR SCR) (t : Time) :
    openLoopPortTrajectory SCR (rsyOpenLoopLiftInput SCR g) ip t =
      closedLoopUnconnPortTrajectory SCR (rsyClosedLoopLiftInput SCR f) ⟨⟨ip.1, ip.2⟩, hU⟩ t :=
  h.1 ip hU t

lemma couplingFunctionSCR_ciscr_port {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (f : rsyClosedLoopITZ SCR) (x : rsy_SZ SCR)
    (g : rsyOpenLoopITZ SCR) (h : CouplingFunctionSCR SCR hOut f x g)
    (ip : Σ (i : Fin n), SCR.VSCR.Port i) (hC : ip ∈ CISCR SCR) (t : Time) :
    openLoopPortTrajectory SCR (rsyOpenLoopLiftInput SCR g) ip t =
      openLoopFeederOutputTrajectory SCR hOut x g ip hC t :=
  h.2 ip hC t

""")

# continuation in part 2
print("wrote body part 1", len(ext.read_text()))
