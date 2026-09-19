import Mbse.WymoreSystemModes
import Mbse.WymoreImplementation
import Mbse.CouplingIsomorphism

/-!
# Wymore Chapter 5: coupling system modes

The component systems in an induced recipe may have different state and port-value
types, but they retain the original port indices and connectivity.  This is the
typed reading of “without constriction.”  Theorems 5.134, 5.136, and 5.138 derive
the resultant mode equations from those component hypotheses by the coupling
function `cfscr` and Lemma 3.77 (`rsy_state_trajectory`).
-/

namespace WymoreModeCoupling

open WymoreSystemModes WymoreImplementation
open Homomorphism Mbse.Wymore

universe u

/-! ## Definition 5.114: induced system-mode recipes -/

/--
  [textbook/definition5.114/source/definition]
  [textbook/definition5.114/lean/inducedSystemModeRecipe]
  Explicit data for an induced recipe.  Port indices and connectivity are shared
  literally with `SCR`; the two `PreservesPorts` witnesses give the corresponding
  surjective port maps, while each `SystemMode` supplies injective whole-input and
  whole-output maps.  `matched` is the compatibility required at internally
  connected ports.
-/
structure InducedSystemModeRecipe {n : Nat} (SCR : SystemCouplingRecipe n) where
  ModeState : Fin n → Type
  ModePortVal : (i : Fin n) → SCR.VSCR.Port i → Type
  ModeOutPortVal : (i : Fin n) → SCR.VSCR.OutPort i → Type
  modeSystem : (i : Fin n) → DiscreteSystem (ModeState i)
    ((p : SCR.VSCR.Port i) → ModePortVal i p)
    ((q : SCR.VSCR.OutPort i) → ModeOutPortVal i q)
  distinct : ∀ i j, i ≠ j → ¬ HEq (modeSystem i) (modeSystem j)
  componentMode : (i : Fin n) → SystemMode (modeSystem i) (SCR.VSCR.Z i)
  inputPorts : (i : Fin n) →
    PreservesPorts (Equiv.refl (SCR.VSCR.Port i)) (componentMode i).inputMap
  outputPorts : (i : Fin n) →
    PreservesPorts (Equiv.refl (SCR.VSCR.OutPort i)) (componentMode i).outputMap
  inducedCompatibility :
    ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR →
        ModeOutPortVal op.1 op.2 = ModePortVal ip.1 ip.2
  matched :
    ∀ (op : Σ i, SCR.VSCR.OutPort i) (ip : Σ i, SCR.VSCR.Port i),
      (op, ip) ∈ SCR.CSCR →
        HEq ((outputPorts op.1).port op.2) ((inputPorts ip.1).port ip.2)

/-- The vector obtained by replacing every component by its named mode system. -/
def inducedModeVector {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : PortSystemVector n where
  SZ := D.ModeState
  Port := SCR.VSCR.Port
  PortVal := D.ModePortVal
  OutPort := SCR.VSCR.OutPort
  OutPortVal := D.ModeOutPortVal
  Z := D.modeSystem
  distinct := D.distinct

/--
  [textbook/definition5.114/lean/sysmoscr]
  `SYSMOSCR`: same port skeleton and same connection relation, with the component
  systems replaced by the supplied non-constricting modes.
-/
def sysmoscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : SystemCouplingRecipe n where
  VSCR := inducedModeVector D
  CSCR := SCR.CSCR
  connectivity :=
    ⟨SCR.connectivity.1, SCR.connectivity.2.1, SCR.connectivity.2.2.1,
      D.inducedCompatibility⟩

@[simp] theorem sysmoscr_cscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : (sysmoscr D).CSCR = SCR.CSCR := rfl

theorem sysmoscr_uiscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : UISCR (sysmoscr D) = UISCR SCR := rfl

theorem sysmoscr_uoscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : UOSCR (sysmoscr D) = UOSCR SCR := rfl

/-- Canonical componentwise state embedding of the induced resultant. -/
def resultantStateMap {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) :
    rsy_SZ (sysmoscr D) → rsy_SZ SCR :=
  fun y i => (D.componentMode i).stateMap (y i)

/-- Canonical external-input embedding, acting through corresponding ports. -/
def resultantInputMap {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) :
    rsy_IZ (sysmoscr D) → rsy_IZ SCR :=
  fun e ip => (D.inputPorts ip.val.1).port ip.val.2 (e ip)

/-- Canonical external-output embedding, acting through corresponding ports. -/
def resultantOutputMap {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) :
    rsy_OZ (sysmoscr D) → rsy_OZ SCR :=
  fun o op => (D.outputPorts op.val.1).port op.val.2 (o op)

theorem resultantStateMap_injective {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : Function.Injective (resultantStateMap D) := by
  intro x y h
  funext i
  exact (D.componentMode i).stateMap_injective (congrFun h i)

/--
Whole-resultant non-constriction.  It is stated explicitly because injectivity
of a product map does not, without inhabitedness assumptions on all other
factors, follow from injectivity of each component system's whole-input map.
-/
structure ResultantPortCorrespondence {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : Prop where
  input_injective : Function.Injective (resultantInputMap D)
  output_injective : Function.Injective (resultantOutputMap D)

/-! ## Definition 5.117: hologenicity -/

/--
Explicit witness that the induced resultant is a mode of the original
resultant.  The behavior is retained as data because it is not determined by
the component SMBFs in the presence of feedback.
-/
structure ResultantModeCompatibility {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i)) where
  ports : ResultantPortCorrespondence D
  behavior : BehaviorWitness (rsy_SZ (sysmoscr D)) (rsy_IZ (sysmoscr D)) (rsy_IZ SCR)
  behavior_initial : ∀ y e, behavior.input y e 0 = resultantInputMap D e
  transition : ∀ y e,
    resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) =
      generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (behavior.input y e)) (behavior.duration y e)
  readout : ∀ y,
    ((rsy (sysmoscr D) hModeOut).RZ y).map (resultantOutputMap D) =
      (rsy SCR hOut).RZ (resultantStateMap D y)

def ResultantModeCompatibility.mode {n : Nat} {SCR : SystemCouplingRecipe n}
    {D : InducedSystemModeRecipe SCR}
    {hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)}
    {hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i)}
    (C : ResultantModeCompatibility D hOut hModeOut) :
    SystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut) where
  stateMap := resultantStateMap D
  inputMap := resultantInputMap D
  outputMap := resultantOutputMap D
  stateMap_injective := resultantStateMap_injective D
  inputMap_injective := C.ports.input_injective
  outputMap_injective := C.ports.output_injective
  behavior := C.behavior
  behavior_initial := C.behavior_initial
  transition := C.transition
  readout := C.readout

/--
  [textbook/definition5.117/source/definition]
  [textbook/definition5.117/lean/CouplingRecipe.IsSystemModeHologenic]
  Hologenicity with all component, port-correspondence, and resultant SMBF
  witnesses named.
-/
def IsSystemModeHologenic {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i)) : Prop :=
  Nonempty (ResultantModeCompatibility D hOut hModeOut)

theorem ResultantModeCompatibility.isSystemMode {n : Nat} {SCR : SystemCouplingRecipe n}
    {D : InducedSystemModeRecipe SCR}
    {hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i)}
    {hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i)}
    (C : ResultantModeCompatibility D hOut hModeOut) :
    IsSystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut) :=
  ⟨C.mode⟩

theorem sysmoscr_component {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (i : Fin n) :
    (sysmoscr D).VSCR.Z i = D.modeSystem i := by
  rfl

/-- Projection of the mode resultant step through `resultantStateMap`. -/
@[simp, wymore] theorem resultantStateMap_NZ {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (y : rsy_SZ (sysmoscr D)) (e : rsy_IZ (sysmoscr D)) (i : Fin n) :
    resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) i =
      (D.componentMode i).stateMap
        ((D.modeSystem i).NZ (y i)
          (some (rsy_component_input_fun (sysmoscr D) hModeOut i e y))) := by
  simp [resultantStateMap, rsy, rsy_NZ, sysmoscr_component]
  rfl

/-! ## Portwise injectivity of a non-constricting inclusion -/

/--
A portwise injective product map has injective factors once every factor is
nonempty, which is how a subset of a product restricts to each port.
-/
theorem preservesPorts_factor_injective
    {Port : Type} {V₁ V₂ : Port → Type}
    {H : ((p : Port) → V₂ p) → ((p : Port) → V₁ p)}
    (hp : PreservesPorts (Equiv.refl Port) H) (hH : Function.Injective H)
    [∀ p, Nonempty (V₂ p)] (p : Port) : Function.Injective (hp.port p) := by
  intro a b hab
  haveI : DecidableEq Port := Classical.typeDecidableEq Port
  classical
  let f : (q : Port) → V₂ q := fun q =>
    if h : q = p then h ▸ a else Classical.choice (inferInstance : Nonempty (V₂ q))
  let g : (q : Port) → V₂ q := fun q =>
    if h : q = p then h ▸ b else Classical.choice (inferInstance : Nonempty (V₂ q))
  have hfg : H f = H g := by
    funext q
    have hf := hp.proj f q
    have hg := hp.proj g q
    simp only [Equiv.refl_apply] at hf hg
    rw [hf, hg]
    by_cases hq : q = p
    · subst hq
      simpa [f, g] using hab
    · simp [f, g, hq]
  have hfeq := congrFun (hH hfg) p
  simpa [f, g] using hfeq

theorem resultantInputMap_injective {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) [∀ i p, Nonempty (D.ModePortVal i p)] :
    Function.Injective (resultantInputMap D) := by
  intro e₁ e₂ h
  funext ip
  exact preservesPorts_factor_injective (D.inputPorts ip.val.1)
    (D.componentMode ip.val.1).inputMap_injective ip.val.2 (congrFun h ip)

theorem resultantOutputMap_injective {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    Function.Injective (resultantOutputMap D) := by
  intro o₁ o₂ h
  funext op
  exact preservesPorts_factor_injective (D.outputPorts op.val.1)
    (D.componentMode op.val.1).outputMap_injective op.val.2 (congrFun h op)

def resultantPorts {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    ResultantPortCorrespondence D where
  input_injective := resultantInputMap_injective D
  output_injective := resultantOutputMap_injective D

/-! ## Resolved component inputs -/

/--
Readout of a mode component, transported portwise, is the readout of its image
state.  This is the system-mode form of `elab_readout`.
-/
theorem mode_readout {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (y : rsy_SZ (sysmoscr D)) (op : Σ i, SCR.VSCR.OutPort i) :
    (D.outputPorts op.1).port op.2 (rsyOutAt (sysmoscr D) hModeOut y op) =
      rsyOutAt SCR hOut (resultantStateMap D y) op := by
  obtain ⟨i, q⟩ := op
  simpa [rsyOutAt_eq_componentReadoutAt, resultantStateMap, sysmoscr_component] using
    alwaysOutputs_port_readout (SCR.VSCR.Z i) (D.modeSystem i)
      (D.componentMode i).stateMap (D.componentMode i).outputMap
      (D.outputPorts i) (hOut i) (hModeOut i) (D.componentMode i).readout (y i) q

/--
At the initial state, the exhibitor coupling resolves each component input to
the image of the mode coupling's resolved input.  Unconnected ports copy the
external value; connected ports copy the source readout.
-/
theorem mode_component_input {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (i : Fin n) (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D)) :
    (D.componentMode i).inputMap
        (rsy_component_input_fun (sysmoscr D) hModeOut i e y) =
      rsy_component_input_fun SCR hOut i (resultantInputMap D e)
        (resultantStateMap D y) := by
  have h :=
    sharedSkeleton_component_input D.modeSystem D.distinct D.inducedCompatibility
      (fun i => (D.componentMode i).stateMap)
      (fun i => (D.componentMode i).inputMap)
      (fun i => (D.componentMode i).outputMap)
      D.inputPorts D.outputPorts D.matched
      (fun i y => (D.componentMode i).readout y) hOut hModeOut i e y
  simpa [resultantInputMap, resultantStateMap] using h

/-- Resultant readout inclusion, reduced to the owning component. -/
theorem resultant_readout_inclusion {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (y : rsy_SZ (sysmoscr D)) :
    ((rsy (sysmoscr D) hModeOut).RZ y).map (resultantOutputMap D) =
      (rsy SCR hOut).RZ (resultantStateMap D y) := by
  simp only [rsy, rsy_RZ, Option.map_some]
  apply congrArg some
  funext op
  simpa [resultantOutputMap] using mode_readout D hOut hModeOut y op.val

/-- The constant external input `CNS(p$)` of duration `d`. -/
def constantExternalInput {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (e : rsy_IZ (sysmoscr D)) :
    rsyClosedLoopITZ SCR :=
  fun _ => resultantInputMap D e

/--
If every component has received its constant mode input on a prefix, its state
is the constant-input trajectory of that prefix.  This is Lemma 3.77 plus
nonanticipation.
-/
theorem component_state_matches_constant {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D)) (j : Fin n) (t : Time)
    (hprefix : ∀ u, u < t →
      rsy_component_input_at SCR hOut j (constantExternalInput D e)
          (resultantStateMap D y) u =
        (D.componentMode j).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut j e y)) :
    generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (constantExternalInput D e)) t j =
      generateStateTrajectory (SCR.VSCR.Z j) ((D.componentMode j).stateMap (y j))
        (liftInput (fun _ =>
          (D.componentMode j).inputMap
            (rsy_component_input_fun (sysmoscr D) hModeOut j e y))) t := by
  rw [rsy_state_trajectory]
  apply stateTrajectory_nonanticipatory
  rw [rsn_eq_iff]
  intro u hu
  simp only [rsy_component_input_trajectory, liftInput, constantExternalInput]
  exact congrArg some (hprefix u hu)

lemma componentReadoutAt_of_readout_eq
    {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    (Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op))
    (hOut : AlwaysOutputs Z) (q : OutPort) {x₁ x₂ : SZ}
    (h : Z.RZ x₁ = Z.RZ x₂) :
    componentReadoutAt Z hOut q x₁ = componentReadoutAt Z hOut q x₂ := by
  unfold componentReadoutAt
  have h₁ := Classical.choose_spec (hOut x₁)
  have h₂ := Classical.choose_spec (hOut x₂)
  have hfun : Classical.choose (hOut x₁) = Classical.choose (hOut x₂) :=
    Option.some_injective _ ((h₁.symm.trans h).trans h₂)
  exact congrFun hfun q

/--
Constant component output keeps a connected port at its initial readout while
the source component's resolved input stays constant.
-/
theorem source_output_stable {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D)) (t : Time)
    (hprefix : ∀ u, u < t → ∀ j,
      rsy_component_input_at SCR hOut j (constantExternalInput D e)
          (resultantStateMap D y) u =
        (D.componentMode j).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut j e y))
    (op : Σ i, SCR.VSCR.OutPort i) (ht : t < d)
    (houtput : HasConstantOutput (D.componentMode op.1)) :
    rsyOutAt SCR hOut
        (generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
          (liftInput (constantExternalInput D e)) t) op =
      rsyOutAt SCR hOut (resultantStateMap D y) op := by
  obtain ⟨j, q⟩ := op
  let modeIn := rsy_component_input_fun (sysmoscr D) hModeOut j e y
  have hstate := component_state_matches_constant D hOut hModeOut e y j t
    (fun u hu => hprefix u hu j)
  have hidx : (D.componentMode j).inputIndex (y j) modeIn = fun _ =>
      (D.componentMode j).inputMap modeIn := by
    funext u
    exact hinput j (y j) modeIn u
  have hlt : t < (D.componentMode j).timeIndex (y j) modeIn := by
    rw [htime j (y j) modeIn]
    exact ht
  have hout := houtput (y j) modeIn t hlt
  simp only [Option.map_id] at hout
  rw [hidx, generateOutputTrajectory] at hout
  rw [← hstate] at hout
  rw [rsyOutAt_eq_componentReadoutAt, rsyOutAt_eq_componentReadoutAt]
  exact componentReadoutAt_of_readout_eq (SCR.VSCR.Z j) (hOut j) q hout

/-- Output constancy is required only of components that own a connected source port. -/
def HasConstantOutputOnSources {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) : Prop :=
  ∀ (i : Fin n), (∃ q, (⟨i, q⟩ : Σ k, SCR.VSCR.OutPort k) ∈ COSCR SCR) →
    HasConstantOutput (D.componentMode i)

/--
[textbook/theorem5.134/proof/resolved_input]
Simultaneous induction for Theorem 5.134 (v).  Under the constant external
input, `cfscr` — here the resolved input `rsy_component_input_at`, identified
with `cfscr` by `cfscr_input_eq_rsy_component_input_at` — equals each
component's constant mode input at every time `s < d`.
-/
theorem resolved_input_constant {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (houtput : HasConstantOutputOnSources D)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (s : Time) (hs : s < d) (i : Fin n) :
    rsy_component_input_at SCR hOut i (constantExternalInput D e)
        (resultantStateMap D y) s =
      (D.componentMode i).inputMap
        (rsy_component_input_fun (sysmoscr D) hModeOut i e y) := by
  classical
  suffices H : ∀ t, t < d → ∀ j,
      rsy_component_input_at SCR hOut j (constantExternalInput D e)
          (resultantStateMap D y) t =
        (D.componentMode j).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut j e y) by
    exact H s hs i
  intro t
  refine Nat.strongRecOn (motive := fun t => t < d → ∀ j,
      rsy_component_input_at SCR hOut j (constantExternalInput D e)
          (resultantStateMap D y) t =
        (D.componentMode j).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut j e y)) t ?_
  intro t ih ht j
  funext port
  by_cases hU : (⟨j, port⟩ : Σ k, SCR.VSCR.Port k) ∈ UISCR SCR
  · have hAt :
        rsy_component_input_at SCR hOut j (constantExternalInput D e)
            (resultantStateMap D y) t port =
          resultantInputMap D e ⟨⟨j, port⟩, hU⟩ := by
      rw [rsy_component_input_at, constantExternalInput, rsy_component_input_uiscr]
    rw [hAt]
    have hstatic := congrFun (mode_component_input D hOut hModeOut j e y) port
    rw [rsy_component_input_uiscr SCR hOut j (resultantInputMap D e)
      (resultantStateMap D y) port hU] at hstatic
    exact hstatic.symm
  · have hC : (⟨j, port⟩ : Σ k, SCR.VSCR.Port k) ∈ CISCR SCR :=
      (not_mem_uiscr_iff_mem_ciscr SCR _).mp hU
    set op := connectedOutput SCR ⟨j, port⟩ hC
    have hop : (op, (⟨j, port⟩ : Σ k, SCR.VSCR.Port k)) ∈ SCR.CSCR :=
      connectedOutput_spec SCR ⟨j, port⟩ hC
    have hty : SCR.VSCR.OutPortVal op.1 op.2 = SCR.VSCR.PortVal j port :=
      SCR.connectivity.2.2.2 op ⟨j, port⟩ hop
    have hprefix : ∀ u, u < t → ∀ k,
        rsy_component_input_at SCR hOut k (constantExternalInput D e)
            (resultantStateMap D y) u =
          (D.componentMode k).inputMap
            (rsy_component_input_fun (sysmoscr D) hModeOut k e y) :=
      fun u hu k => ih u hu (Nat.lt_trans hu ht) k
    have hsrc : HasConstantOutput (D.componentMode op.1) :=
      houtput op.1 ⟨op.2, ⟨⟨j, port⟩, hop⟩⟩
    have hstable := source_output_stable D hOut hModeOut hinput htime e y t
      hprefix op ht hsrc
    have hnow :
        rsy_component_input_at SCR hOut j (constantExternalInput D e)
            (resultantStateMap D y) t port =
          hty ▸ rsyOutAt SCR hOut
            (generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
              (liftInput (constantExternalInput D e)) t) op := by
      rw [rsy_component_input_at]
      exact rsy_component_input_of_conn SCR hOut j
        (constantExternalInput D e t) _
        port op hop hty
    have hzero :
        rsy_component_input_at SCR hOut j (constantExternalInput D e)
            (resultantStateMap D y) 0 port =
          hty ▸ rsyOutAt SCR hOut (resultantStateMap D y) op := by
      rw [rsy_component_input_at, generateStateTrajectory_zero]
      exact rsy_component_input_of_conn SCR hOut j
        (constantExternalInput D e 0) (resultantStateMap D y) port op hop hty
    rw [hnow, hstable, ← hzero]
    have hbase :
        rsy_component_input_at SCR hOut j (constantExternalInput D e)
            (resultantStateMap D y) 0 =
          (D.componentMode j).inputMap
            (rsy_component_input_fun (sysmoscr D) hModeOut j e y) := by
      simp [rsy_component_input_at, constantExternalInput, generateStateTrajectory_zero]
      exact (mode_component_input D hOut hModeOut j e y).symm
    exact congrFun hbase port

/-- Empty connectivity: every input is unconnected, so constant output is unused. -/
theorem resolved_input_constant_empty_cscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (hEmpty : SCR.CSCR = ∅)
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (_hinput : ∀ i, HasConstantInput (D.componentMode i))
    (_htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (s : Time) (_hs : s < d) (i : Fin n) :
    rsy_component_input_at SCR hOut i (constantExternalInput D e)
        (resultantStateMap D y) s =
      (D.componentMode i).inputMap
        (rsy_component_input_fun (sysmoscr D) hModeOut i e y) := by
  classical
  funext port
  have hU : (⟨i, port⟩ : Σ k, SCR.VSCR.Port k) ∈ UISCR SCR := by
    simp [UISCR, CISCR, hEmpty]
  have hAt :
      rsy_component_input_at SCR hOut i (constantExternalInput D e)
          (resultantStateMap D y) s port =
        resultantInputMap D e ⟨⟨i, port⟩, hU⟩ := by
    rw [rsy_component_input_at, constantExternalInput, rsy_component_input_uiscr]
  rw [hAt]
  have hstatic := congrFun (mode_component_input D hOut hModeOut i e y) port
  rw [rsy_component_input_uiscr SCR hOut i (resultantInputMap D e)
    (resultantStateMap D y) port hU] at hstatic
  exact hstatic.symm

/-- Full component output implies source-restricted output. -/
theorem HasConstantOutputOnSources.of_all {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (h : ∀ i, HasConstantOutput (D.componentMode i)) : HasConstantOutputOnSources D :=
  fun i _ => h i

/-- Lemma 3.77 lifts constant component steps once resolved inputs match on `[0, d)`. -/
theorem resultant_state_at_duration {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (hresolved : ∀ t, t < d → ∀ i,
      rsy_component_input_at SCR hOut i (constantExternalInput D e)
          (resultantStateMap D y) t =
        (D.componentMode i).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut i e y)) :
    resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) =
      generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (constantExternalInput D e)) d := by
  funext i
  let modeIn := rsy_component_input_fun (sysmoscr D) hModeOut i e y
  rw [resultantStateMap_NZ, (D.componentMode i).transition (y i) modeIn]
  have hdur : (D.componentMode i).behavior.duration (y i) modeIn = d :=
    htime i (y i) modeIn
  rw [hdur]
  have hidx : (D.componentMode i).behavior.input (y i) modeIn =
      fun _ => (D.componentMode i).inputMap modeIn := by
    funext t
    exact hinput i (y i) modeIn t
  rw [hidx, rsy_state_trajectory]
  apply stateTrajectory_nonanticipatory
  rw [rsn_eq_iff]
  intro t ht
  simp only [rsy_component_input_trajectory, liftInput]
  exact congrArg some (hresolved t ht i).symm

theorem resultant_state_at_duration_of_sources {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (houtput : HasConstantOutputOnSources D)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D)) :
    resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) =
      generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (constantExternalInput D e)) d :=
  resultant_state_at_duration D hOut hModeOut hinput htime e y
    (fun t ht i => resolved_input_constant D hOut hModeOut hinput htime houtput e y t ht i)

theorem resultant_state_at_duration_empty_cscr {n : Nat} {SCR : SystemCouplingRecipe n}
    (hEmpty : SCR.CSCR = ∅)
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D)) :
    resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) =
      generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (constantExternalInput D e)) d :=
  resultant_state_at_duration D hOut hModeOut hinput htime e y
    (fun t ht i =>
      resolved_input_constant_empty_cscr hEmpty D hOut hModeOut hinput htime e y t ht i)

/-- Constant external input of duration `d` with a supplied transition proof. -/
def mkConstantResultantCompat {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (hd : 0 < d)
    (htrans : ∀ y e,
      resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) =
        generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
          (liftInput (constantExternalInput D e)) d)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    ResultantModeCompatibility D hOut hModeOut where
  ports := resultantPorts D
  behavior :=
    { input := fun _ e _ => resultantInputMap D e
      duration := fun _ _ => d
      duration_pos := fun _ _ => hd }
  behavior_initial := fun _ _ => rfl
  transition := htrans
  readout := fun y => resultant_readout_inclusion D hOut hModeOut y

/-- Each external resultant output port belongs to one component, constant on `[0, d)`. -/
theorem resultant_output_constant {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (hSources : HasConstantOutputOnSources D)
    (houtput : ∀ i, HasConstantOutput (D.componentMode i))
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (s : Time) (hs : s < d) :
    generateOutputTrajectory (rsy SCR hOut) (resultantStateMap D y)
        (liftInput (constantExternalInput D e)) s =
      (rsy SCR hOut).RZ (resultantStateMap D y) := by
  simp only [generateOutputTrajectory, rsy, rsy_RZ]
  apply congrArg some
  funext op
  have hprefix : ∀ u, u < s → ∀ j,
      rsy_component_input_at SCR hOut j (constantExternalInput D e)
          (resultantStateMap D y) u =
        (D.componentMode j).inputMap
          (rsy_component_input_fun (sysmoscr D) hModeOut j e y) :=
    fun u hu j => resolved_input_constant D hOut hModeOut hinput htime hSources e y u
      (Nat.lt_of_lt_of_le hu (Nat.le_of_lt hs)) j
  simpa using source_output_stable D hOut hModeOut hinput htime e y s
    hprefix op.val hs (houtput op.val.1)

/-- Component hypotheses of Theorem 5.134. -/
structure ConstantComponentModeData {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (d : Time) : Prop where
  pos : 0 < d
  input : ∀ i, HasConstantInput (D.componentMode i)
  time : ∀ i x p, (D.componentMode i).timeIndex x p = d
  output : ∀ i, HasConstantOutput (D.componentMode i)

/-- The resultant system mode exhibited by the constant external input of duration `d`. -/
def constantResultantCompatibility {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (components : ConstantComponentModeData D d)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    ResultantModeCompatibility D hOut hModeOut :=
  mkConstantResultantCompat D hOut hModeOut components.pos fun y e =>
    resultant_state_at_duration_of_sources D hOut hModeOut components.input components.time
      (HasConstantOutputOnSources.of_all D components.output) e y

/--
  [textbook/theorem5.134/source/theorem]
  [textbook/theorem5.134/lean/hologenic_of_constant_input_output_time]
Theorem 5.134.  Constant input, constant output, a common time index, and no
port constriction make `RSY(SYSMOSCR)` a system mode of `RSY(SCR)` exhibited by
the constant external input of that duration.
-/
theorem hologenic_of_constant_input_output_time
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (components : ConstantComponentModeData D d)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      HasConstantInput (constantResultantCompatibility D hOut hModeOut components).mode ∧
      HasConstantTimeIndex (constantResultantCompatibility D hOut hModeOut components).mode d ∧
      HasConstantOutput (constantResultantCompatibility D hOut hModeOut components).mode := by
  let C := constantResultantCompatibility D hOut hModeOut components
  refine ⟨⟨C⟩, ?_, ?_, ?_⟩
  · intro y e t
    rfl
  · exact ⟨components.pos, fun _ _ => rfl⟩
  · intro y e s hs
    simpa [C, ResultantModeCompatibility.mode, constantResultantCompatibility,
      generateOutputTrajectory] using
      resultant_output_constant D hOut hModeOut components.input components.time
        (HasConstantOutputOnSources.of_all D components.output) components.output e y s hs

/-- Source-only constant output: enough for hologenicity and constant time/input. -/
structure SourceOnlyConstantComponentModeData {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (d : Time) : Prop where
  pos : 0 < d
  input : ∀ i, HasConstantInput (D.componentMode i)
  time : ∀ i x p, (D.componentMode i).timeIndex x p = d
  sources : HasConstantOutputOnSources D

theorem hologenic_of_constant_input_source_output
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (components : SourceOnlyConstantComponentModeData D d)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      ∃ M : SystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut),
        HasConstantInput M ∧ HasConstantTimeIndex M d := by
  let C := mkConstantResultantCompat D hOut hModeOut components.pos fun y e =>
    resultant_state_at_duration_of_sources D hOut hModeOut components.input components.time
      components.sources e y
  exact ⟨⟨C⟩, C.mode, fun _ _ _ => rfl, ⟨components.pos, fun _ _ => rfl⟩⟩

/-- Empty connectivity: constant input and common duration suffice (no constant output). -/
structure EmptyConnectivityConstantComponentModeData {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (d : Time) : Prop where
  empty : SCR.CSCR = ∅
  pos : 0 < d
  input : ∀ i, HasConstantInput (D.componentMode i)
  time : ∀ i x p, (D.componentMode i).timeIndex x p = d

theorem hologenic_of_constant_input_empty_cscr
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (components : EmptyConnectivityConstantComponentModeData D d)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      ∃ M : SystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut),
        HasConstantInput M ∧ HasConstantTimeIndex M d := by
  let C := mkConstantResultantCompat D hOut hModeOut components.pos fun y e =>
    resultant_state_at_duration_empty_cscr components.empty D hOut hModeOut
      components.input components.time e y
  exact ⟨⟨C⟩, C.mode, fun _ _ _ => rfl, ⟨components.pos, fun _ _ => rfl⟩⟩

/-- Duration one: constant output is automatic, so only constant input is required. -/
theorem hologenic_of_constant_input_duration_one
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    (hinput : ∀ i, HasConstantInput (D.componentMode i))
    (htime : ∀ i, HasConstantTimeIndex (D.componentMode i) 1)
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      ∃ M : SystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut),
        IsPrimaryMode M ∧ HasConstantInput M ∧ HasConstantOutput M := by
  have components : ConstantComponentModeData D 1 :=
    { pos := Nat.zero_lt_one
      input := hinput
      time := fun i => (htime i).2
      output := fun i => hasConstantOutput_of_timeIndex_one _ (htime i) }
  have H := hologenic_of_constant_input_output_time D hOut hModeOut components
  exact ⟨H.1, _, H.2.2.1, H.2.1, H.2.2.2⟩

/-! ## Corollary 5.136 -/

/-- Primary components, rewritten on the canonical one-step constant input. -/
def canonicalPrimaryRecipe {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hP : ∀ i, IsPrimaryMode (D.componentMode i)) : InducedSystemModeRecipe SCR where
  ModeState := D.ModeState
  ModePortVal := D.ModePortVal
  ModeOutPortVal := D.ModeOutPortVal
  modeSystem := D.modeSystem
  componentMode := fun i => primaryConstantInputMode (D.componentMode i) (hP i)
  distinct := D.distinct
  inputPorts := D.inputPorts
  outputPorts := D.outputPorts
  inducedCompatibility := D.inducedCompatibility
  matched := D.matched

theorem canonicalPrimary_data {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR) (hP : ∀ i, IsPrimaryMode (D.componentMode i)) :
    ConstantComponentModeData (canonicalPrimaryRecipe D hP) 1 where
  pos := Nat.zero_lt_one
  input := fun i => primaryConstantInputMode_constantInput _ (hP i)
  time := fun i => (primaryConstantInputMode_time _ (hP i)).2
  output := fun i => primaryConstantInputMode_constantOutput _ (hP i)

/--
  [textbook/corollary5.136/source/corollary]
  [textbook/corollary5.136/lean/hologenic_of_primary_modes]
Corollary 5.136.  A primary step is the one-step constant input of paragraph 5.135,
so the duration-one case of the Theorem 5.134 coupling argument applies:
the resolved input at time zero is the mode input, and the resultant is primary.
-/
theorem hologenic_of_primary_modes
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    (hP : ∀ i, IsPrimaryMode (D.componentMode i))
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      ∃ M : SystemMode (rsy (sysmoscr D) hModeOut) (rsy SCR hOut),
        IsPrimaryMode M ∧ HasConstantInput M ∧ HasConstantOutput M := by
  classical
  let C := mkConstantResultantCompat D hOut hModeOut Nat.zero_lt_one (d := 1) fun y e => by
    funext i
    rw [resultantStateMap_NZ, primary_preserves_transition (D.componentMode i) (hP i) (y i)
      (rsy_component_input_fun (sysmoscr D) hModeOut i e y)]
    have hrhs :
        generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y)
            (liftInput (constantExternalInput D e)) 1 i =
          (SCR.VSCR.Z i).NZ ((D.componentMode i).stateMap (y i))
            (some (rsy_component_input_fun SCR hOut i (resultantInputMap D e)
              (resultantStateMap D y))) := by
      rw [generateStateTrajectory_succ, generateStateTrajectory_zero]
      simp [rsy, rsy_NZ, liftInput, resultantStateMap, constantExternalInput]
    rw [hrhs]
    exact congrArg (fun p => (SCR.VSCR.Z i).NZ ((D.componentMode i).stateMap (y i)) (some p))
      (mode_component_input D hOut hModeOut i e y)
  refine ⟨⟨C⟩, C.mode, ⟨Nat.zero_lt_one, fun _ _ => rfl⟩, ?_, ?_⟩
  · intro _ _ _
    rfl
  · intro y e s hs
    have hs0 : s = 0 := Nat.lt_one_iff.mp hs
    subst hs0
    simp [C, ResultantModeCompatibility.mode, generateOutputTrajectory, generateStateTrajectory_zero]

/-! ## Theorem 5.138 -/

/--
Time-zero case of the connected-port calculation.  No constant-input or
constant-output hypothesis is used: the initial state determines every
connected port, and an external trajectory with the right initial value
determines every unconnected port.
-/
theorem resolved_input_time_zero {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (f : rsyClosedLoopITZ SCR) (hf : f 0 = resultantInputMap D e) (i : Fin n) :
    rsy_component_input_at SCR hOut i f (resultantStateMap D y) 0 =
      (D.componentMode i).inputMap
        (rsy_component_input_fun (sysmoscr D) hModeOut i e y) := by
  simp [rsy_component_input_at, generateStateTrajectory_zero, hf]
  exact (mode_component_input D hOut hModeOut i e y).symm

/--
Component inevitability, lifted by Lemma 3.77.  Any external trajectory with
the constant mode's initial value drives the resultant to the mode successor
in `d` steps.
-/
theorem resultant_inevitable_step {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k))
    (hModeOut : ∀ k, AlwaysOutputs ((sysmoscr D).VSCR.Z k))
    {d : Time}
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (hinevit : ∀ i, HasInevitableTransitions (D.componentMode i))
    (e : rsy_IZ (sysmoscr D)) (y : rsy_SZ (sysmoscr D))
    (g : ITZ (rsy_IZ SCR)) (hg : g 0 = resultantInputMap D e) :
    generateStateTrajectory (rsy SCR hOut) (resultantStateMap D y) (liftInput g) d =
      resultantStateMap D ((rsy (sysmoscr D) hModeOut).NZ y (some e)) := by
  funext i
  let modeIn := rsy_component_input_fun (sysmoscr D) hModeOut i e y
  rw [rsy_state_trajectory, resultantStateMap_NZ]
  let gcomp : ITZ ((p : SCR.VSCR.Port i) → SCR.VSCR.PortVal i p) :=
    fun t => rsy_component_input_at SCR hOut i g (resultantStateMap D y) t
  have hg0 : gcomp 0 = (D.componentMode i).inputMap modeIn :=
    resolved_input_time_zero D hOut hModeOut e y g hg i
  have hstep := hinevit i (y i) modeIn gcomp hg0
  rw [htime i (y i) modeIn] at hstep
  have htraj :
      rsy_component_input_trajectory SCR hOut i g (resultantStateMap D y) =
        liftInput gcomp := by
    funext t
    rfl
  rw [htraj]
  rw [show (resultantStateMap D y) i = (D.componentMode i).stateMap (y i) from rfl]
  exact hstep

def inevitableResultantCompatibility {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (hd : 0 < d)
    (htime : ∀ i x p, (D.componentMode i).timeIndex x p = d)
    (hinevit : ∀ i, HasInevitableTransitions (D.componentMode i))
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    ResultantModeCompatibility D hOut hModeOut :=
  mkConstantResultantCompat D hOut hModeOut hd fun y e =>
    (resultant_inevitable_step D hOut hModeOut htime hinevit e y
      (constantExternalInput D e) rfl).symm

/--
  [textbook/theorem5.138/source/theorem]
  [textbook/theorem5.138/lean/hologenic_of_inevitable_constantTime]
Theorem 5.138.  The time-zero coupling identity and component inevitability
make the constant external input a mode behavior of duration `d`, and every
external trajectory with that initial value reaches the mode successor.  The
swapped English subject in the book's last sentence is not a second claim.
-/
theorem hologenic_of_inevitable_constantTime
    {n : Nat} {SCR : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe SCR)
    (hOut : ∀ i, AlwaysOutputs (SCR.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    {d : Time} (hd : 0 < d)
    (htime : ∀ i, HasConstantTimeIndex (D.componentMode i) d)
    (hinevit : ∀ i, HasInevitableTransitions (D.componentMode i))
    [∀ i p, Nonempty (D.ModePortVal i p)]
    [∀ i q, Nonempty (D.ModeOutPortVal i q)] :
    IsSystemModeHologenic D hOut hModeOut ∧
      HasConstantTimeIndex (inevitableResultantCompatibility D hOut hModeOut hd
        (fun i x p => (htime i).2 x p) hinevit).mode d ∧
      HasInevitableTransitions (inevitableResultantCompatibility D hOut hModeOut hd
        (fun i x p => (htime i).2 x p) hinevit).mode := by
  let C := inevitableResultantCompatibility D hOut hModeOut hd
    (fun i x p => (htime i).2 x p) hinevit
  refine ⟨⟨C⟩, ⟨hd, fun _ _ => rfl⟩, ?_⟩
  intro y e g hg
  simpa [C, ResultantModeCompatibility.mode, inevitableResultantCompatibility] using
    resultant_inevitable_step D hOut hModeOut (fun i x p => (htime i).2 x p)
      hinevit e y g hg

/-! ## Theorem 5.119 -/

/--
  [textbook/theorem5.119/source/theorem]
  [textbook/theorem5.119/lean/resultant_implements_of_componentwise]
Theorem 5.119.  Hologenicity supplies the mode of `RSY(SCR2)`.  The component
port-preserving witnesses and matched connected-port maps are a
`ComponentwiseElaboration`, so Theorem 4.56 — the book's Theorem 4.55 —
supplies the homomorphism from that mode resultant to `RSY(SCR0)`.

`hRecipe` is the book's identification of `SCR1 = SYSMOSCR(SCR2, V)` with the
elaboration of the functional components, including the connectivity
correspondence.  It is not an extra dynamical hypothesis.
-/
noncomputable def resultant_implements_of_componentwise
    {n : Nat} {implementing : SystemCouplingRecipe n}
    (D : InducedSystemModeRecipe implementing)
    (hOutImpl : ∀ i, AlwaysOutputs (implementing.VSCR.Z i))
    (hModeOut : ∀ i, AlwaysOutputs ((sysmoscr D).VSCR.Z i))
    (hHolo : IsSystemModeHologenic D hOutImpl hModeOut)
    {functional : SystemCouplingRecipe n}
    (hOutFun : ∀ i, AlwaysOutputs (functional.VSCR.Z i))
    (E : ComponentwiseElaboration functional)
    (hRecipe : elabRecipe E = sysmoscr D) :
    Implements (rsy functional hOutFun) (rsy implementing hOutImpl) := by
  classical
  let C := Classical.choice hHolo
  have hModeE : ∀ i, AlwaysOutputs ((elabRecipe E).VSCR.Z i) := by
    intro i
    rw [hRecipe]
    exact hModeOut i
  have hhom := Classical.choice (thm4_56_resultant_homomorphic_image E hOutFun hModeE).2.2
  exact
    { ModeState := rsy_SZ (sysmoscr D)
      ModeInput := rsy_IZ (sysmoscr D)
      ModeOutput := rsy_OZ (sysmoscr D)
      modeSystem := rsy (sysmoscr D) hModeOut
      mode := C.mode
      hom := moveResultantHom hRecipe hModeE hModeOut hhom.toHomomorphicImageWitness }

/--
  [textbook/theorem5.139/source/open_question|partial]
  [textbook/theorem5.139/lean/chapter5_openQuestion_5_139|partial]
  [textbook/theorem5.139/policy/remains_open|partial]
  **Open Question 5.139.** Are there other, or less stringent, conditions for
  system-mode hologenicity?

  Probed weakenings of Theorem 5.134 (recorded, question remains open):
  * `hologenic_of_constant_input_empty_cscr` — empty `CSCR` drops constant output;
  * `hologenic_of_constant_input_duration_one` — duration one makes constant output automatic;
  * `hologenic_of_constant_input_source_output` — only CSCR source components need constant output;
  * Theorem 5.138 already drops constant input/output under inevitability.

  Blocked without new ideas: cascade-only induction, unequal component durations,
  and dropping constant input without inevitability. This marker carries no axiom.
-/
def chapter5_openQuestion_5_139 : String :=
  "Open: other/less stringent hologenicity conditions. Easy weakenings recorded " ++
    "(empty CSCR; duration one; source-only output; inevitability via 5.138). " ++
    "Blocked: cascade-only, unequal durations, drop constant input without inevitability."

end WymoreModeCoupling
