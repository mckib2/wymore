import Mbse.Isomorphism
import Mbse.PartialDynamicsHomFragment
import Mbse.Wymore
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-!
# A Turing machine as a Wymore coupling recipe

The paper case study needs a universal machine that is presented as a *system* rather than as a
program: components with ports, a connectable vector, a coupling recipe, and a resultant.  This
module builds exactly that.

* `tapeZone` — the tape: state is a two-sided tape with implicit blanks, one input port carrying a
  write/move command and two output ports (one wired to the control, one exposed at the boundary).
* `ctlZone` — the finite control: state is a sense/act phase over the machine table, one input port
  carrying the scanned symbol, one unconnected input port carrying an external load command, one
  output port carrying the tape command and one unconnected output port carrying the halted flag.
* `tmSCR` — the coupling recipe wiring the scanned symbol into the control and the command into the
  tape; the resultant `tmResultant` is the coupled Turing machine.
* `tmReference` — the monolithic reference table over configurations, of which the resultant is a
  homomorphic image (indeed an isomorph), so the compiled dynamics-encoding fragment of the
  reference is satisfied by the coupling.
* `tmMacroStep` — two ticks of the coupled machine perform exactly one Turing machine step.  The
  coupling therefore runs at twice the granularity of the abstract machine, which is what the
  tick-matching discussion in the paper turns on.

The machine table has the shape of `Turing.TM0.Machine` in Mathlib
(`Λ → Γ → Option (Λ × …)`, with `none` meaning halt), with write and move combined into a single
command so that the tape zone has one input port.
-/

namespace TuringCoupling

open Homomorphism PartialDynamicsHomFragment

/-! ## Generic facts about discrete systems

Two components of a connectable vector must be distinct (Definition 3.3).  When one component has
infinite state and the other has finite state, distinctness follows from cardinality alone.
-/

/-- A discrete system is determined by its next-state and readout functions. -/
theorem DiscreteSystem.ext' {S I O : Type} {Z1 Z2 : DiscreteSystem S I O}
    (hN : Z1.NZ = Z2.NZ) (hR : Z1.RZ = Z2.RZ) : Z1 = Z2 := by
  cases Z1; cases Z2; cases hN; cases hR; rfl

/-- Systems over finite state, input and output spaces form a finite type. -/
instance discreteSystem_finite {S I O : Type} [Finite S] [Finite I] [Finite O] :
    Finite (DiscreteSystem S I O) :=
  Finite.of_injective (fun Z => (Z.NZ, Z.RZ)) (by
    intro Z1 Z2 h
    exact DiscreteSystem.ext' (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Systems over an infinite state space form an infinite type: constant next-state functions
already give an injection from the state space. -/
theorem infinite_discreteSystem {S I O : Type} [Infinite S] :
    Infinite (DiscreteSystem S I O) :=
  Infinite.of_injective
    (fun s : S => ({ sz_nonempty := ⟨s⟩, NZ := fun _ _ => s, RZ := fun _ => none } :
      DiscreteSystem S I O))
    (by
      intro s1 s2 h
      have hN := congrArg DiscreteSystem.NZ h
      exact congrFun (congrFun hN s1) none)

/-- Distinct cardinalities refute heterogeneous equality. -/
theorem not_heq_of_infinite_finite {α β : Type} [Infinite α] [Finite β] (a : α) (b : β) :
    ¬ HEq a b := by
  intro h
  have hty : α = β := type_eq_of_heq h
  subst hty
  exact not_finite α

/-! ## The tape -/

/-- Head motion. -/
inductive HeadMove
  | left
  | right
  | stay
  deriving DecidableEq, Repr, Fintype

/-- A command delivered to the tape: hold, or write a symbol and move the head. -/
inductive TapeCmd (Γ : Type)
  | hold
  | act (write : Γ) (move : HeadMove)
  deriving DecidableEq, Repr

/--
A two-sided tape with implicit blanks: `left` lists the cells to the left of the head with the
nearest cell first, `head` is the scanned cell, `right` lists the cells to the right.
-/
structure TapeState (Γ : Type) where
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq, Repr

/-- The blank tape. -/
def TapeState.blank (Γ : Type) [Inhabited Γ] : TapeState Γ :=
  ⟨[], default, []⟩

/-- Apply a tape command: write first, then move, extending with blanks at the ends. -/
def TapeState.apply {Γ : Type} [Inhabited Γ] (t : TapeState Γ) : TapeCmd Γ → TapeState Γ
  | .hold => t
  | .act w .stay => { t with head := w }
  | .act w .left =>
      match t.left with
      | [] => ⟨[], default, w :: t.right⟩
      | a :: l => ⟨l, a, w :: t.right⟩
  | .act w .right =>
      match t.right with
      | [] => ⟨w :: t.left, default, []⟩
      | a :: r => ⟨w :: t.left, a, r⟩

instance {Γ : Type} [Inhabited Γ] : Inhabited (TapeState Γ) := ⟨TapeState.blank Γ⟩

/-- The tape has unboundedly many states: the left part can be arbitrarily long. -/
instance tapeState_infinite {Γ : Type} [Inhabited Γ] : Infinite (TapeState Γ) :=
  Infinite.of_injective (fun n : Nat => (⟨List.replicate n default, default, []⟩ : TapeState Γ))
    (by
      intro m n h
      have hl : List.replicate m (default : Γ) = List.replicate n default :=
        congrArg TapeState.left h
      simpa using congrArg List.length hl)

/-! ## Ports -/

/-- The tape's input ports: the command port (wired to the control). -/
inductive TapeIn
  | cmd
  deriving DecidableEq, Repr, Fintype

/--
The tape's output ports.  Coupling connectivity is one-to-one, so exposing the scanned symbol both
to the control and at the system boundary requires two ports.
-/
inductive TapeOut
  | scan
  | window
  deriving DecidableEq, Repr, Fintype

/-- The control's input ports: the scanned symbol (wired) and an external load command. -/
inductive CtlIn
  | sym
  | load
  deriving DecidableEq, Repr, Fintype

/-- The control's output ports: the tape command (wired) and an external halted flag. -/
inductive CtlOut
  | cmd
  | halted
  deriving DecidableEq, Repr, Fintype

/-- Port value sets of the tape's input ports. -/
def TapeInVal (Γ : Type) : TapeIn → Type
  | .cmd => TapeCmd Γ

/-- Port value sets of the tape's output ports. -/
def TapeOutVal (Γ : Type) : TapeOut → Type
  | .scan => Γ
  | .window => Γ

/-- Port value sets of the control's input ports. -/
def CtlInVal (Γ Λ : Type) : CtlIn → Type
  | .sym => Γ
  | .load => Option Λ

/-- Port value sets of the control's output ports. -/
def CtlOutVal (Γ : Type) : CtlOut → Type
  | .cmd => TapeCmd Γ
  | .halted => Bool

/-! ## The finite control -/

/--
A Turing machine table: in label `q` scanning symbol `a`, either halt (`none`) or move to label
`q'` after writing and moving.  This is the shape of `Turing.TM0.Machine`.
-/
abbrev TMTable (Γ Λ : Type) := Λ → Γ → Option (Λ × Γ × HeadMove)

/--
Control state.  Readouts are functions of state alone (Moore form), so a machine step is split
into a sense phase, which latches the action selected by the table, and an act phase, which emits
the command to the tape.
-/
inductive CtlState (Γ Λ : Type)
  | sense (q : Λ)
  | act (q : Λ) (c : TapeCmd Γ)
  | halted
  deriving DecidableEq, Repr

/-- The command the control emits in a given state. -/
def CtlState.cmd {Γ Λ : Type} : CtlState Γ Λ → TapeCmd Γ
  | .sense _ => .hold
  | .act _ c => c
  | .halted => .hold

/-- The halted flag the control exposes at the boundary. -/
def CtlState.haltedFlag {Γ Λ : Type} : CtlState Γ Λ → Bool
  | .halted => true
  | _ => false

/--
Control next state.  An external load command overrides the machine; otherwise the sense phase
consults the table on the scanned symbol and the act phase returns to sensing.
-/
def CtlState.step {Γ Λ : Type} (M : TMTable Γ Λ) (s : CtlState Γ Λ) (a : Γ) :
    Option Λ → CtlState Γ Λ
  | some q0 => .sense q0
  | none =>
      match s with
      | .sense q =>
          match M q a with
          | none => .halted
          | some (q', w, m) => .act q' (.act w m)
      | .act q _ => .sense q
      | .halted => .halted

/-- Control state is finite when the alphabet and the label set are. -/
def ctlStateEquiv (Γ Λ : Type) : CtlState Γ Λ ≃ Λ ⊕ (Λ × TapeCmd Γ) ⊕ Unit where
  toFun
    | .sense q => .inl q
    | .act q c => .inr (.inl (q, c))
    | .halted => .inr (.inr ())
  invFun
    | .inl q => .sense q
    | .inr (.inl (q, c)) => .act q c
    | .inr (.inr _) => .halted
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩ | _) <;> rfl

/-- `HeadMove` is a three-element type. -/
def headMoveEquiv : HeadMove ≃ Unit ⊕ Unit ⊕ Unit where
  toFun
    | .left => .inl ()
    | .right => .inr (.inl ())
    | .stay => .inr (.inr ())
  invFun
    | .inl _ => .left
    | .inr (.inl _) => .right
    | .inr (.inr _) => .stay
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

instance : Finite HeadMove := Finite.of_equiv _ headMoveEquiv.symm

/-- `TapeCmd Γ` is finite when the alphabet is. -/
def tapeCmdEquiv (Γ : Type) : TapeCmd Γ ≃ Unit ⊕ (Γ × HeadMove) where
  toFun
    | .hold => .inl ()
    | .act w m => .inr (w, m)
  invFun
    | .inl _ => .hold
    | .inr (w, m) => .act w m
  left_inv := by rintro (_ | ⟨_, _⟩) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl

instance tapeCmd_finite {Γ : Type} [Finite Γ] : Finite (TapeCmd Γ) :=
  Finite.of_equiv _ (tapeCmdEquiv Γ).symm

instance ctlState_finite {Γ Λ : Type} [Finite Γ] [Finite Λ] : Finite (CtlState Γ Λ) :=
  Finite.of_equiv _ (ctlStateEquiv Γ Λ).symm

instance ctlState_nonempty {Γ Λ : Type} : Nonempty (CtlState Γ Λ) := ⟨.halted⟩

instance tapeInVal_finite {Γ : Type} [Finite Γ] (p : TapeIn) : Finite (TapeInVal Γ p) := by
  cases p; exact tapeCmd_finite

instance tapeOutVal_finite {Γ : Type} [Finite Γ] (p : TapeOut) : Finite (TapeOutVal Γ p) := by
  cases p <;> assumption

instance ctlInVal_finite {Γ Λ : Type} [Finite Γ] [Finite Λ] (p : CtlIn) :
    Finite (CtlInVal Γ Λ p) := by
  cases p
  · assumption
  · show Finite (Option Λ); infer_instance

instance ctlOutVal_finite {Γ : Type} [Finite Γ] (p : CtlOut) : Finite (CtlOutVal Γ p) := by
  cases p
  · exact tapeCmd_finite
  · exact Finite.of_equiv _ (Equiv.refl Bool)

/-! ## The two zones as discrete systems -/

/-- The tape's readout: the scanned symbol, offered on both output ports. -/
def tapeReadout {Γ : Type} (t : TapeState Γ) : (op : TapeOut) → TapeOutVal Γ op
  | .scan => t.head
  | .window => t.head

/--
The tape zone: state is the tape, the single input port carries a command, and the two output
ports both carry the scanned symbol (one for the control, one for the boundary).
-/
def tapeZone (Γ : Type) [Inhabited Γ] :
    DiscreteSystem (TapeState Γ) ((p : TapeIn) → TapeInVal Γ p)
      ((op : TapeOut) → TapeOutVal Γ op) where
  sz_nonempty := ⟨TapeState.blank Γ⟩
  NZ t
    | none => t
    | some inp => t.apply (inp .cmd)
  RZ t := some (tapeReadout t)

/-- The control's readout: the tape command and the halted flag. -/
def ctlReadout {Γ Λ : Type} (s : CtlState Γ Λ) : (op : CtlOut) → CtlOutVal Γ op
  | .cmd => s.cmd
  | .halted => s.haltedFlag

/--
The control zone: state is the sense/act phase, the input ports carry the scanned symbol and an
external load command, and the output ports carry the tape command and the halted flag.
-/
def ctlZone (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    DiscreteSystem (CtlState Γ Λ) ((p : CtlIn) → CtlInVal Γ Λ p)
      ((op : CtlOut) → CtlOutVal Γ op) where
  sz_nonempty := ⟨.halted⟩
  NZ s
    | none => s
    | some inp => CtlState.step M s (inp .sym) (inp .load)
  RZ s := some (ctlReadout s)

theorem tapeZone_alwaysOutputs (Γ : Type) [Inhabited Γ] : AlwaysOutputs (tapeZone Γ) :=
  fun t => ⟨tapeReadout t, rfl⟩

theorem ctlZone_alwaysOutputs (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    AlwaysOutputs (ctlZone Γ Λ M) :=
  fun s => ⟨ctlReadout s, rfl⟩

/-! ## The connectable vector -/

/-- Component state spaces: tape at index `0`, control at index `1`. -/
def tmSZ (Γ Λ : Type) : Fin 2 → Type :=
  Fin.cases (TapeState Γ) (fun _ => CtlState Γ Λ)

/-- Component input port sets. -/
def tmPort : Fin 2 → Type :=
  Fin.cases TapeIn (fun _ => CtlIn)

/-- Component input port value sets. -/
def tmPortVal (Γ Λ : Type) : (i : Fin 2) → tmPort i → Type :=
  Fin.cases (TapeInVal Γ) (fun _ => CtlInVal Γ Λ)

/-- Component output port sets. -/
def tmOutPort : Fin 2 → Type :=
  Fin.cases TapeOut (fun _ => CtlOut)

/-- Component output port value sets. -/
def tmOutPortVal (Γ : Type) : (i : Fin 2) → tmOutPort i → Type :=
  Fin.cases (TapeOutVal Γ) (fun _ => CtlOutVal Γ)

/-- The two zones indexed as a vector. -/
def tmZ (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) (i : Fin 2) :
    DiscreteSystem (tmSZ Γ Λ i) ((p : tmPort i) → tmPortVal Γ Λ i p)
      ((op : tmOutPort i) → tmOutPortVal Γ i op) :=
  Fin.cases (motive := fun i => DiscreteSystem (tmSZ Γ Λ i)
      ((p : tmPort i) → tmPortVal Γ Λ i p) ((op : tmOutPort i) → tmOutPortVal Γ i op))
    (tapeZone Γ) (fun _ => ctlZone Γ Λ M) i

@[simp] theorem tmZ_zero (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    tmZ Γ Λ M 0 = tapeZone Γ := rfl

@[simp] theorem tmZ_one (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    tmZ Γ Λ M 1 = ctlZone Γ Λ M := rfl

/--
The two zones are distinct in the sense of Definition 3.3: the tape has unboundedly many states
while the control has finitely many, so the two systems cannot even be heterogeneously equal.
-/
theorem tmZ_distinct (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ)
    (i j : Fin 2) (hne : i ≠ j) : ¬ HEq (tmZ Γ Λ M i) (tmZ Γ Λ M j) := by
  have key : ¬ HEq (tapeZone Γ) (ctlZone Γ Λ M) := by
    have : Infinite (DiscreteSystem (TapeState Γ) ((p : TapeIn) → TapeInVal Γ p)
        ((op : TapeOut) → TapeOutVal Γ op)) := infinite_discreteSystem
    exact not_heq_of_infinite_finite _ _
  fin_cases i <;> fin_cases j
  · exact absurd rfl hne
  · simpa using key
  · simpa using fun h => key (HEq.symm h)
  · exact absurd rfl hne

/-- The connectable vector of the Turing machine coupling. -/
def tmVector (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ) :
    PortSystemVector 2 where
  SZ := tmSZ Γ Λ
  Port := tmPort
  PortVal := tmPortVal Γ Λ
  OutPort := tmOutPort
  OutPortVal := tmOutPortVal Γ
  Z := tmZ Γ Λ M
  distinct := tmZ_distinct Γ Λ M

theorem tmVector_alwaysOutputs (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) (i : Fin 2) : AlwaysOutputs ((tmVector Γ Λ M).Z i) := by
  fin_cases i
  · exact tapeZone_alwaysOutputs Γ
  · exact ctlZone_alwaysOutputs Γ Λ M

/-- A component readout is whatever the total readout function returns. -/
theorem componentReadoutAt_of_RZ {SZ IZ OutPort : Type} {OutPortVal : OutPort → Type}
    {Z : DiscreteSystem SZ IZ ((op : OutPort) → OutPortVal op)}
    (hOut : AlwaysOutputs Z) {x : SZ} {f : (op : OutPort) → OutPortVal op}
    (hf : Z.RZ x = some f) (op : OutPort) :
    componentReadoutAt Z hOut op x = f op := by
  have h := Classical.choose_spec (hOut x)
  have hsome : some f = some (Classical.choose (hOut x)) := hf.symm.trans h
  exact congrFun (Option.some.inj hsome).symm op

/-! ## The coupling recipe -/

/-- An output port of the coupling, tagged by the component that carries it. -/
abbrev TMOutIdx := Σ i : Fin 2, tmOutPort i

/-- An input port of the coupling, tagged by the component that carries it. -/
abbrev TMInIdx := Σ i : Fin 2, tmPort i

/-- Wire: the control's command port drives the tape's command port. -/
def wireCmd : TMOutIdx × TMInIdx := (⟨1, CtlOut.cmd⟩, ⟨0, TapeIn.cmd⟩)

/-- Wire: the tape's scan port drives the control's symbol port. -/
def wireScan : TMOutIdx × TMInIdx := (⟨0, TapeOut.scan⟩, ⟨1, CtlIn.sym⟩)

/--
Connectivity of the coupling: exactly two wires, one in each direction, so the recipe is a pure
feedback coupling in the sense of Definition 3.7.  The remaining ports — the control's `load` input
and its `halted` output, and the tape's `window` output — are unconnected and form the boundary of
the resultant.
-/
def tmCSCR : Set (TMOutIdx × TMInIdx) := {wireCmd, wireScan}

theorem mem_tmCSCR_iff (p : TMOutIdx × TMInIdx) : p ∈ tmCSCR ↔ p = wireCmd ∨ p = wireScan :=
  Iff.rfl

private theorem tmOut_cmd_ne_scan : (⟨1, CtlOut.cmd⟩ : TMOutIdx) ≠ ⟨0, TapeOut.scan⟩ := by
  intro h
  exact absurd (congrArg Sigma.fst h) (by decide)

private theorem tmIn_cmd_ne_sym : (⟨0, TapeIn.cmd⟩ : TMInIdx) ≠ ⟨1, CtlIn.sym⟩ := by
  intro h
  exact absurd (congrArg Sigma.fst h) (by decide)

theorem tm_connectivity (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ) :
    IsSystemConnectivity (tmVector Γ Λ M) tmCSCR := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x y1 y2 hm1 hm2
    rcases (mem_tmCSCR_iff _).mp hm1 with h1 | h1 <;>
      rcases (mem_tmCSCR_iff _).mp hm2 with h2 | h2
    · have e1 : y1 = wireCmd.2 := congrArg Prod.snd h1
      have e2 : y2 = wireCmd.2 := congrArg Prod.snd h2
      exact e1.trans e2.symm
    · have e1 : x = wireCmd.1 := congrArg Prod.fst h1
      have e2 : x = wireScan.1 := congrArg Prod.fst h2
      exact absurd (e1.symm.trans e2) tmOut_cmd_ne_scan
    · have e1 : x = wireScan.1 := congrArg Prod.fst h1
      have e2 : x = wireCmd.1 := congrArg Prod.fst h2
      exact absurd (e2.symm.trans e1) tmOut_cmd_ne_scan
    · have e1 : y1 = wireScan.2 := congrArg Prod.snd h1
      have e2 : y2 = wireScan.2 := congrArg Prod.snd h2
      exact e1.trans e2.symm
  · intro x1 x2 y hm1 hm2
    rcases (mem_tmCSCR_iff _).mp hm1 with h1 | h1 <;>
      rcases (mem_tmCSCR_iff _).mp hm2 with h2 | h2
    · have e1 : x1 = wireCmd.1 := congrArg Prod.fst h1
      have e2 : x2 = wireCmd.1 := congrArg Prod.fst h2
      exact e1.trans e2.symm
    · have e1 : y = wireCmd.2 := congrArg Prod.snd h1
      have e2 : y = wireScan.2 := congrArg Prod.snd h2
      exact absurd (e1.symm.trans e2) tmIn_cmd_ne_sym
    · have e1 : y = wireScan.2 := congrArg Prod.snd h1
      have e2 : y = wireCmd.2 := congrArg Prod.snd h2
      exact absurd (e2.symm.trans e1) tmIn_cmd_ne_sym
    · have e1 : x1 = wireScan.1 := congrArg Prod.fst h1
      have e2 : x2 = wireScan.1 := congrArg Prod.fst h2
      exact e1.trans e2.symm
  · intro heq
    have hmem : (⟨1, CtlOut.halted⟩ : TMOutIdx) ∈ {x : TMOutIdx | ∃ y, (x, y) ∈ tmCSCR} :=
      heq ▸ Set.mem_univ _
    obtain ⟨y, hy⟩ := hmem
    simp only [tmCSCR, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      wireCmd, wireScan] at hy
    rcases hy with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [Sigma.mk.injEq] at h
  · intro heq
    have hmem : (⟨1, CtlIn.load⟩ : TMInIdx) ∈ {y : TMInIdx | ∃ x, (x, y) ∈ tmCSCR} :=
      heq ▸ Set.mem_univ _
    obtain ⟨x, hx⟩ := hmem
    simp only [tmCSCR, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      wireCmd, wireScan] at hx
    rcases hx with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [Sigma.mk.injEq] at h
  · intro op ip hm
    rcases (mem_tmCSCR_iff _).mp hm with h | h
    · have h1 : op = wireCmd.1 := congrArg Prod.fst h
      have h2 : ip = wireCmd.2 := congrArg Prod.snd h
      subst h1; subst h2; rfl
    · have h1 : op = wireScan.1 := congrArg Prod.fst h
      have h2 : ip = wireScan.2 := congrArg Prod.snd h
      subst h1; subst h2; rfl

/-- The Turing machine coupling recipe. -/
def tmSCR (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ) :
    SystemCouplingRecipe 2 where
  VSCR := tmVector Γ Λ M
  CSCR := tmCSCR
  connectivity := tm_connectivity Γ Λ M

theorem tmSCR_alwaysOutputs (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) (i : Fin 2) : AlwaysOutputs ((tmSCR Γ Λ M).VSCR.Z i) :=
  tmVector_alwaysOutputs Γ Λ M i

/-- The coupled Turing machine: the resultant of the recipe. -/
noncomputable def tmResultant (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ]
    (M : TMTable Γ Λ) :
    DiscreteSystem (rsy_SZ (tmSCR Γ Λ M)) (rsy_IZ (tmSCR Γ Λ M)) (rsy_OZ (tmSCR Γ Λ M)) :=
  rsy (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M)

/-! ## Which ports are connected -/

section Ports

variable (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ)

theorem tape_cmd_mem_ciscr : (⟨0, TapeIn.cmd⟩ : TMInIdx) ∈ CISCR (tmSCR Γ Λ M) :=
  ⟨⟨1, CtlOut.cmd⟩, Or.inl rfl⟩

theorem ctl_sym_mem_ciscr : (⟨1, CtlIn.sym⟩ : TMInIdx) ∈ CISCR (tmSCR Γ Λ M) :=
  ⟨⟨0, TapeOut.scan⟩, Or.inr rfl⟩

theorem ctl_load_mem_uiscr : (⟨1, CtlIn.load⟩ : TMInIdx) ∈ UISCR (tmSCR Γ Λ M) := by
  intro hC
  obtain ⟨op, hop⟩ := hC
  rcases (mem_tmCSCR_iff _).mp hop with h | h
  · have e : (⟨1, CtlIn.load⟩ : TMInIdx) = wireCmd.2 := congrArg Prod.snd h
    simp [wireCmd, Sigma.mk.injEq] at e
  · have e : (⟨1, CtlIn.load⟩ : TMInIdx) = wireScan.2 := congrArg Prod.snd h
    simp [wireScan, Sigma.mk.injEq] at e

theorem tape_window_mem_uoscr : (⟨0, TapeOut.window⟩ : TMOutIdx) ∈ UOSCR (tmSCR Γ Λ M) := by
  intro hC
  obtain ⟨ip, hip⟩ := hC
  rcases (mem_tmCSCR_iff _).mp hip with h | h
  · have e : (⟨0, TapeOut.window⟩ : TMOutIdx) = wireCmd.1 := congrArg Prod.fst h
    simp [wireCmd, Sigma.mk.injEq] at e
  · have e : (⟨0, TapeOut.window⟩ : TMOutIdx) = wireScan.1 := congrArg Prod.fst h
    simp [wireScan, Sigma.mk.injEq] at e

theorem ctl_halted_mem_uoscr : (⟨1, CtlOut.halted⟩ : TMOutIdx) ∈ UOSCR (tmSCR Γ Λ M) := by
  intro hC
  obtain ⟨ip, hip⟩ := hC
  rcases (mem_tmCSCR_iff _).mp hip with h | h
  · have e : (⟨1, CtlOut.halted⟩ : TMOutIdx) = wireCmd.1 := congrArg Prod.fst h
    simp [wireCmd, Sigma.mk.injEq] at e
  · have e : (⟨1, CtlOut.halted⟩ : TMOutIdx) = wireScan.1 := congrArg Prod.fst h
    simp [wireScan, Sigma.mk.injEq] at e

end Ports

/-! ## What each port carries

The value a connected input port receives is the value on the output port that feeds it.  Stated
heterogeneously because the two sides are typed by the (equal, but not syntactically identical)
port value sets of the two ends of the wire.
-/

private theorem heq_of_eqRec {A B : Sort u} (h : A = B) (a : A) : HEq (h ▸ a) a := by
  cases h; rfl

theorem rsyOutAt_congr_heq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (x : rsy_SZ SCR)
    {op1 op2 : Σ (j : Fin n), SCR.VSCR.OutPort j} (h : op1 = op2) :
    HEq (rsyOutAt SCR hOut x op1) (rsyOutAt SCR hOut x op2) := by
  cases h; rfl

theorem rsy_component_input_heq {n : Nat} (SCR : SystemCouplingRecipe n)
    (hOut : ∀ k, AlwaysOutputs (SCR.VSCR.Z k)) (i : Fin n) (extIn : rsy_IZ SCR)
    (x : rsy_SZ SCR) (port : SCR.VSCR.Port i) (op : Σ (j : Fin n), SCR.VSCR.OutPort j)
    (hop : (op, (⟨i, port⟩ : Σ j, SCR.VSCR.Port j)) ∈ SCR.CSCR) :
    HEq (rsy_component_input_fun SCR hOut i extIn x port) (rsyOutAt SCR hOut x op) := by
  have hC : (⟨i, port⟩ : Σ j, SCR.VSCR.Port j) ∈ CISCR SCR := ⟨op, hop⟩
  have hopEq : connectedOutput SCR ⟨i, port⟩ hC = op :=
    SCR.connectivity.1.2 _ _ ⟨i, port⟩ (connectedOutput_spec SCR ⟨i, port⟩ hC) hop
  rw [rsy_component_input_ciscr SCR hOut i extIn x port hC]
  exact HEq.trans (heq_of_eqRec _ _) (rsyOutAt_congr_heq SCR hOut x hopEq)

section Wiring

variable (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ)
variable (extIn : rsy_IZ (tmSCR Γ Λ M)) (x : rsy_SZ (tmSCR Γ Λ M))

/-- The tape's command port carries the command the control is currently emitting. -/
theorem tm_input_tape_cmd :
    rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 0 extIn x TapeIn.cmd =
      CtlState.cmd (x 1) := by
  have h := rsy_component_input_heq (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 0 extIn x
    TapeIn.cmd ⟨1, CtlOut.cmd⟩ (Or.inl rfl)
  have hout : rsyOutAt (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) x ⟨1, CtlOut.cmd⟩ =
      CtlState.cmd (x 1) := by
    rw [rsyOutAt_eq_componentReadoutAt]
    exact componentReadoutAt_of_RZ (tmSCR_alwaysOutputs Γ Λ M 1) rfl CtlOut.cmd
  exact (eq_of_heq h).trans hout

/-- The control's symbol port carries the symbol under the tape head. -/
theorem tm_input_ctl_sym :
    rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x CtlIn.sym =
      TapeState.head (x 0) := by
  have h := rsy_component_input_heq (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x
    CtlIn.sym ⟨0, TapeOut.scan⟩ (Or.inr rfl)
  have hout : rsyOutAt (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) x ⟨0, TapeOut.scan⟩ =
      TapeState.head (x 0) := by
    rw [rsyOutAt_eq_componentReadoutAt]
    exact componentReadoutAt_of_RZ (tmSCR_alwaysOutputs Γ Λ M 0) rfl TapeOut.scan
  exact (eq_of_heq h).trans hout

/-- The control's load port is unconnected, so it carries whatever the environment supplies. -/
theorem tm_input_ctl_load :
    rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x CtlIn.load =
      extIn ⟨⟨1, CtlIn.load⟩, ctl_load_mem_uiscr Γ Λ M⟩ :=
  rsy_component_input_uiscr (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x CtlIn.load
    (ctl_load_mem_uiscr Γ Λ M)

/-! ## The resultant's dynamics

The coupled machine is a Wymore system in its own right: state is a tape together with a control
phase, external input is the load command on the control's unconnected port, and external output is
the scanned symbol together with the halted flag on the two unconnected output ports.
-/

/-- On a driven tick the tape applies the command the control is emitting. -/
theorem tmResultant_NZ_tape :
    (tmResultant Γ Λ M).NZ x (some extIn) 0 = TapeState.apply (x 0) (CtlState.cmd (x 1)) := by
  show TapeState.apply (x 0)
      (rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 0 extIn x TapeIn.cmd) = _
  rw [tm_input_tape_cmd]

/-- On a driven tick the control steps on the scanned symbol, subject to the external load. -/
theorem tmResultant_NZ_ctl :
    (tmResultant Γ Λ M).NZ x (some extIn) 1 =
      CtlState.step M (x 1) (TapeState.head (x 0))
        (extIn ⟨⟨1, CtlIn.load⟩, ctl_load_mem_uiscr Γ Λ M⟩) := by
  show CtlState.step M (x 1)
      (rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x CtlIn.sym)
      (rsy_component_input_fun (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) 1 extIn x CtlIn.load) = _
  rw [tm_input_ctl_sym, tm_input_ctl_load]

/-- An autonomous tick leaves the machine where it is: both zones idle without input. -/
theorem tmResultant_NZ_none : (tmResultant Γ Λ M).NZ x none = x := by
  funext i
  fin_cases i <;> rfl

/-- The boundary output on the tape's window port is the scanned symbol. -/
theorem tmResultant_out_window :
    rsyOutAt (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) x ⟨0, TapeOut.window⟩ =
      TapeState.head (x 0) := by
  rw [rsyOutAt_eq_componentReadoutAt]
  exact componentReadoutAt_of_RZ (tmSCR_alwaysOutputs Γ Λ M 0) rfl TapeOut.window

/-- The boundary output on the control's halted port is the halted flag. -/
theorem tmResultant_out_halted :
    rsyOutAt (tmSCR Γ Λ M) (tmSCR_alwaysOutputs Γ Λ M) x ⟨1, CtlOut.halted⟩ =
      CtlState.haltedFlag (x 1) := by
  rw [rsyOutAt_eq_componentReadoutAt]
  exact componentReadoutAt_of_RZ (tmSCR_alwaysOutputs Γ Λ M 1) rfl CtlOut.halted

/-- The resultant always produces output, so it can itself be a component of a further coupling. -/
theorem tmResultant_alwaysOutputs : AlwaysOutputs (tmResultant Γ Λ M) :=
  fun _ => ⟨_, rfl⟩

end Wiring

/-! ## A concrete table

Universality is definitional for the construction above — it is parametric in the table `M` — but a
concrete instance is needed to state audits and to match the finite instance the solver checks.  This
is the machine that inverts the scanned bit, moves right, and halts.
-/

/-- Invert the scanned bit and move right, then halt.  Labels: `false` runs, `true` halts. -/
def bitFlipTable : TMTable Bool Bool
  | false, a => some (true, !a, .right)
  | true, _ => none

/-! ## The monolithic reference

The functional intent is stated as a single system over configurations, with no ports and no
internal structure: state is a tape together with a control phase, input is the load command,
output is the scanned symbol together with the halted flag.  This is the `Z_spec` of the paper, and
the coupling of the previous sections is the `Z_impl`.
-/

/-- A configuration of the abstract machine. -/
abbrev TMConfig (Γ Λ : Type) := TapeState Γ × CtlState Γ Λ

/-- The reference table: one tick moves the tape by the control's command and steps the control. -/
def tmReference (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    DiscreteSystem (TMConfig Γ Λ) (Option Λ) (Γ × Bool) where
  sz_nonempty := ⟨(TapeState.blank Γ, .halted)⟩
  NZ c
    | none => c
    | some ld => (c.1.apply c.2.cmd, CtlState.step M c.2 c.1.head ld)
  RZ c := some (c.1.head, c.2.haltedFlag)

theorem tmReference_alwaysOutputs (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ) :
    AlwaysOutputs (tmReference Γ Λ M) :=
  fun _ => ⟨_, rfl⟩

/-! ## The coupling realises the reference -/

section Realisation

variable (Γ Λ : Type) [Inhabited Γ] [Finite Γ] [Finite Λ] (M : TMTable Γ Λ)

/-- Port values of an external input carrying the load command `ld`. -/
def tmExtInVal (ld : Option Λ) : (i : Fin 2) → (p : tmPort i) → tmPortVal Γ Λ i p :=
  Fin.cases (motive := fun i => (p : tmPort i) → tmPortVal Γ Λ i p)
    (fun p => match p with | TapeIn.cmd => TapeCmd.hold)
    (fun _ p => match p with | CtlIn.sym => (default : Γ) | CtlIn.load => ld)

/-- The external input of the coupling that carries the load command `ld`. -/
def tmExtIn (ld : Option Λ) : rsy_IZ (tmSCR Γ Λ M) :=
  fun ip => tmExtInVal Γ Λ ld ip.val.1 ip.val.2

/-- Port values of a boundary output carrying scanned symbol `a` and halted flag `b`. -/
def tmExtOutVal (a : Γ) (b : Bool) : (i : Fin 2) → (op : tmOutPort i) → tmOutPortVal Γ i op :=
  Fin.cases (motive := fun i => (op : tmOutPort i) → tmOutPortVal Γ i op)
    (fun op => match op with | TapeOut.scan => a | TapeOut.window => a)
    (fun _ op => match op with | CtlOut.cmd => TapeCmd.hold | CtlOut.halted => b)

/-- The load port is the only unconnected input port. -/
theorem uiscr_eq_load (ip : UnconnInPort (tmSCR Γ Λ M)) : ip.val = ⟨1, CtlIn.load⟩ := by
  obtain ⟨⟨i, p⟩, hp⟩ := ip
  fin_cases i
  · cases p
    exact absurd (tape_cmd_mem_ciscr Γ Λ M) hp
  · cases p
    · exact absurd (ctl_sym_mem_ciscr Γ Λ M) hp
    · rfl

/-- The window and halted ports are the only unconnected output ports. -/
theorem uoscr_cases (op : UnconnOutPort (tmSCR Γ Λ M)) :
    op.val = ⟨0, TapeOut.window⟩ ∨ op.val = ⟨1, CtlOut.halted⟩ := by
  obtain ⟨⟨i, p⟩, hp⟩ := op
  fin_cases i
  · cases p
    · exact absurd ⟨⟨1, CtlIn.sym⟩, Or.inr rfl⟩ hp
    · exact Or.inl rfl
  · cases p
    · exact absurd ⟨⟨0, TapeIn.cmd⟩, Or.inl rfl⟩ hp
    · exact Or.inr rfl

/-- The state map of the realisation: read off the two component states. -/
def tmHS (x : rsy_SZ (tmSCR Γ Λ M)) : TMConfig Γ Λ := (x 0, x 1)

/-- The input map: read the load command off the unconnected input port. -/
def tmHI (f : rsy_IZ (tmSCR Γ Λ M)) : Option Λ :=
  f ⟨⟨1, CtlIn.load⟩, ctl_load_mem_uiscr Γ Λ M⟩

/-- The output map: read the scanned symbol and the halted flag off the boundary. -/
def tmHO (g : rsy_OZ (tmSCR Γ Λ M)) : Γ × Bool :=
  (g ⟨⟨0, TapeOut.window⟩, tape_window_mem_uoscr Γ Λ M⟩,
    g ⟨⟨1, CtlOut.halted⟩, ctl_halted_mem_uoscr Γ Λ M⟩)

/--
The reference is a homomorphic image of the coupling: the three maps collect the component states
and the boundary port values, and the two dynamics agree tick for tick.
-/
def tmRealisation : HomomorphicImageWitness (tmReference Γ Λ M) (tmResultant Γ Λ M) where
  HS := tmHS Γ Λ M
  HI := tmHI Γ Λ M
  HO := tmHO Γ Λ M
  HS_surjective := by
    intro c
    refine ⟨Fin.cases (motive := fun i => tmSZ Γ Λ i) c.1 (fun _ => c.2), ?_⟩
    rfl
  HI_surjective := fun ld => ⟨tmExtIn Γ Λ M ld, rfl⟩
  HO_surjective := by
    intro ab
    exact ⟨fun op => tmExtOutVal Γ ab.1 ab.2 op.val.1 op.val.2, rfl⟩
  preserves_transition := by
    intro x oi
    cases oi with
    | none =>
        show tmHS Γ Λ M ((tmResultant Γ Λ M).NZ x none) = _
        rw [tmResultant_NZ_none]
        rfl
    | some extIn =>
        show ((tmResultant Γ Λ M).NZ x (some extIn) 0,
            (tmResultant Γ Λ M).NZ x (some extIn) 1) = _
        rw [tmResultant_NZ_tape, tmResultant_NZ_ctl]
        rfl
  preserves_readout := by
    intro x
    show some (tmHO Γ Λ M _) = _
    dsimp only [tmHO]
    rw [tmResultant_out_window, tmResultant_out_halted]
    rfl

theorem tmReference_isHomomorphicImage :
    IsHomomorphicImage (tmReference Γ Λ M) (tmResultant Γ Λ M) :=
  ⟨tmRealisation Γ Λ M⟩

/-- The realisation is in fact an isomorphism: nothing is lost in either direction. -/
def tmRealisationIso : IsomorphismWitness (tmReference Γ Λ M) (tmResultant Γ Λ M) where
  toHomomorphicImageWitness := tmRealisation Γ Λ M
  HS_injective := by
    intro x y h
    funext i
    have h0 : x 0 = y 0 := congrArg Prod.fst h
    have h1 : x 1 = y 1 := congrArg Prod.snd h
    fin_cases i
    · exact h0
    · exact h1
  HI_injective := by
    intro f g h
    funext ip
    have hip : ip = ⟨⟨1, CtlIn.load⟩, ctl_load_mem_uiscr Γ Λ M⟩ :=
      Subtype.ext (uiscr_eq_load Γ Λ M ip)
    subst hip
    exact h
  HO_injective := by
    intro f g h
    have hw : f ⟨⟨0, TapeOut.window⟩, tape_window_mem_uoscr Γ Λ M⟩ =
        g ⟨⟨0, TapeOut.window⟩, tape_window_mem_uoscr Γ Λ M⟩ := congrArg Prod.fst h
    have hh : f ⟨⟨1, CtlOut.halted⟩, ctl_halted_mem_uoscr Γ Λ M⟩ =
        g ⟨⟨1, CtlOut.halted⟩, ctl_halted_mem_uoscr Γ Λ M⟩ := congrArg Prod.snd h
    funext op
    rcases uoscr_cases Γ Λ M op with hop | hop
    · have : op = ⟨⟨0, TapeOut.window⟩, tape_window_mem_uoscr Γ Λ M⟩ := Subtype.ext hop
      subst this; exact hw
    · have : op = ⟨⟨1, CtlOut.halted⟩, ctl_halted_mem_uoscr Γ Λ M⟩ := Subtype.ext hop
      subst this; exact hh

theorem tmResultant_isomorphic_reference :
    IsIsomorphicTo (tmReference Γ Λ M) (tmResultant Γ Λ M) :=
  ⟨tmRealisationIso Γ Λ M⟩

/-! ## The headline corollary

The coupling satisfies the dynamics-encoding fragment compiled from the reference, and by the
bi-implication that is *equivalent* to being a realisation of it — so the fragment is exactly the
conformance question, not an approximation of it.
-/

theorem tmResultant_satisfies_reference_fragment :
    SystemSatisfiesPartialDynamicsHom (tmReference Γ Λ M) (tmResultant Γ Λ M) :=
  partialDynamicsHom_of_hom (tmReference_isHomomorphicImage Γ Λ M)

theorem tmResultant_satisfies_iff_hom :
    SystemSatisfiesPartialDynamicsHom (tmReference Γ Λ M) (tmResultant Γ Λ M) ↔
      IsHomomorphicImage (tmReference Γ Λ M) (tmResultant Γ Λ M) :=
  partialDynamicsHom_iff_hom

end Realisation

/-! ## Two ticks make one Turing step

The control's readout depends on state alone, so it cannot both observe the scanned symbol and
react to it within one tick.  A machine step is therefore split across two ticks: a sense tick that
latches the table's decision and an act tick that carries it out.  This is the tick-granularity
phenomenon the paper discusses, exhibited by the machine itself.
-/

section MacroStep

variable (Γ Λ : Type) [Inhabited Γ] (M : TMTable Γ Λ)

/-- Two ticks from a sense phase perform exactly the machine step selected by the table. -/
theorem tmReference_two_ticks (t : TapeState Γ) (q q' : Λ) (w : Γ) (m : HeadMove)
    (hM : M q t.head = some (q', w, m)) :
    (tmReference Γ Λ M).NZ ((tmReference Γ Λ M).NZ (t, .sense q) (some none)) (some none) =
      (t.apply (.act w m), .sense q') := by
  simp [tmReference, CtlState.step, CtlState.cmd, TapeState.apply, hM]

/-- When the table halts, two ticks leave the tape alone and park the control in `halted`. -/
theorem tmReference_two_ticks_halt (t : TapeState Γ) (q : Λ) (hM : M q t.head = none) :
    (tmReference Γ Λ M).NZ ((tmReference Γ Λ M).NZ (t, .sense q) (some none)) (some none) =
      (t, .halted) := by
  simp [tmReference, CtlState.step, CtlState.cmd, TapeState.apply, hM]

/-- Halting is stable: no further tick moves the machine. -/
theorem tmReference_halted_stable (t : TapeState Γ) (ld : Option Λ) :
    (tmReference Γ Λ M).NZ (t, .halted) (some ld) =
      (t, CtlState.step M .halted t.head ld) := by
  simp [tmReference, CtlState.cmd, TapeState.apply]

end MacroStep

end TuringCoupling
