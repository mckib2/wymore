import Mathlib.Data.Fintype.Basic

/--
  Formalization of Wayne Wymore's Tricotyledon Theory of System Design (T3SD)
-/

/-
  A Wymorian Discrete System: Z = (SZ, IZ, OZ, NZ, RZ)
  - SZ must be non-empty (enforced by the sz_nonempty proof).
  - IZ and OZ can be standard types, or 'Unit' for closed systems.
  - SZ, IZ, and OZ are assumed to be finite for discrete systems.
-/
structure DiscreteSystem (SZ : Type) (IZ : Type) (OZ : Type) where
    /-- Proof that the state space is not empty -/
    sz_nonempty : Nonempty SZ

    /-- Proof that the state space is finite -/
    sz_finite : Fintype SZ

    /-- Proof that the input space is finite -/
    iz_finite : Fintype IZ

    /-- Proof that the output space is finite -/
    oz_finite : Fintype OZ

    /-- Next State Function: takes a state and an input, returns a new state -/
    NZ : SZ → IZ → SZ

    /-- Readout Function: takes a state, returns an output -/
    RZ : SZ → OZ

-- Define Time as an alias for Natural Numbers
abbrev Time := Nat

-- We use variables here so we don't have to rewrite {SZ IZ OZ} for every definition
variable {SZ IZ OZ : Type}

-- The set of all possible Input Trajectories
abbrev ITZ (IZ : Type) := Time → IZ

-- The set of all possible State Trajectories
abbrev STZ (SZ : Type) := Time → SZ

-- The set of all possible Output Trajectories
abbrev OTZ (OZ : Type) := Time → OZ

/-- Generates the state trajectory given a system, an initial state, and an input trajectory -/
def generateStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : STZ SZ
  | 0 => s0                                      -- At time 0, state is s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)  -- At time t+1, apply NZ to the state at time t and input at time t

/-- Generates the output trajectory based on the state trajectory -/
def generateOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : OTZ OZ :=
  -- For any time t, apply RZ to whatever the state is at time t
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)

/--
  A logical predicate defining what it means for an arbitrary function 'g'
  to be a valid state trajectory for input trajectory 'f'.
-/
def IsValidStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) : Prop :=
  ∀ t : Time, g (t + 1) = Z.NZ (g t) (f t)

/--
  A logical predicate defining what it means for an arbitrary function 'h'
  to be a valid output trajectory for state trajectory 'g'.
-/
def IsValidOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (g : STZ SZ) (h : OTZ OZ) : Prop :=
  ∀ t : Time, h t = Z.RZ (g t)
