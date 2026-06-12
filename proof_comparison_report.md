# Proof Comparison Report: Textbook Set Theory vs. Lean Type Theory

This report compiles the analyses of the proofs of core theorems in Wayne Wymore's Model-Based Systems Engineering (MBSE) textbook against their formalizations in Lean.


## Theorem 2.25: Closure of Complete Input Trajectories

### Theorem Statement

#### Textbook Statement
> The set of complete input trajectories of a system is closed under translation and concatenation: If $Z \in \text{DSYSTEMS}$, $\{f_1, f_2\} \subseteq \text{ITZ}$, and $t \in \text{TZ}^+$, then
> $$f_1 \rightarrow t \in \text{ITZ} \quad \text{and} \quad \text{CTN}(f_1, t, f_2) \in \text{ITZ}$$

#### Lean Representation
Definitions in [Mbse/Wymore.lean](file://Mbse/Wymore.lean):
* `translate` at [Mbse/Wymore.lean:L308](file://Mbse/Wymore.lean#L308)
* `concatenate` at [Mbse/Wymore.lean:L335](file://Mbse/Wymore.lean#L335)
* `complete_trajectories_closed_under_translation` at [Mbse/Wymore.lean:L327](file://Mbse/Wymore.lean#L327)
* `complete_trajectories_closed_under_concatenation` at [Mbse/Wymore.lean:L342](file://Mbse/Wymore.lean#L342)

```lean
def translate {A : Type} (f : Time → A) (r : Time) : Time → A :=
  fun t => f (t + r)

def concatenate {A : Type} (f g : Time → A) (r : Time) : Time → A :=
  fun t => if t < r then f t else g (t - r)

def complete_trajectories_closed_under_translation {A : Type} (f : Time → A) (r : Time) : Time → A :=
  translate f r

def complete_trajectories_closed_under_concatenation {A : Type} (f g : Time → A) (r : Time) : Time → A :=
  concatenate f g r
```

### Proof Analysis

#### Textbook Proof
The textbook cites two mathematical dependencies to establish closure:
1. **Translation (Theorem A1.286)**: Proves that shifting a function $f_1 \in \text{FNS}(\text{TZ}, \text{IZ})$ by $t$ yields a function with domain $W' = \{s \mid s + t \in \text{TZ}\}$. Since the time scale $\text{TZ} = \mathbb{N}$, any shift $s + t$ is still in $\mathbb{N}$, making $W' = \text{TZ}$. Thus, the domain is preserved.
2. **Concatenation (Theorem A1.292)**: Shows that concatenating functions defined on intervals yields a function on the union of the intervals. Concatenating $f_1$ (on $V = \text{TZ}$) and $f_2$ (on $W = \text{TZ}$) at time $t$ yields a domain $\text{TZ}[0, t) \cup \{s \mid s \ge t, s - t \in \text{TZ}\} = \text{TZ}$.

Both proofs are correct and mathematically sound under set theory.

#### Lean Verification
In Lean, complete trajectories are represented as total functions of type `Time → A` (where `Time` is defined as `Nat`).
- Both `translate` and `concatenate` are defined as operations that return a function of type `Time → A`.
- Because type theory models functions as primitives rather than subset relations, the fact that these operations return terms of type `Time → A` is verified statically by the Lean compiler at compile time.
- No set-theoretic union or shifted domain existence proofs are required. The type system itself guarantees the closure property.

### Comparison Summary

| Feature | Textbook Set Theory | Lean Type Theory |
|---|---|---|
| **Representation** | Relations over Cartesian products. | First-class total functions (`Time → A`). |
| **Closure Verification** | Explicit proofs of shifted domain equations. | Trivial; handled by compiler type-checking. |
| **Computability** | Relational predicates. | Directly executable via `#eval`. |

---

## Theorem 2.29: State Trajectory is a Function (Uniqueness)

### Theorem Statement

#### Textbook Statement
> The state trajectory is a function: If $Z \in \text{DSYSTEMS}$, $f \in \text{ITZ}$, and $x \in \text{SZ}$, then $\text{STZ}(f, x) \in \text{FNS}(\text{TZ}, \text{SZ})$.

#### Lean 4 Representation
Definitions in [Mbse/Wymore.lean](file://Mbse/Wymore.lean):
* `generateStateTrajectory` at [Mbse/Wymore.lean:L155](file://Mbse/Wymore.lean#L155)
* `stateTrajectory_unique` at [Mbse/Wymore.lean:L213](file://Mbse/Wymore.lean#L213)

```lean
def generateStateTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : STZ SZ
  | 0 => s0
  | t + 1 => Z.NZ (generateStateTrajectory Z s0 f t) (f t)

theorem stateTrajectory_unique (Z : DiscreteSystem SZ IZ OZ) (f : ITZ IZ) (g : STZ SZ) (s0 : SZ)
    (h_init : g 0 = s0)
    (h_valid : IsValidStateTrajectory Z f g) :
    ∀ t, g t = generateStateTrajectory Z s0 f t := by
  intro t
  induction t with
  | zero => exact h_init
  | succ n ih =>
    rw [generateStateTrajectory_succ, h_valid n, ih]
```

### Proof Analysis

#### Textbook Proof
The textbook proves that $\text{STZ}(f, x)$ satisfies the three conditions of a function (Definition A1.155):
1. **Subset**: $\text{STZ}(f, x) \subseteq \text{TZ} \times \text{SZ}$ by construction.
2. **Totality**: For every $t \in \text{TZ}$, there exists a state $y \in \text{SZ}$.
3. **Single-valuedness**: Proven by induction on $t$:
   - *Base Case* ($t = 0$): $y_1 = x = y_2$.
   - *Inductive Step*: Assumes $y_1 = y_2$ for $t$. For $t+1$, they both map to $\text{NZ}(\text{STZ}(f,x)(t), f(t))$, which must yield the same state because inputs and previous states are equal.

#### Lean Verification
In dependent type theory, function well-formedness (totality and single-valuedness) is guaranteed by design:
- The recursion engine checks that `generateStateTrajectory` terminates and covers all cases of the `Time` (natural number) domain. Thus, the function is total and single-valued by construction.
- The theorem `stateTrajectory_unique` serves as the formal equivalent of Wymore's single-valuedness proof. It shows that any function `g` satisfying the recurrence relation is pointwise equal to the generated state trajectory.
- The proof uses structural induction on `t`. The base case is resolved by `h_init`. The inductive step rewrites the recurrence equation and applies the induction hypothesis `ih` to close the goal.

### Comparison Summary

| Feature | Textbook Set Theory | Lean Type Theory |
|---|---|---|
| **Totality** | Set-theoretic existence proof. | Guaranteed by recursion checking. |
| **Single-valuedness** | Proved inductively over domain coordinates. | Structural induction showing equality to the unique generator. |
| **Well-formedness** | Required to be proven explicitly. | Embedded in the compiler's type system. |

---

## Theorem 2.32: Output Trajectory is a Function (Composition)

### Theorem Statement

#### Textbook Statement
> The output trajectory is a function: If $Z \in \text{DSYSTEMS}$, $f \in \text{ITZ}$, $x \in \text{SZ}$, and $t \in \text{TZ}$, then $\text{OTZ}(f, x) \in \text{FNS}(\text{TZ}, \text{OZ})$ and $\text{OTZ}(f, x)(t) = \text{RZ}(\text{STZ}(f, x)(t))$.

#### Lean 4 Representation
Definitions in [Mbse/Wymore.lean](file://Mbse/Wymore.lean):
* `generateOutputTrajectory` at [Mbse/Wymore.lean:L165](file://Mbse/Wymore.lean#L165)

```lean
def generateOutputTrajectory (Z : DiscreteSystem SZ IZ OZ) (s0 : SZ) (f : ITZ IZ) : OTZ OZ :=
  fun t => Z.RZ (generateStateTrajectory Z s0 f t)
```

### Proof Analysis

#### Textbook Proof
The textbook proof states:
> That $\text{OTZ}(f, x) \in \text{FNS}(\text{TZ}, \text{OZ})$ is a consequence of the facts that $\text{RZ} \in \text{FNS}(\text{SZ}, \text{OZ})$, by the definition at 2.4, and that $\text{STZ}(f, x) \in \text{FNS}(\text{TZ}, \text{SZ})$, by the theorems at 2.29 and A1.249. That $\text{OTZ}(f, x)(t) = \text{RZ}(\text{STZ}(f, x)(t))$ is a consequence of the theorem at A1.250.

**Erratum**:
The textbook references **Theorems A1.249** and **A1.250** to justify function composition. However:
- **Theorem A1.249** defines $f(f^{-1}(C)) \subseteq C$ (image of preimage inclusion).
- **Theorem A1.250** defines $f^{-1}(B - C) = A - f^{-1}(C)$ (preimage of a complement).

These theorems concern set images/preimages and complements, not function composition. This is a clear cross-reference numbering error in the original textbook. The correct citation should have referred to set-theoretic composition lemmas (such as Definition A1.268).

#### Lean Verification
In type theory, function composition is natively defined:
- `Z.RZ` has type `SZ → OZ`.
- `generateStateTrajectory Z s0 f` has type `Time → SZ`.
- The composition `fun t => Z.RZ (generateStateTrajectory Z s0 f t)` is immediately verified by the type checker to have type `Time → OZ` (representing complete output trajectories).
- The value equation is definitionally true and proven by reflexivity (`rfl`). No lemmas are needed.

### Comparison Summary

| Feature | Textbook Set Theory | Lean Type Theory |
|---|---|---|
| **Composability** | Requires set relation composition theorems. | Handled automatically by function application typing rules. |
| **Pointwise Identity** | Proved via set-complements (cited erroneously). | Definitionally true by computation (`rfl`). |
| **Correctness** | Contains a cross-referencing erratum. | Verified type-safe by compiler compilation. |

---

## Theorem 2.46: Time Invariance of State Trajectory

### Theorem Statement

#### Textbook Statement
> If $Z \in \text{DSYSTEMS}$, $f \in \text{ITZ}$, $x \in \text{SZ}$, and $\{s, t\} \subseteq \text{TZ}$, then:
> $$\text{STZ}(f \rightarrow s, \text{STZ}(f, x)(s))(t) = \text{STZ}(f, x)(s + t)$$

#### Lean Representation
Definitions in [Mbse/Wymore.lean](file://Mbse/Wymore.lean):
* `stateTrajectory_time_invariance` at [Mbse/Wymore.lean:L407](file://Mbse/Wymore.lean#L407)

```lean
theorem stateTrajectory_time_invariance
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f : ITZ IZ) (s t : Time) :
    generateStateTrajectory Z (generateStateTrajectory Z x f s) (translate f s) t =
    generateStateTrajectory Z x f (s + t) := by
  induction t with
  | zero =>
    simp only [generateStateTrajectory_zero, Nat.add_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [ih]
    unfold translate
    congr 2
    exact Nat.add_comm t s
```

### Proof Analysis

#### Textbook Proof
The textbook employs a double induction strategy:
1. **Base Case $s = 0$**: Proves the statement for all $t$ when $s=0$.
2. **First Induction (on $t$, for $s = 1$)**:
   - Base case $t=0$: proven directly.
   - Inductive step: Assumes the theorem holds for $s=1$ and all $t \le n$. Proves for $n+1$ using the state trajectory recurrence relation and the definition of translation.
3. **Second Induction (on $s$, for all $t$)**:
   - Assumes the theorem holds for all $t$ and all $s \le n$.
   - For $s = n+1$, unfolds the translation $(f \rightarrow n) \rightarrow 1$ using **Theorem A1.288** (translation composition) and applies the induction hypotheses for $n$ and $1$.

Wymore's proof is correct but complex, due to the need to prove translation compositions step-by-step over relational shifts.

#### Lean Verification
Lean collapses Wymore's double induction into a single induction on $t$ that generalizes over all $s$:
- **Base Case (`zero`)**: Both sides simplify definitionally to the state at time $s$. Closed automatically.
- **Inductive Step (`succ`)**: Unfolds the successor step on both sides. Rewriting with the induction hypothesis `ih` leaves the input terms to prove: `translate f s t = f (s + t)`. By definition of `translate`, this reduces to `f (t + s) = f (s + t)`. This is resolved directly using the commutativity of natural number addition: `Nat.add_comm t s`.

### Comparison Summary

| Feature | Textbook Set Theory | Lean Type Theory |
|---|---|---|
| **Induction Strategy** | Double induction (first on $t$ for $s=1$, then on $s$). | Single induction on $t$ (generalizing over all $s$). |
| **Dependencies** | Theorem A1.288 (composition of translations). | Bypassed; uses `Nat.add_comm` instead. |
| **Proof Length** | Long; multiple pages. | Short; 10 lines of Lean code. |

---

## Theorem 2.48: Nonanticipatory Theorem

### Theorem Statement

#### Textbook Statement
> If $Z \in \text{DSYSTEMS}$, $\{(f, x, t), (g, x, t)\} \subseteq \text{EXZ}$ and
> $\text{RSN}(f, \text{TZ}[0, t)) = \text{RSN}(g, \text{TZ}[0, t))$,
>
> then
>
> $\text{STZ}(f, x)(t) = \text{STZ}(g, x)(t)$.

#### Lean 4 Representation
Definitions in [Mbse/Wymore.lean](file://Mbse/Wymore.lean):
* `RSN` at [Mbse/Wymore.lean:L434](file://Mbse/Wymore.lean#L434)
* `rsn_eq_iff` at [Mbse/Wymore.lean:L441](file://Mbse/Wymore.lean#L441)
* `stateTrajectory_nonanticipatory` at [Mbse/Wymore.lean:L456](file://Mbse/Wymore.lean#L456)

```lean
def RSN {A B : Type} (f : A → B) (S : Set A) : {a : A // a ∈ S} → B :=
  fun ⟨a, _⟩ => f a

theorem rsn_eq_iff {A B : Type} (f g : A → B) (S : Set A) :
    RSN f S = RSN g S ↔ ∀ a ∈ S, f a = g a

theorem stateTrajectory_nonanticipatory
    (Z : DiscreteSystem SZ IZ OZ) (x : SZ) (f g : ITZ IZ) (t : Time)
    (h_agree : RSN f {i | i < t} = RSN g {i | i < t}) :
    generateStateTrajectory Z x f t = generateStateTrajectory Z x g t := by
  induction t with
  | zero =>
    simp only [generateStateTrajectory_zero]
  | succ t ih =>
    simp only [generateStateTrajectory_succ]
    rw [rsn_eq_iff] at h_agree
    have h_lt : ∀ i < t, f i = g i := by
      intro i hi
      exact h_agree i (Nat.lt_trans hi (Nat.lt_succ_self t))
    have h_eq : f t = g t := by
      exact h_agree t (Nat.lt_succ_self t)
    have h_rsn_t : RSN f {i | i < t} = RSN g {i | i < t} := by
      rw [rsn_eq_iff]
      exact h_lt
    rw [ih h_rsn_t, h_eq]
```

### Proof Analysis

#### Textbook Proof
The textbook employs strong induction on the time variable $t$:
- *Base Case* ($t = 0$): $\text{STZ}(f, x)(0) = x = \text{STZ}(g, x)(0)$ by definition.
- *Inductive Step*: Assumes the theorem is true for all $t \le n$. For $n+1$, under the hypothesis $\text{RSN}(f, \text{TZ}[0, n+1)) = \text{RSN}(g, \text{TZ}[0, n+1))$, it deduces:
  1. $\text{RSN}(f, \text{TZ}[0, n)) = \text{RSN}(g, \text{TZ}[0, n))$
  2. $f(n) = g(n)$
  
  Applying the induction hypothesis at $n$ yields $\text{STZ}(f, x)(n) = \text{STZ}(g, x)(n)$. Combining this with $f(n) = g(n)$ inside the state transition function $\text{NZ}$ proves the theorem for $n+1$.

#### Lean Verification
Lean simplifies the induction strategy from strong induction to **standard mathematical induction** (`induction t`):
- **Base Case (`zero`)**: Trivially holds as both sides reduce to `x`.
- **Inductive Step (`succ`)**:
  - We use `rsn_eq_iff` to convert the subtype function restriction equality `RSN f {i | i < succ t} = RSN g {i | i < succ t}` into pointwise agreement: `∀ i < succ t, f i = g i`.
  - From this, we extract:
    1. Agreement on the predecessor interval: `∀ i < t, f i = g i` (since $i < t \implies i < t + 1$).
    2. Agreement at the boundary: `f t = g t` (since $t < t+1$).
  - We reconstruct the restriction equality for the predecessor interval, `RSN f {i | i < t} = RSN g {i | i < t}`, using `rsn_eq_iff`.
  - Applying the standard induction hypothesis `ih` yields equality of the states at time `t`.
  - Substituting the equal states and equal boundary inputs `f t = g t` into `Z.NZ` completes the proof.

Standard induction suffices because the transition relation is a first-order recurrence, depending only on the state and input at the immediate predecessor step.

### Comparison Summary

| Feature | Textbook Set Theory | Lean Type Theory |
|---|---|---|
| **Induction Type** | Strong induction (all $t \le n$). | Standard induction (predecessor $t$). |
| **Restriction Model** | Relation subset $f \cap (S \times B)$. | Subtype-restricted function mapping. |
| **Interval Shifting** | Set union separation of $\text{TZ}[0, n+1)$. | Pointwise separation via inequality cases. |

---
