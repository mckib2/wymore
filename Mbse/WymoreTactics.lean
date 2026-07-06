import Mbse.WymoreSimp

/-!
# Wymore proof tactics

Macro tactics wrapping the lemma library in [`Trajectory`](Trajectory.lean).
See [`LTLTactics`](LTLTactics.lean) for clause-satisfaction helpers.
-/

open Lean Parser Tactic

/-- `wymore_trajectory_induction` runs standard induction on trajectory time. -/
syntax (name := wymoreTrajectoryInduction) "wymore_trajectory_induction" : tactic

macro_rules
  | `(tactic| wymore_trajectory_induction) =>
    `(tactic| intro t; induction t with
      | zero => simp [generateStateTrajectory_zero]
      | succ n ih => simp [generateStateTrajectory_succ])

/-- `wymore_output_of_state h` rewrites an output goal using a state trajectory lemma. -/
syntax (name := wymoreOutputOfState) "wymore_output_of_state " rwRule : tactic

macro_rules
  | `(tactic| wymore_output_of_state $h:rwRule) =>
    `(tactic| unfold generateOutputTrajectory; rw [$h])

/-- `wymore_card_rng` closes the varying-output ↔ `RNG` cardinality equivalence. -/
syntax (name := wymoreCardRng) "wymore_card_rng" : tactic

macro_rules
  | `(tactic| wymore_card_rng) =>
    `(tactic| exact Trajectory.varyingOutput_iff_card_rng)

/-- `wymore_simp` runs the `@[wymore]` simp set. -/
syntax (name := wymoreSimp) "wymore_simp" : tactic

macro_rules
  | `(tactic| wymore_simp) =>
    `(tactic| simp only [wymore])

set_option hygiene false

private def eraseMacroScopesRec (stx : Syntax) : Syntax :=
  stx.replaceM (m := Id) fun stx =>
    match stx with
    | Syntax.ident _ _ val _ =>
      some (mkIdent val.eraseMacroScopes).raw
    | _ => none

/--
`dpda_step_destruct D, snap, inp, q, s, q_new, new_top` destructs a
DPDA snapshot `snap` into its state `q` and stack `s`, then generalises the
transition `D.F q inp (peek D.z0 s)` as hypothesis `hF` and case-splits
the result into `none` (first goal) and `some (q_new, new_top)` (second goal).
-/
syntax (name := dpdaStepDestruct)
  "dpda_step_destruct" ident "," term "," term ","
    ident "," ident "," ident "," ident : tactic

macro_rules
  | `(tactic| dpda_step_destruct $d:ident , $snap:term , $inp:term ,
      $q:ident , $s:ident , $q_new:ident , $new_top:ident) => do
    let dClean : TSyntax `ident := ⟨eraseMacroScopesRec d.raw⟩
    let snapClean : TSyntax `term := ⟨eraseMacroScopesRec snap.raw⟩
    let inpClean : TSyntax `term := ⟨eraseMacroScopesRec inp.raw⟩
    let qBind : TSyntax `ident := ⟨(mkIdent q.getId.eraseMacroScopes).raw⟩
    let sBind : TSyntax `ident := ⟨(mkIdent s.getId.eraseMacroScopes).raw⟩
    let q_newBind : TSyntax `ident := ⟨(mkIdent q_new.getId.eraseMacroScopes).raw⟩
    let new_topBind : TSyntax `ident := ⟨(mkIdent new_top.getId.eraseMacroScopes).raw⟩
    let t1 ← `(tactic| obtain ⟨$qBind, $sBind⟩ := $snapClean)
    let t2 ← `(tactic| generalize hF : ($dClean).F $qBind $inpClean (DPDA.peek ($dClean).z0 $sBind) = v)
    let t3 ← `(tactic| rcases v with _ | ⟨$q_newBind, $new_topBind⟩)
    `(tactic| ($t1; $t2; $t3))
