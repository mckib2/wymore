import Lean
import Mbse.Wymore
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Lean Elab Command Term Meta

syntax (name := wymore_system_cmd)
  "wymore_system" ident "=" "(" ident "," ident "," ident "," ident "," ident ")" "where"
  ident "=" "{" term,* "},"
  ident "=" "{" term,* "},"
  ident "=" "{" term,* "},"
  ident "=" "{" term,* "},"
  ident "=" "{" term,* "}."
  : command

@[command_elab wymore_system_cmd]
def elabWymoreSystem : CommandElab := fun stx => do
  match stx with
  | `(command| wymore_system $sysName:ident = ($szName:ident, $izName:ident, $ozName:ident, $nzName:ident, $rzName:ident) where
        $szName2:ident = { $szElems:term,* },
        $izName2:ident = { $izElems:term,* },
        $ozName2:ident = { $ozElems:term,* },
        $nzName2:ident = { $nzPairs:term,* },
        $rzName2:ident = { $rzPairs:term,* }.) => do

    let _ := (szName2, izName2, ozName2, nzName2, rzName2)

    let toCtorName (s : Syntax) : Name :=
      let str := (s.reprint.getD "val" |>.trimAscii).toString
      Name.mkSimple ("v" ++ str.replace "(" "_" |>.replace ")" "_" |>.replace "," "_" |>.replace " " "")

    let szCtors := szElems.getElems.map (fun e => mkIdent (toCtorName e))
    let izCtors := izElems.getElems.map (fun e => mkIdent (toCtorName e))
    let ozCtors := ozElems.getElems.map (fun e => mkIdent (toCtorName e))

    elabCommand (← `(command| inductive $szName:ident where $[| $szCtors:ident]* deriving Fintype, DecidableEq, Repr))
    elabCommand (← `(command| inductive $izName:ident where $[| $izCtors:ident]* deriving Fintype, DecidableEq, Repr))
    elabCommand (← `(command| inductive $ozName:ident where $[| $ozCtors:ident]* deriving Fintype, DecidableEq, Repr))

    let mut nzS := #[]
    let mut nzI := #[]
    let mut nzNext := #[]
    for pair in nzPairs.getElems do
      match pair with
      | `(term| (($s, $i), $sNext)) =>
          nzS := nzS.push (mkIdent (szName.getId ++ toCtorName s))
          nzI := nzI.push (mkIdent (izName.getId ++ toCtorName i))
          nzNext := nzNext.push (mkIdent (szName.getId ++ toCtorName sNext))
      | _ => throwErrorAt pair "Invalid NZ pair format. Expected ((s, i), s')"

    elabCommand (← `(command| def $nzName:ident (s : $szName:ident) (i : $izName:ident) : $szName:ident :=
      match s, i with
      $[| $nzS:ident, $nzI:ident => $nzNext:ident]*))

    let mut rzS := #[]
    let mut rzO := #[]
    for pair in rzPairs.getElems do
      match pair with
      | `(term| ($s, $o)) =>
          rzS := rzS.push (mkIdent (szName.getId ++ toCtorName s))
          rzO := rzO.push (mkIdent (ozName.getId ++ toCtorName o))
      | _ => throwErrorAt pair "Invalid RZ pair format. Expected (s, o)"

    elabCommand (← `(command| def $rzName:ident (s : $szName:ident) : $ozName:ident :=
      match s with
      $[| $rzS:ident => $rzO:ident]*))

    if szElems.getElems.isEmpty then throwErrorAt szName "State set SZ cannot be empty"
    let firstSz := szElems.getElems[0]!
    let firstSzCtor := mkIdent (szName.getId ++ toCtorName firstSz)

    elabCommand (← `(command| def $sysName:ident : DiscreteSystem $szName:ident $izName:ident $ozName:ident := {
      sz_nonempty := ⟨$firstSzCtor:ident⟩,
      sz_finite := inferInstance,
      iz_finite := inferInstance,
      oz_finite := inferInstance,
      NZ := $nzName:ident,
      RZ := $rzName:ident
    }))

  | _ => throwUnsupportedSyntax
