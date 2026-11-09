import Mbse.LSC
import Mbse.DocExport
import Mbse.WymoreCore

/-!
# Drawable LSC presentations for techdoc export

Techdoc derive builds `LscDoc` by recovering the envelope law from `functionalIOR ψ`
and evaluating a computable `ψ` (or `ψ_eval` twin) on a default presentation-window
sample policy.  Figures are finite windows into (often infinite) `ITR`.
-/

namespace Mbse.LscPresentation

open LSC
open Mbse.DocExport

/-- Temperature as export string. -/
def tempStr : Temperature → String
  | .cold => "cold"
  | .hot => "hot"

/-- Serialize a diagrammatic element using `Repr` for concrete payloads. -/
def elementToDoc {IR OR : Type} [Repr IR] [Repr OR] : Element IR OR → LscElementDoc
  | .inMsg t tick v =>
    { kind := "inMsg", temp := tempStr t, tick := some tick, value := reprStr v }
  | .outMsg t tick v =>
    { kind := "outMsg", temp := tempStr t, tick := some tick, value := reprStr v }
  | .outSymbolic t tick binder =>
    { kind := "outSymbolic", temp := tempStr t, tick := some tick, value := binder }
  | .condition t tick label =>
    { kind := "condition", temp := tempStr t, tick := tick, label := label }
  | .tickSync tick =>
    { kind := "tickSync", tick := some tick }
  | .silenceOut t tick =>
    { kind := "silenceOut", temp := tempStr t, tick := some tick }

def chartBodyToDocs {IR OR : Type} [Repr IR] [Repr OR] (b : ChartBody IR OR) :
    List LscElementDoc :=
  b.elements.map elementToDoc

/-- Lean-side presentation: law + named chart bodies. -/
structure Presentation (IR OR : Type) where
  law : String
  horizonNote : String := "presentation window (not full ITR coverage)"
  chartName : String := ""
  preCondition : String := ""
  mainCondition : String := ""
  paths : List (String × ChartBody IR OR) := []

/-- Build a synchronous path body: cold `in`, tick sync, hot `out` per tick, then law. -/
def syncPathBody {IR OR : Type} (n : Nat) (law : String)
    (inp : Fin n → IR) (out : Fin n → OR) : ChartBody IR OR where
  elements :=
    (List.finRange n).flatMap (fun t =>
      [ Element.inMsg .cold t.val (inp t)
      , Element.tickSync t.val
      , Element.outMsg .hot t.val (out t) ]) ++
      [Element.condition .hot none law]

/-- Convert a presentation into the JSON-facing `LscDoc`. -/
def toLscDoc {IR OR : Type} [Repr IR] [Repr OR] (p : Presentation IR OR)
    (iorName : String) (ir : String) (or_ : String) : LscDoc :=
  let pathDocs : List LscPathDoc :=
    p.paths.map fun ⟨id, body⟩ => { id := id, elements := chartBodyToDocs body }
  let primary := pathDocs.head?.map (·.elements) |>.getD []
  { chartName := if p.chartName.isEmpty then s!"LSC_{iorName}" else p.chartName
    preCondition :=
      if p.preCondition.isEmpty then s!"f ∈ {iorName}.itr" else p.preCondition
    mainCondition :=
      if p.mainCondition.isEmpty then p.law else p.mainCondition
    inMessage := s!"in(f(t)) : {ir}"
    outMessage := s!"out(g(t)) : {or_}"
    law := p.law
    horizonNote := p.horizonNote
    elements := primary
    paths := pathDocs
    fromPresentation := true }

/-- Truncate long `Repr` strings for figure labels. -/
def abbrevLabel (s : String) (maxLen : Nat := 56) : String :=
  if s.length ≤ maxLen then s
    else String.ofList (s.toList.take (maxLen - 3)) ++ "..."

/-- String-labelled path (no `Repr` required): triples `(tick, inValue, outValue)`. -/
def syncPathDocs (law : String) (ticks : List (Nat × String × String)) :
    List LscElementDoc :=
  ticks.flatMap (fun ⟨t, inp, out⟩ =>
    [ { kind := "inMsg", temp := "cold", tick := some t, value := abbrevLabel inp }
    , { kind := "tickSync", tick := some t }
    , { kind := "outMsg", temp := "hot", tick := some t, value := abbrevLabel out } ]) ++
    [ { kind := "condition", temp := "hot", label := law } ]

/-- Assemble `LscDoc` from string-labelled paths. -/
def lscDocFromStringPaths (iorName ir or_ law horizonNote : String)
    (paths : List (String × List (Nat × String × String))) : LscDoc :=
  let pathDocs : List LscPathDoc :=
    paths.map fun ⟨id, ticks⟩ => { id := id, elements := syncPathDocs law ticks }
  let primary := pathDocs.head?.map (·.elements) |>.getD []
  { chartName := s!"LSC_{iorName}"
    preCondition := s!"f ∈ {iorName}.itr"
    mainCondition := law
    inMessage := s!"in(f(t)) : {ir}"
    outMessage := s!"out(g(t)) : {or_}"
    law := law
    horizonNote := horizonNote
    elements := primary
    paths := pathDocs
    fromPresentation := true }

/-- Pad a finite Bool list to an infinite trajectory. -/
def boolTraj (vals : List Bool) (default : Bool := false) : ITZ Bool :=
  fun t => vals.getD t default

/-- Default Bool presentation prefixes for horizon `H`. -/
def defaultBoolPrefixes (H : Nat) : List (String × List Bool) :=
  let pad (b : Bool) : List Bool := List.replicate H b
  let pulse : List Bool :=
    (List.range H).map fun t => decide (1 ≤ t ∧ t ≤ 2)
  let alt : List Bool :=
    (List.range H).map fun t => decide (t % 2 = 0)
  [ ("const_false", pad false)
  , ("pulse", if H = 0 then [] else pulse)
  , ("alt", if H = 0 then [] else alt) ]

/--
  Evaluate a Bool→OR envelope on default presentation samples.
  `ψ` must be computable (or a proven eval twin).
-/
def lscDocFromBoolPsi {OR : Type} [Repr OR]
    (iorName orName ψName : String) (H : Nat)
    (ψ : ITZ Bool → ITZ OR) : LscDoc :=
  let law := s!"g = {ψName} f"
  let note :=
    s!"presentation window t in 0..{if H = 0 then 0 else H - 1} (ITR is infinite; default Bool samples)"
  let paths : List (String × List (Nat × String × String)) :=
    (defaultBoolPrefixes H).map fun ⟨id, vals⟩ =>
      let f := boolTraj vals
      let ticks :=
        (List.range H).map fun t =>
          (t, reprStr (f t), reprStr (ψ f t))
      (id, ticks)
  lscDocFromStringPaths iorName "Bool" orName law note paths

/--
  Large / non-Bool alphabets: one constant-`default` presentation path.
  Not an ITR enumeration — labeled as such in `horizonNote`.
-/
def lscDocFromInhabitedPsi {IR OR : Type} [Repr IR] [Repr OR] [Inhabited IR]
    (iorName ir or_ ψName : String) (H : Nat)
    (ψ : ITZ IR → ITZ OR) : LscDoc :=
  let law := s!"g = {ψName} f"
  let note :=
    s!"presentation window t in 0..{if H = 0 then 0 else H - 1} (ITR is infinite; Inhabited default sample)"
  let f : ITZ IR := fun _ => default
  let ticks :=
    (List.range H).map fun t =>
      (t, reprStr (f t), reprStr (ψ f t))
  lscDocFromStringPaths iorName ir or_ law note [("const_default", ticks)]

/--
  Large alphabets with an explicit finite stim prefix (primary path) plus the
  Inhabited-default idle path.  Consumer packages export `{ψ}_lsc_prefix : List IR`.
-/
def lscDocFromPrefixPsi {IR OR : Type} [Repr IR] [Repr OR] [Inhabited IR]
    (iorName ir or_ ψName : String) (stimPrefix : List IR)
    (ψ : ITZ IR → ITZ OR) : LscDoc :=
  let law := s!"g = {ψName} f"
  let H := stimPrefix.length
  let note :=
    s!"presentation window t in 0..{if H = 0 then 0 else H - 1} (ITR is infinite; coupled stim + Inhabited default)"
  let fStim : ITZ IR := fun t => stimPrefix.getD t default
  let stimTicks :=
    (List.range H).map fun t =>
      (t, reprStr (fStim t), reprStr (ψ fStim t))
  let idleH := if H = 0 then 4 else min H 4
  let fIdle : ITZ IR := fun _ => default
  let idleTicks :=
    (List.range idleH).map fun t =>
      (t, reprStr (fIdle t), reprStr (ψ fIdle t))
  lscDocFromStringPaths iorName ir or_ law note
    [("coupled_stim", stimTicks), ("const_default", idleTicks)]

/-- Schematic characteristic when ψ cannot be evaluated. -/
def schematicLscDoc (iorName ir or_ : String) (law : String := "g ∈ er f") : LscDoc where
  chartName := s!"LSC_{iorName}"
  preCondition := s!"f ∈ {iorName}.itr"
  mainCondition := if law.isEmpty then s!"g ∈ {iorName}.er f" else law
  inMessage := s!"in(f(t)) : {ir}"
  outMessage := s!"out(g(t)) : {or_}"
  law := law
  horizonNote := "schematic characteristic only (no evaluable presentation window)"
  elements := []
  paths := []
  fromPresentation := false

end Mbse.LscPresentation
