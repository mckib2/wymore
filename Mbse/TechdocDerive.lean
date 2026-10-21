import Lean
import Mbse.DocExport
import Mbse.TechdocAttr

/-!
# Derive `IsrPackageDoc` from `@[techdoc]` ISR roots

Walks elaborated `Expr` values (technology set literals, CSCR wires, cell aliases)
to fill the JSON DTO consumed by `scripts/techdoc`.
-/

open Lean Meta Core
open Mbse.DocExport
open Mbse.TechdocAttr

namespace Mbse.TechdocDerive

def throwDerive {α : Type} (msg : String) : MetaM α :=
  throwError msg

/-- Hierarchical name without requiring the constant to exist. -/
def n! (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) fun n p => Name.str n p

def nm_Technology := n! "WymoreTechnology.Technology"
def nm_Technology_mk := n! "WymoreTechnology.Technology.mk"
def nm_AnyOf := n! "WymoreTechnology.AnyDiscreteSystem.of"
def nm_AnyOfNamed := n! "WymoreTechnology.AnyDiscreteSystem.ofNamed"
def nm_SCR := n! "Mbse.Wymore.SystemCouplingRecipe"
def nm_SCR' := n! "SystemCouplingRecipe"
def nm_IOR := n! "WymoreRequirements.InputOutputRequirement"
def nm_IOR' := n! "InputOutputRequirement"
def nm_FSD := n! "WymoreRequirements.FunctionalSystemDesign"
def nm_functionalIOR := n! "IORTemporalFragment.functionalIOR"
def nm_olr_infinite := n! "WymoreRequirements.OperationalLength.infinite"
def nm_olr_finite := n! "WymoreRequirements.OperationalLength.finite"
def nm_Insert := ``Insert.insert
def nm_Singleton := ``Singleton.singleton
def nm_empty := ``EmptyCollection.emptyCollection
def nm_insert := ``insert
def nm_singleton := ``singleton
def nm_Prod_mk := ``Prod.mk
def nm_Subtype_mk := ``Subtype.mk

/-- Unfold a constant’s value once (definition body). -/
def constValue? (n : Name) : MetaM (Option Expr) := do
  let env ← getEnv
  match env.find? n with
  | some (.defnInfo d) => return some d.value
  | some (.thmInfo t) => return some t.value
  | _ => return none

partial def strip (e : Expr) : Expr :=
  e.consumeMData

/-- Dig for a natural number literal inside Fin/OfNat noise. -/
partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app f a => natLit? a <|> natLit? f
  | .mdata _ e => natLit? e
  | .proj _ _ e => natLit? e
  | _ => none

/-- Peel `fun x => x = a ∨ x = b ∨ …` (or nested Or/Eq) into element exprs. -/
partial def setElementsFromPred (pred : Expr) : MetaM (Array Expr) := do
  let pred := strip pred
  match pred with
  | .lam _ _ body _ => setElementsFromPred body
  | _ =>
    if pred.isAppOf ``Or then
      let args := pred.getAppArgs
      if args.size < 2 then
        throwDerive s!"Or predicate: too few args\n{pred}"
      let left ← setElementsFromPred args[args.size - 2]!
      let right ← setElementsFromPred args[args.size - 1]!
      return left ++ right
    else if pred.isAppOf ``Eq then
      let args := pred.getAppArgs
      if args.size < 2 then
        throwDerive s!"Eq predicate: too few args\n{pred}"
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!
      if lhs.isFVar || lhs.isBVar then
        return #[rhs]
      else if rhs.isFVar || rhs.isBVar then
        return #[lhs]
      else
        return #[rhs]
    else
      throwDerive s!"unsupported set predicate shape:\n{pred}"

/--
Walk a set/insert/singleton literal into element exprs.

Important: do **not** `whnf` set expressions — that reduces `{a, b}` to predicates
`fun x => x = a ∨ …`. Instead unfold named aliases one level, and accept both
`Insert`/`Singleton` and `setOf (fun x => x = c)` / `Or` shapes.
-/
partial def setElements (e : Expr) : MetaM (Array Expr) := do
  let e0 := strip e
  let e ←
    match e0.getAppFn.constName? with
    | some c =>
      if e0.isConst then
        if let some v ← constValue? c then pure (strip v) else pure e0
      else pure e0
    | none => pure e0
  if e.isAppOfArity nm_empty 2 then
    return #[]
  else if e.isAppOf nm_Singleton || e.isAppOf nm_singleton then
    return #[e.getAppArgs.back!]
  else if e.isAppOf nm_Insert || e.isAppOf nm_insert then
    let args := e.getAppArgs
    if args.size < 2 then
      throwDerive s!"Insert: too few args ({args.size})"
    let elem := args[args.size - 2]!
    let rest := args[args.size - 1]!
    -- Preserve surface order: `{a, b}` = Insert a {b} → [a, b]
    return #[elem] ++ (← setElements rest)
  else if e.isAppOf (n! "setOf") || e.isAppOf (n! "Set.setOf") then
    setElementsFromPred e.getAppArgs.back!
  else if e.isLambda then
    setElementsFromPred e
  else
    throwDerive s!"unsupported set literal shape:\n{e}"

/-- Peel `AnyDiscreteSystem.of` / `ofNamed` to the component constant name. -/
def componentConstOfAny? (e : Expr) : Option Name :=
  let e := strip e
  if e.isAppOf nm_AnyOf || e.isAppOf nm_AnyOfNamed then
    e.getAppArgs.back?.bind fun a => a.getAppFn.constName?
  else
    e.getAppFn.constName?

/-- Extract technology member names from a `Technology` definition. -/
def technologyMembers (tyr : Name) : MetaM (Array String) := do
  let some val ← constValue? tyr
    | throwDerive s!"technology `{tyr}` has no value"
  -- Do not `whnf` — that reduces set literals to predicates.
  let carrier? : Option Expr :=
    if val.isAppOf nm_Technology_mk then
      val.getAppArgs[0]?
    else if val.isAppOf nm_Subtype_mk then
      let args := val.getAppArgs
      if args.size ≥ 2 then some args[args.size - 2]! else none
    else
      let args := val.getAppArgs
      if args.isEmpty then none else some args[0]!
  let some carrier := carrier?
    | throwDerive s!"cannot find technology carrier in `{tyr}`:\n{val}"
  let elems ← setElements carrier
  let mut names : Array String := #[]
  for el in elems do
    match componentConstOfAny? el with
    | some c => names := names.push (shortName c)
    | none => throwDerive s!"technology element is not AnyDiscreteSystem.of <const>:\n{el}"
  return names

/-- Extract `n` from type `SystemCouplingRecipe n`. -/
def scrArity (scrTy : Expr) : MetaM Nat := do
  let ty ← whnf scrTy
  let head := ty.getAppFn.constName?
  if head == some nm_SCR || head == some nm_SCR' || head.map shortName == some "SystemCouplingRecipe" then
    match ty.getAppArgs.back?.bind natLit? with
    | some n => return n
    | none => throwDerive s!"SystemCouplingRecipe arity not a nat lit:\n{ty}"
  else
    throwDerive s!"expected SystemCouplingRecipe type, got:\n{ty}"

/-- Find a structure field RHS by field name using `StructureInfo`. -/
partial def findFieldRhs (field : Name) (e : Expr) : MetaM (Option Expr) := do
  let e := strip e
  match e with
  | .letE _ _ v b _ =>
    if let some r ← findFieldRhs field v then return some r
    findFieldRhs field b
  | .mdata _ e' => findFieldRhs field e'
  | e =>
    if e.isApp then
      let fn := e.getAppFn
      if let some c := fn.constName? then
        let env ← getEnv
        if let some (.ctorInfo ci) := env.find? c then
          if let some info := getStructureInfo? env ci.induct then
            let args := e.getAppArgs
            let fieldNames := info.fieldNames
            if let some idx := fieldNames.findIdx? (· == field) then
              let offset := args.size - fieldNames.size
              if idx + offset < args.size then
                return some args[idx + offset]!
      -- Deep search fallback for CSCR set literals
      if field == `CSCR then
        if e.isAppOf nm_Insert || e.isAppOf nm_Singleton
            || e.isAppOf nm_insert || e.isAppOf nm_singleton then
          return some e
      for a in e.getAppArgs do
        if let some r ← findFieldRhs field a then
          return some r
      return none
    else
      return none

structure WireEnds where
  name : String
  fromIdx : Nat
  toIdx : Nat
  deriving Repr

def wireEndsFromExpr (wireName : Name) (e : Expr) : MetaM WireEnds := do
  let e ← whnf e
  let e := strip e
  let args := e.getAppArgs
  if args.size < 2 then
    throwDerive s!"wire `{wireName}`: expected Prod, got:\n{e}"
  let left := args[args.size - 2]!
  let right := args[args.size - 1]!
  let fromIdx ← match natLit? (← whnf left) with
    | some n => pure n
    | none => throwDerive s!"wire `{wireName}`: cannot read source Fin from\n{left}"
  let toIdx ← match natLit? (← whnf right) with
    | some n => pure n
    | none => throwDerive s!"wire `{wireName}`: cannot read target Fin from\n{right}"
  return { name := shortName wireName, fromIdx, toIdx }

/-- Unfold definitional aliases once without reducing sets to predicates. -/
def unfoldConstOnce (e : Expr) : MetaM Expr := do
  let e := strip e
  match e.getAppFn.constName? with
  | some c =>
    if let some v ← constValue? c then
      -- Preserve apps: `toyCSCR` vs `f a`
      if e.isConst then
        return v
      else
        return e
    else
      return e
  | none => return e

def scrWires (scr : Name) : MetaM (Array WireEnds) := do
  let some val ← constValue? scr
    | throwDerive s!"SCR `{scr}` has no value"
  let val ← unfoldConstOnce val
  let some cscr ← findFieldRhs `CSCR val
    | throwDerive s!"SCR `{scr}`: cannot find CSCR field"
  -- Prefer one-level unfold of a named CSCR def; avoid `whnf` (turns sets into predicates).
  let cscr ← unfoldConstOnce cscr
  let elems ← setElements cscr
  let mut wires : Array WireEnds := #[]
  for el0 in elems do
    let el0 := strip el0
    if el0.isConst then
      let some wname := el0.constName? | throwDerive s!"CSCR const without name:\n{el0}"
      let some wval ← constValue? wname
        | throwDerive s!"wire `{wname}` has no value"
      wires := wires.push (← wireEndsFromExpr wname wval)
    else if el0.isAppOf nm_Prod_mk || el0.isAppOf ``Prod.mk then
      let wname := Name.mkSimple s!"wire{wires.size}"
      wires := wires.push (← wireEndsFromExpr wname el0)
    else if let some wname := el0.getAppFn.constName? then
      -- Named wire applied or residual form — use const value when available
      if let some wval ← constValue? wname then
        wires := wires.push (← wireEndsFromExpr wname wval)
      else
        wires := wires.push (← wireEndsFromExpr wname el0)
    else
      throwDerive s!"CSCR element is not a named wire or Prod:\n{el0}"
  return wires

/-- Module name for a declaration, if known. -/
def moduleOf? (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  return env.header.moduleNames[idx]!

def cellAliases (scr : Name) (n : Nat) : MetaM (Array String) := do
  let env ← getEnv
  let some mod := moduleOf? env scr
    | throwDerive s!"no module for `{scr}`"
  let mut names : Array String := Array.replicate n "comp"
  for i in [:n] do
    names := names.set! i s!"comp{i}"

  let mut cellFns : Array Name := #[]
  if let some scrVal ← constValue? scr then
    let scrVal ← whnf scrVal
    if let some vscr ← findFieldRhs `VSCR scrVal then
      let vscr ← whnf vscr
      if let some z ← findFieldRhs `Z vscr then
        let z ← whnf z
        if let some c := z.getAppFn.constName? then
          cellFns := cellFns.push c
        else if let .lam _ _ body _ := strip z then
          if let some c := body.getAppFn.constName? then
            cellFns := cellFns.push c
  for cand in #["rleCell", "toyCell", "fedCell"] do
    let full := mod ++ Name.mkSimple cand
    if env.contains full then cellFns := cellFns.push full
    let simple := Name.mkSimple cand
    if env.contains simple then cellFns := cellFns.push simple

  let moduleConsts := env.constants.fold (init := #[]) fun acc name info =>
    if moduleOf? env name == some mod then
      match info with
      | .defnInfo d => acc.push (name, d.value)
      | _ => acc
    else acc

  for (name, val) in moduleConsts do
    let val ← whnf val
    for cellFn in cellFns do
      if val.isAppOf cellFn then
        if let some k := natLit? val then
          if k < n then
            names := names.set! k (shortName name)
  return names

/-- Type-head constant of a declaration, avoiding `whnf` so abbrevs like `Technology` remain. -/
def typeHeadName (n : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let some info := env.find? n | return none
  let ty := info.type.consumeMData
  match ty.getAppFn.constName? with
  | some h => return some h
  | none =>
    forallTelescope ty fun _ body => do
      let body := body.consumeMData
      match body.getAppFn.constName? with
      | some h => return some h
      | none =>
        let body ← whnf body
        return body.getAppFn.constName?

def headMatches (h : Name) (candidates : Array Name) : Bool :=
  candidates.any fun c => h == c || shortName h == shortName c

def findByTypeHead (consts : Array Name) (heads : Array Name) : MetaM (Option Name) := do
  for c in consts do
    if let some h ← typeHeadName c then
      if headMatches h heads then
        return some c
  return none

def findByNameSuffix (consts : Array Name) (suffix : String) : Option Name :=
  consts.find? fun c => (shortName c).endsWith suffix

/-- Constants mentioned in `e`, plus one-level unfold of each definitional alias. -/
def collectConstsDeep (e : Expr) : MetaM (Array Name) := do
  let mut acc : Array Name := e.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  for c in acc do
    seen := seen.insert c
  -- One-level expand of defs appearing as apps/consts
  for c in e.getUsedConstants do
    if let some v ← constValue? c then
      for d in v.getUsedConstants do
        unless seen.contains d do
          seen := seen.insert d
          acc := acc.push d
  return acc

def docstringTitleSummary (decl : Name) : MetaM (String × String) := do
  let env ← getEnv
  match ← findDocString? env decl with
  | none => return ("", "")
  | some doc =>
    let lines := (doc.splitOn "\n").filter (fun l => !l.all Char.isWhitespace)
    match lines with
    | [] => return ("", "")
    | t :: rest => return (t, " ".intercalate rest)

def iorHorizon (ior : Name) : MetaM String := do
  let some val ← constValue? ior | return "unknown"
  let consts := val.getUsedConstants
  if consts.any (fun c => c == nm_functionalIOR || shortName c == "functionalIOR"
      || c == nm_olr_infinite || shortName c == "infinite") then
    return "infinite"
  if consts.any (fun c => c == nm_olr_finite || shortName c == "finite") then
    return "finite"
  return "unknown"

def iorAlphabet (ior : Name) : MetaM (String × String) := do
  let env ← getEnv
  let some info := env.find? ior | return ("", "")
  let ty ← whnf info.type
  if let some h := ty.getAppFn.constName? then
    if headMatches h #[nm_IOR, nm_IOR'] then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        let ir ← ppExpr args[args.size - 2]!
        let or_ ← ppExpr args[args.size - 1]!
        return (toString ir, toString or_)
  return ("", "")

def deriveIsrPackage (id : String) : MetaM IsrPackageDoc := do
  let env ← getEnv
  let some attr ← techdocAttrRef.get
    | throwDerive "techdocAttr not initialized"
  let some root := findTechdocDecl? env attr id
    | throwDerive s!"unknown techdoc id '{id}' (known: {listTechdocIds env attr})"
  let some rootVal ← constValue? root
    | throwDerive s!"techdoc root `{root}` has no value"
  let rootInfo ← getConstInfo root
  -- Type carries IOR/TYR parameters; value carries SCR / witnesses / choice args.
  let used ← collectConstsDeep rootVal
  let used := used ++ rootInfo.type.getUsedConstants

  let some tyr ← do
      if let some t ← findByTypeHead used #[nm_Technology] then pure (some t)
      else pure (findByNameSuffix used "Technology")
    | throwDerive s!"`{root}`: no Technology constant in type/value constants"
  let some scr ← do
      if let some s ← findByTypeHead used #[nm_SCR, nm_SCR'] then pure (some s)
      else pure (findByNameSuffix used "SCR")
    | throwDerive s!"`{root}`: no SystemCouplingRecipe constant in type/value constants"
  let some ior ← do
      if let some i ← findByTypeHead used #[nm_IOR, nm_IOR'] then pure (some i)
      else pure (findByNameSuffix used "IOR")
    | throwDerive s!"`{root}`: no InputOutputRequirement constant in type/value constants"

  let members ← technologyMembers tyr
  let scrInfo ← getConstInfo scr
  let n ← scrArity scrInfo.type
  let aliases ← cellAliases scr n
  let compNames := if members.size == n then members else aliases

  let wires ← scrWires scr
  let mut sources : Std.HashSet Nat := {}
  let mut targets : Std.HashSet Nat := {}
  let mut wireDocs : Array WireDoc := #[]
  for w in wires do
    sources := sources.insert w.fromIdx
    targets := targets.insert w.toIdx
    let fromC := if w.fromIdx < compNames.size then compNames[w.fromIdx]! else s!"comp{w.fromIdx}"
    let toC := if w.toIdx < compNames.size then compNames[w.toIdx]! else s!"comp{w.toIdx}"
    wireDocs := wireDocs.push {
      name := w.name
      fromComponent := fromC
      fromPort := "out"
      toComponent := toC
      toPort := "in"
    }

  let mut boundary : Array BoundaryPortDoc := #[]
  for i in [:n] do
    let cname := if i < compNames.size then compNames[i]! else s!"comp{i}"
    unless targets.contains i do
      boundary := boundary.push { component := cname, port := "in", direction := "in" }
    unless sources.contains i do
      boundary := boundary.push { component := cname, port := "out", direction := "out" }

  let components : Array ComponentDoc :=
    compNames.map fun name =>
      { name := name
        stateType := ""
        inPorts := [{ name := "in", valueType := "" }]
        outPorts := [{ name := "out", valueType := "" }]
        role := "" }

  let mut functionalSystem := ""
  let mut buildableSystem := ""
  let mut modeWitness := ""
  let mut homWitness := ""
  for c in used do
    let s := shortName c
    if functionalSystem.isEmpty then
      if s.endsWith "Spec" || s.endsWith "Ref" || s.endsWith "_fsd" then
        functionalSystem := if s.endsWith "_fsd" then "" else s
        if s.endsWith "_fsd" then
          if let some val ← constValue? c then
            for d in val.getUsedConstants do
              let sd := shortName d
              if sd.endsWith "Spec" || sd.endsWith "Ref" then
                functionalSystem := sd
        else
          functionalSystem := s
    if buildableSystem.isEmpty && (s.endsWith "Resultant" || s.endsWith "_resultant") then
      buildableSystem := s
    if modeWitness.isEmpty && (s.endsWith "_mode" || s.endsWith "Mode") then
      modeWitness := s
    if homWitness.isEmpty && (s.endsWith "_hom" || s.endsWith "Hom") then
      homWitness := s

  for c in used do
    if let some h ← typeHeadName c then
      if headMatches h #[nm_FSD] || (shortName c).endsWith "_fsd" then
        if let some val ← constValue? c then
          for d in val.getUsedConstants do
            let sd := shortName d
            if functionalSystem.isEmpty && (sd.endsWith "Spec" || sd.endsWith "Ref") then
              functionalSystem := sd

  let (title, summary) ← docstringTitleSummary root
  let horizon ← iorHorizon ior
  let (ir, or_) ← iorAlphabet ior
  let formalRefs := #[root, tyr, scr, ior].map (·.toString) |>.toList

  return {
    id := id
    title := title
    summary := summary
    technology := { name := shortName tyr, members := members.toList }
    coupling := {
      name := shortName scr
      components := components.toList
      wires := wireDocs.toList
      boundaryPorts := boundary.toList
    }
    ior := {
      name := shortName ior
      inputType := ir
      outputType := or_
      horizon := horizon
      description := ""
      lsc := some {
        chartName := s!"LSC_{shortName ior}"
        preCondition := s!"f ∈ {shortName ior}.itr"
        mainCondition := s!"g ∈ {shortName ior}.er f"
        inMessage := s!"in(f(t)) : {ir}"
        outMessage := s!"out(g(t)) : {or_}"
      }
    }
    functionalSystem := functionalSystem
    buildableSystem := buildableSystem
    implements := {
      functionalSystem := functionalSystem
      implementingSystem := buildableSystem
      modeWitness := modeWitness
      homWitness := homWitness
      notes := ""
    }
    formalRefs := formalRefs
  }

unsafe def withMbseMeta {α : Type} (k : MetaM α) : IO α := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Mbse }] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<techdoc>", fileMap := default }
  let state : Core.State := { env }
  Prod.fst <$> CoreM.toIO (ctx := ctx) (s := state) do
    MetaM.run' k

def listIds : MetaM (List String) := do
  let env ← getEnv
  let some attr ← techdocAttrRef.get
    | throwDerive "techdocAttr not initialized"
  return listTechdocIds env attr

end Mbse.TechdocDerive
