import Lean

/-!
# `@[techdoc "id"]` attribute

Marks an `ImplementableSystemDesign` (or other ISR root) for JSON export via
`lake exe mbse-doc-export`. Ids are stored in a parametric attribute extension
so exporters can list and resolve them after `importModules`.
-/

open Lean

/-- Attribute syntax: `@[techdoc "toy"]`. -/
syntax (name := techdoc) "techdoc" ppSpace str : attr

/-- Forward declaration filled by `initialize` below. -/
initialize techdocAttrRef : IO.Ref (Option (ParametricAttribute String)) ← IO.mkRef none

namespace Mbse.TechdocAttr

/-- All `(id, decl)` pairs recorded by `@[techdoc]`, local and imported. -/
def allTechdocEntries (env : Environment) (attr : ParametricAttribute String) :
    Array (String × Name) :=
  Id.run do
    let mut out : Array (String × Name) := #[]
    let (_decls, m) := attr.ext.getState env
    for (decl, id) in m.toList do
      out := out.push (id, decl)
    for i in [:env.header.modules.size] do
      let modIdx : ModuleIdx := i
      let entries := attr.ext.getModuleEntries env modIdx
      for (decl, id) in entries do
        out := out.push (id, decl)
    pure out

/-- Sorted unique techdoc ids. -/
def listTechdocIds (env : Environment) (attr : ParametricAttribute String) : List String :=
  Id.run do
    let ids := (allTechdocEntries env attr).map (·.1)
    let mut seen : Std.HashSet String := {}
    let mut out : Array String := #[]
    for id in ids do
      unless seen.contains id do
        seen := seen.insert id
        out := out.push id
    pure (out.toList.mergeSort (· < ·))

/-- Resolve a techdoc id to its root declaration name. -/
def findTechdocDecl? (env : Environment) (attr : ParametricAttribute String) (id : String) :
    Option Name :=
  (allTechdocEntries env attr).find? (·.1 == id) |>.map (·.2)

/-- Pretty short name (last name component). -/
def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- Access the registered attribute (after `initialize`). -/
def getTechdocAttr : IO (ParametricAttribute String) := do
  match ← techdocAttrRef.get with
  | some a => return a
  | none => throw <| IO.userError "techdocAttr not initialized"

end Mbse.TechdocAttr

/-- Parametric attribute: `@[techdoc "toy"]` on an ISR root declaration. -/
initialize techdocAttr : ParametricAttribute String ← do
  let attr ← registerParametricAttribute {
    name := `techdoc
    descr := "Mark a declaration as a techdoc export root (string id)."
    getParam := fun declName stx => do
      let `(attr| techdoc $s:str) := stx
        | throwError "invalid `[techdoc]` attribute, expected `[techdoc \"id\"]`"
      let id := s.getString
      let env ← getEnv
      if let some attr ← techdocAttrRef.get then
        for (existingId, existingDecl) in Mbse.TechdocAttr.allTechdocEntries env attr do
          if existingId == id && existingDecl != declName then
            throwError "techdoc id `{id}` already used by `{existingDecl}`"
      return id
  }
  techdocAttrRef.set (some attr)
  pure attr
