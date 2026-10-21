import Lean.Data.Json

/-!
# Documentation export model for technology / coupling / ISR packages

String-labelled presentation views of Wymore technology, coupling recipes, and
implementability (ISR / PoI) packages. Formal proofs stay authoritative; these
structures are the JSON contract consumed by `scripts/techdoc`.
-/

namespace Mbse.DocExport

open Lean

/-- Schema version embedded in every exported JSON document. -/
def schemaVersion : Nat := 1

structure PortDoc where
  name : String
  valueType : String := ""
  deriving Repr, Inhabited

structure ComponentDoc where
  name : String
  stateType : String := ""
  inPorts : List PortDoc := []
  outPorts : List PortDoc := []
  role : String := ""
  deriving Repr, Inhabited

structure WireDoc where
  name : String := ""
  fromComponent : String
  fromPort : String
  toComponent : String
  toPort : String
  deriving Repr, Inhabited

structure BoundaryPortDoc where
  component : String
  port : String
  direction : String  -- "in" | "out"
  deriving Repr, Inhabited

structure TechnologyDoc where
  name : String
  members : List String
  unusedShelf : List String := []
  deriving Repr, Inhabited

structure CouplingDoc where
  name : String
  components : List ComponentDoc
  wires : List WireDoc
  boundaryPorts : List BoundaryPortDoc := []
  deriving Repr, Inhabited

structure IorDoc where
  name : String
  inputType : String := ""
  outputType : String := ""
  horizon : String := "infinite"  -- "infinite" | "finite <n>"
  description : String := ""
  deriving Repr, Inhabited

structure ImplementsDoc where
  functionalSystem : String
  implementingSystem : String
  modeWitness : String := ""
  homWitness : String := ""
  notes : String := ""
  deriving Repr, Inhabited

/-- Full implementability / PoI package presentation. -/
structure IsrPackageDoc where
  id : String
  title : String := ""
  summary : String := ""
  technology : TechnologyDoc
  coupling : CouplingDoc
  ior : IorDoc
  functionalSystem : String := ""
  buildableSystem : String := ""
  implements : ImplementsDoc
  formalRefs : List String := []
  deriving Repr, Inhabited

/-! ## JSON encoding -/

private def portToJson (p : PortDoc) : Json :=
  Json.mkObj [
    ("name", Json.str p.name),
    ("valueType", Json.str p.valueType)
  ]

private def componentToJson (c : ComponentDoc) : Json :=
  Json.mkObj [
    ("name", Json.str c.name),
    ("stateType", Json.str c.stateType),
    ("inPorts", Json.arr (c.inPorts.map portToJson).toArray),
    ("outPorts", Json.arr (c.outPorts.map portToJson).toArray),
    ("role", Json.str c.role)
  ]

private def wireToJson (w : WireDoc) : Json :=
  Json.mkObj [
    ("name", Json.str w.name),
    ("fromComponent", Json.str w.fromComponent),
    ("fromPort", Json.str w.fromPort),
    ("toComponent", Json.str w.toComponent),
    ("toPort", Json.str w.toPort)
  ]

private def boundaryToJson (b : BoundaryPortDoc) : Json :=
  Json.mkObj [
    ("component", Json.str b.component),
    ("port", Json.str b.port),
    ("direction", Json.str b.direction)
  ]

private def technologyToJson (t : TechnologyDoc) : Json :=
  Json.mkObj [
    ("name", Json.str t.name),
    ("members", Json.arr (t.members.map Json.str).toArray),
    ("unusedShelf", Json.arr (t.unusedShelf.map Json.str).toArray)
  ]

private def couplingToJson (c : CouplingDoc) : Json :=
  Json.mkObj [
    ("name", Json.str c.name),
    ("components", Json.arr (c.components.map componentToJson).toArray),
    ("wires", Json.arr (c.wires.map wireToJson).toArray),
    ("boundaryPorts", Json.arr (c.boundaryPorts.map boundaryToJson).toArray)
  ]

private def iorToJson (i : IorDoc) : Json :=
  Json.mkObj [
    ("name", Json.str i.name),
    ("inputType", Json.str i.inputType),
    ("outputType", Json.str i.outputType),
    ("horizon", Json.str i.horizon),
    ("description", Json.str i.description)
  ]

private def implementsToJson (i : ImplementsDoc) : Json :=
  Json.mkObj [
    ("functionalSystem", Json.str i.functionalSystem),
    ("implementingSystem", Json.str i.implementingSystem),
    ("modeWitness", Json.str i.modeWitness),
    ("homWitness", Json.str i.homWitness),
    ("notes", Json.str i.notes)
  ]

def isrPackageToJson (d : IsrPackageDoc) : Json :=
  Json.mkObj [
    ("schemaVersion", Json.num schemaVersion),
    ("id", Json.str d.id),
    ("title", Json.str d.title),
    ("summary", Json.str d.summary),
    ("technology", technologyToJson d.technology),
    ("coupling", couplingToJson d.coupling),
    ("ior", iorToJson d.ior),
    ("functionalSystem", Json.str d.functionalSystem),
    ("buildableSystem", Json.str d.buildableSystem),
    ("implements", implementsToJson d.implements),
    ("formalRefs", Json.arr (d.formalRefs.map Json.str).toArray)
  ]

/-- Pretty-printed JSON string for an ISR documentation package. -/
def toPrettyJson (d : IsrPackageDoc) : String :=
  (isrPackageToJson d).pretty

end Mbse.DocExport
