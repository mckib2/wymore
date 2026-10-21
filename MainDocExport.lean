import Mbse.DocExport
import Mbse.TechdocDerive

/-!
# JSON export CLI for ISR documentation packages

Derives `IsrPackageDoc` from `@[techdoc "id"]` ISR roots via Meta Expr walking.

```
lake exe mbse-doc-export list
lake exe mbse-doc-export export toy
lake exe mbse-doc-export export toy --out build/techdoc/toy/design.json
```
-/

open Mbse.DocExport
open Mbse.TechdocDerive

def usage : String :=
  "usage:\n" ++
  "  lake exe mbse-doc-export list\n" ++
  "  lake exe mbse-doc-export export <id> [--out path.json]\n"

def writeOut (path? : Option String) (content : String) : IO Unit := do
  match path? with
  | none => IO.println content
  | some path =>
    let p : System.FilePath := path
    if let some parent := p.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile p content
    IO.eprintln s!"wrote {path}"

/-- Parse `export` args: `<id>` and optional `--out path`. -/
def parseExportArgs : List String → Except String (String × Option String)
  | [name] => .ok (name, none)
  | [name, "--out", path] => .ok (name, some path)
  | ["--out", path, name] => .ok (name, some path)
  | _ => .error "export requires <id> and optional --out path.json"

/-- Lake may forward a leading `--` separator into program args; strip it. -/
def normalizeArgs : List String → List String
  | "--" :: rest => rest
  | args => args

unsafe def main (args : List String) : IO UInt32 := do
  match normalizeArgs args with
  | ["list"] =>
    try
      let ids ← withMbseMeta listIds
      for id in ids do
        IO.println id
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"
      return 1
  | "export" :: rest =>
    match parseExportArgs rest with
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      IO.eprintln usage
      return 1
    | .ok (name, out?) =>
      try
        let doc ← withMbseMeta (deriveIsrPackage name)
        writeOut out? (toPrettyJson doc)
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
  | _ =>
    IO.eprintln usage
    return 1
