import Miri.Frontend.FoundationAbi
import Miri.Frontend.FoundationPhysicalTypes
import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationRegionErasure

open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported constrained type accepted")

def main (paths : List String) : IO Unit := do
  let [finitePath,compilerPath] := paths | throw (IO.userError "expected finite/compiler NonNull exports")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let some row := document.types.find? (fun row =>
      ((row.getObjVal? "shape" >>= fun shape => shape.getObjValAs? String "kind").toOption == some "pattern_type"))
    | throw (IO.userError "source constrained type absent")
  let id ← checked (row.getObjValAs? Nat "type_id")
  let source ← checked (typeExpr document id)
  let instantiated ← checked (instantiate #[some (.primitive "uint" "u8")] #[] source)
  let base := ConcreteType.pointer "raw_pointer_const" (.primitive "uint" "u8")
  unless sameConcrete 1024 instantiated (.patternNotNull base) && !sameConcrete 1024 instantiated base do
    throw (IO.userError "NotNull constraint erased during substitution")
  unless sameConcrete 1024 instantiated (← checked (eraseRegions instantiated)) do
    throw (IO.userError "region erasure lost NotNull constraint")
  failure (physicalLayoutOfDocument document instantiated)
  failure (rustModeShapeOfDocument document false instantiated)
  let compiler ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let types ← checked (compiler.getObjValAs? (Array Json) "types")
  let some actual := types.find? (fun row =>
      (row.getObjValAs? String "display").toOption == some "pattern_type!(*const u8 is !null)")
    | throw (IO.userError "compiler constrained type absent")
  let shape ← checked (actual.getObjVal? "shape")
  let pattern ← checked (shape.getObjVal? "pattern")
  unless (← checked (pattern.getObjValAs? String "kind")) == "not_null" do
    throw (IO.userError "compiler constraint differs")
  let baseId ← checked (shape.getObjValAs? Nat "base")
  let some actualBase := types[baseId]? | throw (IO.userError "compiler base absent")
  unless (← checked (actualBase.getObjValAs? String "display")) == "*const u8" do
    throw (IO.userError "compiler base differs")
  let sourceShape ← checked (row.getObjVal? "shape")
  let badShape := sourceShape.setObjVal! "pattern" (Json.mkObj [("kind",toJson "range")])
  let badRow := row.setObjVal! "shape" badShape
  failure (typeExpr { document with types := document.types.mapIdx fun index entry =>
    if index == id then badRow else entry } id)
  failure (instantiate #[] #[] source)
  IO.println "foundation NotNull pattern: source substitution retains constraint and matches compiler base/pattern; unknown pattern/missing args/physical layout reject"
