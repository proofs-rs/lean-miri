import Miri.Input.Decoder
import Miri.Input.ValidateTables

open Miri Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (label : String) (document : ImportDocument) : IO Unit :=
  match validatePrimaryTables document with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: typed table reference was accepted")

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | [] => throw (IO.userError "expected exported compiler input")
  let imported ← must (decodeJson (← IO.FS.readFile path))
  let document := imported.document
  let some firstType := document.types[0]? | throw (IO.userError "missing fixture type")
  let some firstInstance := document.instances[0]? | throw (IO.userError "missing fixture instance")
  unless !document.definitions.isEmpty do throw (IO.userError "missing fixture definition")
  let _ ← must (validatePrimaryTables document)
  let withShape (shape : TypeShape) :=
    { document with types := document.types.set! 0 { firstType with shape } }
  reject "tuple element" (withShape (.tuple #[document.types.size]))
  reject "array length" (withShape (.array 0 document.typeConstants.size ⟨0, true⟩))
  reject "array constructor width" (withShape (.array 0 0 ⟨2^64, true⟩))
  reject "pattern endpoint" (withShape (.patternType 0 (.range document.typeConstants.size document.typeConstants.size)))
  reject "owned type argument" (withShape (.closure 0 #[.Type document.types.size] 0))
  reject "owned constant argument" (withShape (.closure 0 #[.Const document.typeConstants.size] 0))
  reject "binder definition" (withShape (.unsafeBinder 0 #[.Type (.Param document.definitions.size)]))
  reject "region definition" (withShape (.reference 0 .Not (.LateParameter document.definitions.size .ClosureEnv)))
  reject "dynamic predicate" (withShape (.dynamicTraitObject #[document.predicates.size] none .Erased))
  let invalidInstance := { firstInstance with genericArgs := #[.Lifetime (.LateParameter document.definitions.size .ClosureEnv)] }
  reject "instance lifetime definition" { document with instances := document.instances.set! 0 invalidInstance }
  reject "constant child" { document with typeConstants := #[.Expr .FunctionCall #[.Const 1]] }
  reject "valtree child" { document with typeConstants := #[.Value 0 ⟨#[.Branch #[1]], 0⟩] }
  IO.println "typed table bounds passed: owned shapes, arguments, binders, regions, predicates and constant children"
