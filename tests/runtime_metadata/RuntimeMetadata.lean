import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Miri Miri.ABI Miri.Input
private def must (result : Except String A) : IO A :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let path ← match args with | path::_ => pure path | [] => throw (IO.userError "missing export")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  check metadata.obligations.isEmpty s!"metadata obligations: {reprStr metadata.obligations}"
  check (metadata.source.raw == decoded.document.raw) "original source evidence lost"
  check ((metadata.target.validate).isOk) "invalid canonical target"
  let values := metadata.layouts.filterMap fun (_,value) => value.toOption
  check (values.any fun x => match x.layout.fields with | .Union _ => true | _ => false) "union missing"
  check (values.any fun x => match x.layout.fields with | .Array .. => true | _ => false) "array missing"
  check (values.any fun x => match x.layout.backendRepr with | .SimdVector => true | _ => false) "SIMD missing"
  check (values.any fun x => match x.layout.backendRepr with | .Scalar (.Initialized (value := .Float _)) => true | _ => false) "float missing"
  let mut multiple := 0
  let mut niches := 0
  for value in values do
    match value.layout.variants with
    | .Multiple _ encoding _ variants =>
      multiple := multiple + 1
      match encoding with | .Niche .. => niches := niches + 1 | _ => pure ()
      for index in List.range variants.size do
        let selected ← must ((metadata.forVariant value index).mapError toString)
        check (selected.layout.variants == Variants.Single index) "selected variant missing"
        check (selected.layout.randomizationSeed == 0) "source variant seed not zero"
        for field in List.range selected.layout.fields.count do
          let _ ← must ((metadata.field selected field).mapError toString)
    | _ => pure ()
  check (multiple >= 2 && niches >= 1) "direct and niche variants not covered"
  let scope ← must ((RuntimeMetadata.require decoded.document.selectedScope "selected scope").mapError toString)
  check (scope.roots.size == 1) "fixture must have one selected root"
  let root ← must ((RuntimeMetadata.require scope.roots[0]? "selected root").mapError toString)
  let some body := decoded.document.bodies.find? (·.definitionId == some root.definitionId)
    | throw (IO.userError "canonical root body missing")
  -- records(e, u, p, ...) has p in MIR local3, after return local0.
  let parameter ← must ((RuntimeMetadata.require body.locals[3]? "records p parameter").mapError toString)
  let reference ← must ((metadata.lookup parameter.typeId).mapError toString)
  let pointee ← must ((metadata.pointee reference).mapError toString)
  let expected ← must ((metadata.integerLayout .u32).mapError toString)
  check (pointee.ty == expected.ty && pointee.ty != reference.ty) "source u32 pointee identity changed"
  check (!(metadata.lookup 999999).isOk) "unknown type accepted"
  check (!(RuntimeMetadata.importTarget .null).isOk) "missing target accepted"
  let first ← must ((RuntimeMetadata.require decoded.document.types[0]? "first type").mapError toString)
  check (!(RuntimeMetadata.layout metadata.target { first.layout with fields := none }).isOk) "missing fields accepted"
  check (!(RuntimeMetadata.layout metadata.target { first.layout with status := .unknown }).isOk) "unknown layout accepted"
  let duplicate := { decoded.document with types := decoded.document.types.push first }
  check (!(RuntimeMetadata.ofDocument duplicate).isOk) "duplicate IDs accepted"
  let incomplete := { decoded.document with types := decoded.document.types.map fun node =>
      if node.id == first.id then { node with layout := { node.layout with fields := none } } else node }
  let kept ← must ((RuntimeMetadata.ofDocument incomplete).mapError toString)
  check (!kept.obligations.isEmpty && !(kept.lookup first.id).isOk) "layout failure was hidden"
  check (kept.source.raw == incomplete.raw) "failed-query source lost"
  IO.println s!"runtime metadata: {values.size} exact layouts, {multiple} multiple-variant layouts; queries and explicit failures passed"
