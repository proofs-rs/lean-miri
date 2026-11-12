import MiriTests.Input.LegacyFixture
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Miri Miri.ABI Miri.Input
private def must (result : Except String A) : IO A :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let path ← match args with | path::_ => pure path | [] => throw (IO.userError "missing export")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  check metadata.obligations.isEmpty s!"metadata obligations: {reprStr metadata.obligations}"
  check ((metadata.target.validate).isOk) "invalid canonical target"
  let values := metadata.source.types.filterMap fun node => (metadata.lookup node.id).toOption
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
  let some bodyIndex := (List.range decoded.document.bodies.size).find? (fun index =>
      (SourceMir.metadata decoded.document index).toOption.any (·.definitionId == some root.definitionId))
    | throw (IO.userError "canonical root body missing")
  let initialTypes ← must (TypeArena.World.ofDocument decoded.document)
  let (body,typeArena) ← must ((SourceMir.resolveBody decoded.document bodyIndex).run initialTypes)
  -- records(e, u, p, ...) has p in MIR local3, after return local0.
  let parameter ← must ((RuntimeMetadata.require body.mir.locals[3]? "records p parameter").mapError toString)
  let reference ← must ((metadata.lookup parameter).mapError toString)
  let pointee ← must ((metadata.pointee reference).mapError toString)
  let expected ← must ((metadata.integerLayout .u32).mapError toString)
  check (pointee.ty == expected.ty && pointee.ty != reference.ty) "source u32 pointee identity changed"
  let (pointerId,typeArena) ← must ((TypeArena.World.internType (.rawPointer 0 .Mut)).run typeArena)
  let (pointer,typeArena) ← must ((RuntimeMetadata.layoutInWorld metadata pointerId).run typeArena)
  check (pointer.ty == pointerId) "on-demand pointer lost its canonical constructor identity"
  let some originalType := decoded.document.types[0]? | throw (IO.userError "missing material type")
  let badTypes := decoded.document.types.set! 0 {originalType with id := decoded.document.types.size}
  let badMetadata : RuntimeMetadata := {
    source := {decoded.document with types := badTypes}, target := metadata.target, materialLayoutFuel := metadata.materialLayoutFuel,
    normalizationContext := metadata.normalizationContext, checkedMaterial := none, denseTypes := none }
  check (!(badMetadata.lookup 0).isOk) "inconsistent material type identity accepted"
  let missingTarget := { decoded.document with runtimeTargetDataLayout := none }
  check (!(RuntimeMetadata.ofDocument missingTarget).isOk) "missing target accepted"
  let first ← must ((RuntimeMetadata.require decoded.document.types[0]? "first type").mapError toString)
  let physical ← must ((RuntimeMetadata.require decoded.document.layouts[first.layoutId]? "first physical layout").mapError toString)
  check (!(RuntimeMetadata.layout metadata.target { physical with fields := none }).isOk) "missing fields accepted"
  let missingSize := do JsonReader.run DecoderValues.decodeCompilerLayout ("{\"kind\":\"layout\",\"field_offsets_bytes\":[]}")
  check (match missingSize with | .error reason => reason.contains "size/alignment" | .ok _ => false)
    "missing layout size was not rejected at the input boundary"
  let duplicate := { decoded.document with types := decoded.document.types.push first }
  check (!(RuntimeMetadata.ofDocument duplicate).isOk) "duplicate IDs accepted"
  -- Primitive/tuple/union recipes intentionally omit eager fields. Corrupt a
  -- remaining physical layout whose actual query depends on that material.
  let some materialType := decoded.document.types.find? (fun node =>
      (decoded.document.layouts[node.layoutId]?).any fun layout =>
        layout.primitiveRecipe.isNone && layout.tupleType.isNone &&
        layout.unionType.isNone && layout.structType.isNone && layout.enumType.isNone && layout.fields.isSome)
    | throw (IO.userError "fixture lacks a physical layout failure control")
  let some materialLayout := decoded.document.layouts[materialType.layoutId]?
    | throw (IO.userError "physical layout failure control disappeared")
  let incompleteLayouts := decoded.document.layouts.set! materialType.layoutId { materialLayout with fields := none }
  let incomplete := { decoded.document with layouts := incompleteLayouts }
  let kept ← must ((RuntimeMetadata.ofDocument incomplete).mapError toString)
  check (!kept.obligations.isEmpty && !(kept.lookup materialType.id).isOk) "layout failure was hidden"
  check ((kept.source.layouts[materialType.layoutId]?).bind (·.fields) |>.isNone) "failed-query layout lost"
  IO.println s!"runtime metadata: {values.size} exact layouts, {multiple} multiple-variant layouts; queries and explicit failures passed"
