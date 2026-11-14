import Miri.Input.TableTail
import Miri.Input.TypeConstCodec
import Miri.Input.CatalogDecoderRuntime
import Miri.Input.GenericInstantiation

/-! Read-only mechanism probe over a raw-material projection of one immutable
export. No compiler answers or instantiated bodies are loaded or cached. The
projection retains all type shapes/constant trees and definition identities used
by GenericInstantiation.ofType/resolveType. Timings are diagnostic wall times. -/
open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def log (value : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn value
  out.flush
private def milliseconds (start finish : Nat) : Nat := (finish - start) / 1000000
private def primitiveChild (types : Array TypeNode) (source : TypeNode) : Bool :=
  match source.shape with
  | .reference child .. => match types[child]? with
    | some node => [.bool,.char,.int,.uint,.float,.str,.never].contains node.shapeKind
    | none => false
  | _ => false

def main (args : List String) : IO Unit := do
  let [path,mode,selection] := args
    | throw (IO.userError "expected material.json cert|raw primitive|early-reference|late-reference")
  log "probe: read material start"
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let getArray (key : String) : IO (Array Json) := do must ((← must (raw.getObjVal? key)).getArr?)
  let rows ← getArray "types"
  let types ← rows.mapM (fun row => must (JsonReader.run DecoderValues.parseTypeNode row.compress))
  let definitions ← (← getArray "definitions").mapM fun row =>
    must (JsonReader.run (DecoderValues.parseDefinitionId "probe.definition") row.compress)
  let constants ← (← getArray "type_constants").mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "probe.constant") row.compress)
  let target ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  unless target.defaultAddressSpacePointerSpec.pointerSizeBytes > 0 do
    throw (IO.userError "generic instantiation target pointer width is zero")
  let context : GenericInstantiation.Context := {
    types, definitions, constants, pointerBytes := target.defaultAddressSpacePointerSpec.pointerSizeBytes }
  let context ← if mode == "raw" then pure context else if mode == "cert" then do
    if dense : TypeArena.isDense types = true then
      pure {context with denseTypes := some ⟨dense⟩}
    else throw (IO.userError "material projection has non-dense type identities")
    else throw (IO.userError "unknown context mode")
  let refs := types.filter (primitiveChild types)
  let nominals := types.filter fun node => match node.shape with
    | .adt data => data.args.isEmpty
    | _ => false
  let chosen := match selection with
    | "primitive" => types.find? (fun (node : TypeNode) => node.shapeKind == TypeShapeKind.uint)
    | "early-reference" => refs[0]?
    | "late-reference" => refs.back?
    | "early-nominal" => nominals[0]?
    | "late-nominal" => nominals.back?
    | _ => none
  let some chosen := chosen | throw (IO.userError "probe candidate absent")
  let hash ← must ((← must (raw.getObjVal? "source_sha256")).getStr?)
  log s!"probe: source_sha256={hash}; types={types.size}; defs={definitions.size}; mode={mode}; candidate={selection}; id={chosen.id}; ctor={repr chosen.shapeKind}"
  let start ← IO.monoNanosNow
  let term ← must (GenericInstantiation.ofType context 1024 chosen.id)
  let formed ← IO.monoNanosNow
  log s!"probe: ofType_ms={milliseconds start formed}"
  log "probe: resolve start"
  let actual ← must (GenericInstantiation.resolveType context 1024 term)
  let resolved ← IO.monoNanosNow
  unless actual == chosen.id do throw (IO.userError s!"canonical identity differs: expected={chosen.id}; actual={actual}")
  log s!"probe: resolve_ms={milliseconds formed resolved}; canonical_id={actual}; outcome=exact"
