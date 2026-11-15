import Miri.Frontend.FoundationPhysicalRegistry

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Fresh two-root compiler-entry export exercises the generic fn()->T source
signature. This checks physical materialization, not process startup execution. -/
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh compiler-entry foundation export")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some sourceId := document.types.findIdx? (fun row =>
      ((row.getObjVal? "shape") >>= (·.getObjValAs? String "kind")).toOption == some "function_pointer")
    | throw (IO.userError "source function pointer absent")
  let source ← checked (typeExpr document sourceId)
  let concrete ← checked (instantiate #[some (.tuple #[])] #[] source)
  let (physical, id) ← checked ((PhysicalTypeRegistry.start document).intern concrete)
  let (node, layout) ← checked (physical.lookup id)
  let .functionPointer signature binders := node.shape
    | throw (IO.userError "physical function pointer shape lost")
  unless signature.inputs.isEmpty && binders.isEmpty && signature.safety == .Safe &&
      signature.abi == .Rust && !signature.cVariadic do
    throw (IO.userError "source function pointer signature changed")
  let (output, _) ← checked (physical.lookup signature.output)
  unless output.shapeKind == .tuple do throw (IO.userError "generic return substitution lost")
  let target ← checked (runtimeTargetOfTarget document.target)
  let spec ← checked ((target.pointerSpecIn target.instructionAddressSpace).mapError toString)
  unless layout.sizeBytes == some spec.pointerSize.bytes.toNat &&
      layout.abiAlignBytes == some (← checked (spec.pointerAlign.bytes.mapError toString)).toNat do
    throw (IO.userError "function pointer target layout changed")
  let some scalar := layout.backendRepresentation >>= (·.scalar)
    | throw (IO.userError "function pointer scalar absent")
  unless scalar.validRange == some (1, 2^(spec.pointerSize.bytes.toNat*8)-1) &&
      scalar.primitive.addressSpace == some target.instructionAddressSpace.value.toNat &&
      layout.largestNiche.isSome do
    throw (IO.userError "function pointer nonnull/code address-space layout changed")
  let _ ← checked (physical.runtimeLayout id)
  match (PhysicalTypeRegistry.start document).intern
      (.functionPointer #[] (.tuple #[]) "safe" "c" false) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported C function pointer accepted")
  let some sourceRow := document.types[sourceId]? | throw (IO.userError "source function pointer row absent")
  let shape ← checked (sourceRow.getObjVal? "shape")
  let signatureSource ← checked (shape.getObjVal? "signature")
  let changed := signatureSource.setObjVal! "bound_variables" (toJson #[Json.null])
  let changedRow := sourceRow.setObjVal! "shape" (shape.setObjVal! "signature" changed)
  let types := document.types.mapIdx (fun index original =>
    if index == sourceId then changedRow else original)
  let malformed := { document with types }
  match typeExpr malformed sourceId with
  | .error "bound function-pointer signature unsupported" => pure ()
  | .error error => throw (IO.userError s!"unexpected binder diagnostic: {error}")
  | .ok _ => throw (IO.userError "bound function pointer accepted")
  IO.println "foundation fn pointer: source generic signature, exact physical joins, nonnull instruction address space and unsupported ABI rejection passed"
