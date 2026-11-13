import Miri.Input.WorldReferenceAbi
import Miri.Input.WorldBoxAbi
import Miri.Input.WorldAggregateAbi

namespace Miri.Input.WorldAbiScalar
open Miri.ABI GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def classify (runtime : RuntimeMetadata) (session : AbiSessionMaterial) (definition : Option FunctionAbiMaterial)
    (isReturn : Bool) (id : TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let layout ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld runtime id)
  if layout.layout.isZst then return ArgAbi.initial layout
  if let .Memory := layout.layout.backendRepr then
    return ← WorldAggregateAbi.smallMemory runtime layout
  if let .ScalarPair .. := layout.layout.backendRepr then
    return ← liftPure (WorldAggregateAbi.nonPointerPair layout)
  let arena := (← get).arena
  let constructor ← liftPure do
    match ← arena.lookupType id with
    | .constructed constructor => pure (some constructor)
    | .material source => arena.materialKey source
  if let some (.adt _ arguments) := constructor then
    let declaration ← RuntimeArrayTypes.liftType (RuntimeMetadata.adtDeclarationInWorld runtime id)
    if declaration.langItem == some "owned_box" then
      return ← WorldBoxAbi.classify session isReturn layout arguments
  if let some (.reference pointee mutability _) := constructor then
    return ← WorldReferenceAbi.classify session definition isReturn layout pointee mutability
  if constructor.any (fun constructor => match constructor with
      | .rawPointer .. | .functionPointer .. => true | _ => false) then
    return ← liftPure (ArgAbi.conservativePointerScalar layout)
  liftPure (ArgAbi.nonPointerScalar layout 0)

end Miri.Input.WorldAbiScalar
