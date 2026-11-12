import Miri.Input.WorldReferenceAbi

namespace Miri.Input.WorldAbiScalar
open Miri.ABI GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def classify (runtime : RuntimeMetadata) (session : AbiSessionMaterial) (definition : Option FunctionAbiMaterial)
    (isReturn : Bool) (id : TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let layout ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld runtime id)
  if layout.layout.isZst then return ArgAbi.initial layout
  let arena := (← get).arena
  let constructor ← liftPure do
    match ← arena.lookupType id with
    | .constructed constructor => pure (some constructor)
    | .material source => arena.materialKey source
  if let some (.reference pointee mutability _) := constructor then
    return ← WorldReferenceAbi.classify session definition isReturn layout pointee mutability
  if constructor.any (fun constructor => match constructor with
      | .rawPointer .. | .functionPointer .. => true | _ => false) then
    return ← liftPure (ArgAbi.conservativePointerScalar layout)
  liftPure (ArgAbi.nonPointerScalar layout 0)

end Miri.Input.WorldAbiScalar
