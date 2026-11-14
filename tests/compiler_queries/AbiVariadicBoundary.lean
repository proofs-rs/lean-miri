import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
import Miri.Input.WorldFunctionPointerAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def variadicSignature : GenericSubstitution.Term → GenericSubstitution.Term
  | .binder variables body => .binder variables (variadicSignature body)
  | .node .aggregate "signature" payload children =>
    .node .aggregate "signature" (payload.replace "\"c_variadic\":false" "\"c_variadic\":true") children
  | other => other

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh ordinary Item ABI source")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let candidates := document.instances.filter fun node => match node.instanceKind with
    | .Item id => ((document.definitions[id]?).bind (·.rawPath)).any fun source =>
      (source.components.back?.bind (·.name)) == some "identity"
    | _ => false
  let some ordinary := candidates[0]? | throw (IO.userError "missing ordinary identity source")
  let empty ← must (InstanceArena.Store.ofSource world.arena #[])
  let key ← must (InstanceArena.Key.ofSource world.arena ordinary.instanceKind ordinary.genericArgs)
  let (callee,instances) ← must (empty.intern world.arena key)
  let world := {world with instances}
  let _ ← must ((WorldInstanceAbi.construct callee #[]).run world)
  let definitions := document.definitions.map fun source =>
    {source with genericTemplate := source.genericTemplate.map fun template =>
      {template with signatureExpression := template.signatureExpression.map variadicSignature}}
  let source := {world.metadata.source with definitions}
  let metadata := {world.metadata with source,checkedMaterial := none}
  let altered := {world with metadata}
  let (signature,_) ← must ((InstanceSignature.instantiate 16384 callee).run altered)
  unless (← must (RawFunctionSignature.read signature)).cVariadic do
    throw (IO.userError "variadic Item negative control did not alter the raw signature")
  if ((WorldInstanceAbi.construct callee #[]).run altered).isOk then
    throw (IO.userError "constructed Rust variadic Item ABI accepted")
  let (pointer,world) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internType (.functionPointer {
    abiPacked := Miri.ABI.ExternAbi.asPacked .Rust
    safe := true, cVariadic := true, splatted := none
    inputs := #[document.queries.primitives.u8], output := document.queries.primitives.u8}))).run world)
  if ((WorldFunctionPointerAbi.construct pointer #[]).run world).isOk then
    throw (IO.userError "constructed Rust variadic FnPtr ABI accepted")
  IO.println "PASS constructed Rust variadic Item and FnPtr signatures are explicit capability errors"
