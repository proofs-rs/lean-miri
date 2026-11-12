import Miri.Input.RuntimeArrayTypes
import Miri.Input.WorldTypeName
import Miri.Input.WorldNamedArguments

/-! rustc_middle/ty/print/mod.rs::Print<Instance> and Print<ShimKind>.
Paths and argument spelling are read from this execution's complete instance
key. A diagnostic FnDef signature is never substituted for an Instance name. -/
namespace Miri.Input.WorldInstanceName
open Miri.Interpreter
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

/-- Domain discriminator for the currently ported raw named-path branch. -/
def supports (world : RuntimeArrayTypes.World) (key : InstanceArena.Key) : Bool :=
  key.definition.crateIndex == 0 &&
  match world.arena.definitionRef key.definition with
  | .error _ => false
  | .ok reference => match world.arena.definitions[reference]? with
    | none => false
    | some definition => match definition.rawPath with
      | none => false
      | some path => (path.genericHeader.any (fun header => header.parentParameterCount == 0)) && path.components.all fun component =>
        ["crate_root","type","value"].contains component.kind

def query (fuel : Nat) (key : InstanceArena.Key) : RuntimeArrayTypes.CompilerM String := do
  let world ← get
  unless supports world key do throw "instance rendering requires an unported raw definition-path branch"
  let some options := world.metadata.source.queries.session.printOptions
    | throw "instance rendering requires raw print options"
  let reference ← lift (world.arena.definitionRef key.definition)
  let some definition := world.arena.definitions[reference]? | throw "instance source definition absent"
  let some path := definition.rawPath | throw "instance raw path absent"
  let mut result ← lift (DefinitionPath.localNamedPath path options.verboseInternals
    options.trimDiagnosticPaths options.trimmedDefPaths)
  let arguments ← lift (WorldNamedArguments.own world.arena fuel path key.arguments)
  let printType := fun id => RuntimeArrayTypes.liftType (WorldTypeName.query world.metadata fuel id)
  if !arguments.isEmpty then
    result := result ++ "::<"
    for (argument,index) in arguments.zipIdx do
      if index > 0 then result := result ++ ", "
      let value ← match argument with
        | .Type id => printType id
        | .Const id => RuntimeArrayTypes.liftType (WorldConstantName.query id)
        | .Lifetime .Static => pure "'static"
        | .Lifetime .Erased => pure "'_"
        | .Lifetime _ => throw "instance named lifetime printing requires raw region naming"
      result := result ++ value
    result := result ++ ">"
  let suffix ← match key.kind with
    | .Item _ => pure ""
    | .Intrinsic _ => pure " - intrinsic"
    | .LlvmIntrinsic _ => pure " - LLVM intrinsic"
    | .Virtual _ index => pure s!" - virtual#{index}"
    | .Shim shim => do
      let text ← match shim with
        | .VTable _ => pure "shim(vtable)"
        | .Reify _ none => pure "shim(reify)"
        | .Reify _ (some .FnPtr) => pure "shim(reify-fnptr)"
        | .Reify _ (some .Vtable) => pure "shim(reify-vtable)"
        | .ThreadLocal _ => pure "shim(tls)"
        | .ClosureOnce .. | .ConstructCoroutineInClosure .. => pure "shim"
        | .DropGlue _ none => pure "shim(None)"
        | .DropGlue _ (some ty) | .AsyncDropGlueCtor _ ty => return s!"shim(Some({← printType ty}))"
        | .FnPtr _ ty | .Clone _ ty | .FnPtrAsPtr _ ty | .FnPtrFromPtr _ ty
        | .AsyncDropGlue _ ty => return s!"shim({← printType ty})"
        | .FutureDropPoll _ proxy impl => return s!"dropshim({← printType proxy}-{← printType impl})"
      pure (" - " ++ text)
  pure (result ++ suffix)
end Miri.Input.WorldInstanceName
