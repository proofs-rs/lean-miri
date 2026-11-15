import Miri.Frontend.FoundationEntrySeed
import Miri.Input.CompilerValidityWorld
import Miri.Input.SourcePhysical
import Miri.Input.SourceTypeQueries
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def rejects (result : Except String A) : IO Unit :=
  match result with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported validity fact accepted")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine std source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let world ← IO.ofExcept (compilerEntrySeed document)
  let before := world.canonical.types.size
  let (world,pointer) ← IO.ofExcept (SourcePhysical.intern world (.functionPointer #[] (.tuple #[]) .Safe .Rust false))
  let .functionPointer := (← IO.ofExcept (CompilerValidityWorld.classify world pointer))
    | throw (IO.userError "FnPtr validity classification")
  unless (← IO.ofExcept (CompilerValidityWorld.opsemInhabited world pointer)) &&
      (← IO.ofExcept (CompilerValidityWorld.isFreeze world pointer)) do throw (IO.userError "FnPtr structural facts")
  let some source := world.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some physical := source.physical | throw (IO.userError "source types absent")
  let some closureRef := physical.types.findIdx? (fun type => match type with | .closure _ => true | _ => false)
    | throw (IO.userError "genuine closure source absent")
  let closure ← IO.ofExcept (SourceTypes.instantiate physical #[some (.tuple #[])] #[none] closureRef)
  let (world,closure) ← IO.ofExcept (SourcePhysical.intern world closure)
  let .aggregate false false false := (← IO.ofExcept (CompilerValidityWorld.classify world closure))
    | throw (IO.userError "closure non-ADT classification flags")
  unless (← IO.ofExcept (CompilerValidityWorld.opsemInhabited world closure)) do throw (IO.userError "closure upvars inhabitedness")
  rejects (CompilerValidityWorld.isFreeze world closure)
  let runtime ← IO.ofExcept ((RuntimeMetadata.ofDocument world.canonical).mapError toString)
  let layout ← IO.ofExcept ((runtime.lookup closure).mapError toString)
  let .capturedVar "0" := (← IO.ofExcept (CompilerValidityWorld.fieldPath world layout 0 pointer))
    | throw (IO.userError "external capture path must use index")
  let some abi := source.abi | throw (IO.userError "ABI declaration source absent")
  let [header] := (abi.functions.filter fun function =>
    (source.declarations.find? (·.definition == function.definition)).map (·.path) == some "std::rt::lang_start_internal").toList
    | throw (IO.userError "genuine dyn reference signature absent")
  let some input := header.signature.inputs[0]? | throw (IO.userError "dyn ref source absent")
  let reference ← IO.ofExcept (SourceTypes.instantiate physical #[] #[] input header.signature.boundVariables)
  let (world,reference) ← IO.ofExcept (SourcePhysical.intern world reference)
  let some row := world.canonical.types[reference]? | throw (IO.userError "reference type absent")
  let .reference dynamic _ _ := row.shape | throw (IO.userError "source is not a reference")
  let .dynamic _ := (← IO.ofExcept (CompilerValidityWorld.classify world dynamic))
    | throw (IO.userError "dynamic classification")
  let .dynamic _ := (← IO.ofExcept (CompilerValidityWorld.metadataTail world dynamic))
    | throw (IO.userError "dynamic metadata tail")
  unless (← IO.ofExcept (CompilerValidityWorld.opsemInhabited world dynamic)) &&
      (← IO.ofExcept (CompilerValidityWorld.opsemInhabited world reference)) &&
      (← IO.ofExcept (CompilerValidityWorld.isFreeze world reference)) do throw (IO.userError "dyn/ref structural facts")
  rejects (CompilerValidityWorld.isFreeze world dynamic)
  let (world,str) ← IO.ofExcept (SourcePhysical.intern world (.primitive "str" ""))
  unless (← IO.ofExcept (CompilerValidityWorld.isFreeze world str)) &&
      (← IO.ofExcept (CompilerValidityWorld.opsemInhabited world str)) do throw (IO.userError "str structural facts")
  let (world,raw) ← IO.ofExcept (SourcePhysical.intern world (.pointer "raw_pointer_const" (.primitive "str" "")))
  let .rawPointer _ false := (← IO.ofExcept (CompilerValidityWorld.classify world raw))
    | throw (IO.userError "raw str pointee must be unsized")
  let (world,raw) ← IO.ofExcept (SourcePhysical.intern world (.pointer "raw_pointer_const" (.primitive "uint" "u8")))
  let .rawPointer _ true := (← IO.ofExcept (CompilerValidityWorld.classify world raw))
    | throw (IO.userError "raw integer pointee must be sized")
  unless world.canonical.types.size > before do throw (IO.userError "test did not exercise types appended after seed")
  IO.println "live source FnPtr/closure/dyn/ref/str validity facts pass; unknown Freeze rejects"
