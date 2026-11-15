import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerWorldAbi
import Miri.Input.TableTail
open Lean Miri Miri.Input Miri.Frontend.Foundation

private def compareArgument (world : SourceCompilerWorld.World) (actual : AbiArgument) (expected : Json) : IO Unit := do
  let mode ← IO.ofExcept (expected.getObjVal? "mode")
  let mode ← IO.ofExcept (JsonReader.run (DecoderValues.parseAbiPassMode "$.mode") mode.compress)
  unless actual.mode == mode do throw (IO.userError "reference complete compiler pass mode differs")
  let layout ← IO.ofExcept (expected.getObjVal? "layout")
  let layout ← IO.ofExcept (JsonReader.run DecoderValues.decodeCompilerLayout layout.compress)
  let some actual := world.canonical.layouts[actual.layoutId]? | throw (IO.userError "ABI layout absent")
  let target ← IO.ofExcept (SourcePhysical.target world)
  let actual ← IO.ofExcept ((RuntimeMetadata.layout target actual).mapError toString)
  let expected ← IO.ofExcept ((RuntimeMetadata.layout target layout).mapError toString)
  unless actual == expected do throw (IO.userError "reference full compiler physical layout differs")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected genuine std source and compiler oracle")
  let source ← IO.ofExcept (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let seeded ← IO.ofExcept (compilerEntrySeed source)
  let some material := seeded.canonical.sourceMaterial | throw (IO.userError "source absent")
  let [declaration] := (material.declarations.filter (·.path == "std::rt::lang_start_internal")).toList
    | throw (IO.userError "actual HRTB callee source absent")
  let queries := {seeded.canonical.queries with instanceAbis := #[]}
  let canonical := {seeded.canonical with functionAbis := #[],queries}
  let world := {seeded with canonical,derivedInstanceAbis := #[]}
  let (world,callee) ← IO.ofExcept (SourceCompilerWorld.internItem material.declarations world ⟨declaration.definition,#[]⟩)
  let (derived,abi) ← IO.ofExcept (SourceAbi.derive world callee #[])
  let oracle ← IO.ofExcept (Json.parse (← IO.FS.readFile oraclePath))
  let convention ← IO.ofExcept (oracle.getObjVal? "calling_convention")
  unless abi.canUnwind == (← IO.ofExcept (oracle.getObjValAs? Bool "can_unwind")) &&
      abi.cVariadic == (← IO.ofExcept (oracle.getObjValAs? Bool "c_variadic")) &&
      abi.fixedCount == (← IO.ofExcept (oracle.getObjValAs? Nat "fixed_count")) &&
      (← IO.ofExcept (convention.getObjValAs? String "kind")) == "rust" do
    throw (IO.userError "reference ABI header differs")
  compareArgument derived abi.returnValue (← IO.ofExcept (oracle.getObjVal? "return_argument"))
  let arguments ← IO.ofExcept (oracle.getObjValAs? (Array Json) "arguments")
  unless abi.arguments.size == arguments.size do throw (IO.userError "reference ABI argument arity differs")
  for (actual,expected) in abi.arguments.zip arguments do compareArgument derived actual expected
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  match SourceCompilerWorld.demandInstanceAbi access callee #[] world with
  | .error error _ => throw (IO.userError (reprStr error))
  | .ok _ updated =>
    unless updated.derivedInstanceAbis.size == 1 do throw (IO.userError "live World ABI memo absent")
    unless (← IO.ofExcept (SourceCompilerWorld.node updated callee)).kind == .identityOnly do
      throw (IO.userError "ABI demand manufactured a MIR body")
  let some abiMaterial := material.abi | throw (IO.userError "typed ABI declarations absent")
  let optimized := {material with abi := some {abiMaterial with optimizationDisabled := false}}
  let optimized := {world with canonical := {world.canonical with sourceMaterial := some optimized}}
  match SourceAbi.derive optimized callee #[] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "optimized reference attributes guessed")
  for binder in #[#[],#[SourceTypes.BoundVariable.region .anonymous]] do
    let functions := abiMaterial.functions.map fun function =>
      if function.definition == declaration.definition then
        {function with signature := {function.signature with boundVariables := binder}}
      else function
    let broken := {material with abi := some {abiMaterial with functions}}
    let broken := {world with canonical := {world.canonical with sourceMaterial := some broken}}
    match SourceAbi.derive broken callee #[] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "invalid signature binder accepted")
  let some physical := material.physical | throw (IO.userError "typed physical source absent")
  let unsizedIndex := physical.types.size
  let unsized := {physical with types := physical.types.push (.primitive "str" "")}
  let functions := abiMaterial.functions.map fun function =>
    if function.definition == declaration.definition then
      {function with signature := {function.signature with output := unsizedIndex}}
    else function
  let unsized := {material with physical := some unsized,abi := some {abiMaterial with functions}}
  let unsized := {world with canonical := {world.canonical with sourceMaterial := some unsized}}
  match SourceAbi.derive unsized callee #[] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsized value mistaken for zero-sized value")
  let [method] := (material.declarations.filter (·.path == "std::process::ExitCode::to_i32")).toList
    | throw (IO.userError "actual scalar method source absent")
  let (methodWorld,methodId) ← IO.ofExcept (SourceCompilerWorld.internItem material.declarations world ⟨method.definition,#[]⟩)
  let (methodWorld,methodAbi) ← IO.ofExcept (SourceAbi.derive methodWorld methodId #[])
  let expected ← IO.ofExcept (oracle.getObjVal? "inherent")
  compareArgument methodWorld methodAbi.returnValue (← IO.ofExcept (expected.getObjVal? "return_argument"))
  let expected ← IO.ofExcept (expected.getObjValAs? (Array Json) "arguments")
  unless methodAbi.arguments.size == expected.size do throw (IO.userError "scalar method arity differs")
  for (actual,expected) in methodAbi.arguments.zip expected do compareArgument methodWorld actual expected
  IO.println "actual HRTB &dyn std ABI equals compiler; live World derives it without imported answers"
