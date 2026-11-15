import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceAbi
import Miri.Input.DecoderValues
open Lean Miri Miri.Input Miri.Frontend.Foundation

private def mode (world : SourceCompilerWorld.World) (path : String) (arguments : Array MIR.GenericArg := #[]) : Except String (SourceCompilerWorld.World × FunctionAbi) := do
  let some material := world.canonical.sourceMaterial | throw "source absent"
  let [declaration] := (material.declarations.filter (·.path == path)).toList | throw "function source absent"
  let (world,callee) ← SourceCompilerWorld.internItem material.declarations world ⟨declaration.definition,arguments⟩
  SourceAbi.derive world callee #[]

def main (args : List String) : IO Unit := do
  let [path,closurePath,oraclePath] := args | throw (IO.userError "expected aggregate ABI source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let world ← IO.ofExcept (compilerEntrySeed document)
  let (world,large) ← IO.ofExcept (mode world "large")
  let expected : AbiPassMode := ⟨.indirect,#[⟨670,24,some 8,.none⟩],none,none,none,some .pointer⟩
  unless large.returnValue.mode == expected && large.arguments.map (·.mode) == #[expected] do
    throw (IO.userError "large aggregate indirect mode differs")
  for (name,bytes,bits) in [("dense",4,128),("short",3,0),("padded",8,0)] do
    let (_,abi) ← IO.ofExcept (mode world name)
    let expected : AbiPassMode := ⟨.cast,#[],some ⟨#[],none,⟨.integer,bytes*8,none⟩,bytes,false,⟨bits,0,none,.none⟩⟩,some 0,none,none⟩
    unless abi.returnValue.mode == expected && abi.arguments.map (·.mode) == #[expected] do
      throw (IO.userError s!"{name} aggregate cast/initialization mode differs")
  let oracle ← IO.ofExcept (Json.parse (← IO.FS.readFile oraclePath))
  let instances ← IO.ofExcept (oracle.getObjValAs? (Array Json) "instances")
  let queries ← IO.ofExcept (oracle.getObjValAs? (Array Json) "compiler_instance_abis")
  let abis ← IO.ofExcept (oracle.getObjValAs? (Array Json) "fn_abis")
  let arguments ← IO.ofExcept (oracle.getObjValAs? (Array Json) "abi_arguments")
  let parseMode := fun value => IO.ofExcept (JsonReader.run (DecoderValues.parseAbiPassMode "$.mode") value.compress)
  for name in ["large","dense","short","padded"] do
    let [node] := (instances.filter fun row => (row.getObjValAs? String "def_path").toOption == some name).toList
      | throw (IO.userError "oracle function identity absent/ambiguous")
    let id ← IO.ofExcept (node.getObjValAs? Nat "instance_id")
    let [query] := (queries.filter fun row => (row.getObjValAs? Nat "instance_id").toOption == some id &&
      (row.getObjValAs? (Array Nat) "extra_argument_types").toOption == some #[]).toList
      | throw (IO.userError "oracle exact ABI key absent/ambiguous")
    let index ← IO.ofExcept (query.getObjValAs? Nat "abi_query")
    let some expected := abis[index]? | throw (IO.userError "oracle ABI absent")
    let (_,actual) ← IO.ofExcept (mode world name)
    let result ← IO.ofExcept (expected.getObjValAs? Nat "return")
    let some result := arguments[result]? | throw (IO.userError "oracle return absent")
    unless actual.returnValue.mode == (← parseMode (← IO.ofExcept (result.getObjVal? "mode"))) do
      throw (IO.userError s!"{name}: independent compiler return mode differs")
    let ids ← IO.ofExcept (expected.getObjValAs? (Array Nat) "arguments")
    unless ids.size == actual.arguments.size do throw (IO.userError "oracle argument count differs")
    for (id,argument) in ids.zip actual.arguments do
      let some row := arguments[id]? | throw (IO.userError "oracle argument absent")
      unless argument.mode == (← parseMode (← IO.ofExcept (row.getObjVal? "mode"))) do
        throw (IO.userError s!"{name}: independent compiler argument mode differs")
    unless actual.fixedCount == (← IO.ofExcept (expected.getObjValAs? Nat "fixed_count")) &&
        actual.canUnwind == (← IO.ofExcept (expected.getObjValAs? Bool "can_unwind")) &&
        actual.cVariadic == (← IO.ofExcept (expected.getObjValAs? Bool "c_variadic")) do
      throw (IO.userError "independent compiler ABI header differs")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile closurePath) >>= decode)
  let world ← IO.ofExcept (compilerEntrySeed document)
  let some source := world.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := source.physical | throw (IO.userError "physical source absent")
  let [closure] := (physical.types.zipIdx |>.filterMap fun (type,index) => match type with
    | .closure closure =>
      if physical.definitions[closure.definition]?.map (·.path) == some "std::rt::lang_start_internal::{closure#0}" then some index else none
    | _ => none).toList | throw (IO.userError "genuine internal closure absent")
  let concrete ← IO.ofExcept (SourceTypes.instantiate physical #[] #[] closure)
  let (world,closure) ← IO.ofExcept (SourcePhysical.intern world concrete)
  let (_,abi) ← IO.ofExcept (mode world "local_probe" #[.Type closure])
  let expectedReturn : AbiPassMode := ⟨.indirect,#[⟨670,16,some 8,.none⟩],none,none,none,some .pointer⟩
  let expectedInput : AbiPassMode := ⟨.indirect,#[⟨670,40,some 8,.none⟩],none,none,none,some .pointer⟩
  unless abi.returnValue.mode == expectedReturn && abi.arguments.map (·.mode) == #[expectedInput] do
    throw (IO.userError "genuine Result/closure memory indirect modes differ")
  let (world,isize) ← IO.ofExcept (SourcePhysical.intern world (.primitive "int" "isize"))
  let (_,externalAbi) ← IO.ofExcept (mode world "std::panic::catch_unwind" #[.Type closure,.Type isize])
  unless externalAbi.returnValue.mode == expectedReturn && externalAbi.arguments.map (·.mode) == #[expectedInput] do
    throw (IO.userError "caller optNo external no-deduction modes differ")
  IO.println "local aggregate/Result/closure ABI modes and caller optNo external baseline passed"
