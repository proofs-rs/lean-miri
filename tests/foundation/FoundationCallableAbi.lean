import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerWorldAbi
import Miri.Input.SourcePhysical
import Miri.Input.TableTail
open Lean Miri Miri.Input Miri.Frontend.Foundation

private def demand (world : SourceCompilerWorld.World) (definition : DefinitionId)
    (pointer output : Nat) : Except String (SourceCompilerWorld.World × FunctionAbi) := do
  let some material := world.canonical.sourceMaterial | throw "source absent"
  let (world,callee) ← SourceCompilerWorld.internItem material.declarations world ⟨definition,#[.Type pointer,.Type output]⟩
  SourceAbi.derive world callee #[]

def main (args : List String) : IO Unit := do
  let path :: oraclePath :: malformed := args | throw (IO.userError "expected genuine std shortbacktrace header source")
  for path in malformed do
    let source ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
    match typedSourceMaterial source with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "accepted malformed callable declaration")
  let source ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let seeded ← IO.ofExcept (compilerEntrySeed source)
  let some material := seeded.canonical.sourceMaterial | throw (IO.userError "source absent")
  let [declaration] := (material.declarations.filter (·.path == "std::sys::backtrace::__rust_begin_short_backtrace")).toList
    | throw (IO.userError "genuine callable callee declaration absent")
  let queries := {seeded.canonical.queries with instanceAbis := #[]}
  let canonical := {seeded.canonical with functionAbis := #[],queries}
  let world := {seeded with canonical,derivedInstanceAbis := #[]}
  let (world,unit) ← IO.ofExcept (SourcePhysical.intern world (.tuple #[]))
  let (world,pointer) ← IO.ofExcept (SourcePhysical.intern world (.functionPointer #[] (.tuple #[]) .Safe .Rust false))
  let (_,abi) ← IO.ofExcept (demand world declaration.definition pointer unit)
  unless abi.arguments.size == 1 && abi.returnValue.mode.kind == .ignore do
    throw (IO.userError "actual shortbacktrace ABI shape mismatch")
  let oracle ← IO.ofExcept (Json.parse (← IO.FS.readFile oraclePath))
  let convention ← IO.ofExcept (oracle.getObjVal? "calling_convention")
  unless (← IO.ofExcept (oracle.getObjValAs? Bool "can_unwind")) == abi.canUnwind &&
      (← IO.ofExcept (oracle.getObjValAs? Bool "c_variadic")) == abi.cVariadic &&
      (← IO.ofExcept (oracle.getObjValAs? Nat "fixed_count")) == abi.fixedCount &&
      (← IO.ofExcept (convention.getObjValAs? String "kind")) == "rust" do
    throw (IO.userError "actual compiler ABI header differs")
  let expectedReturn ← IO.ofExcept (oracle.getObjVal? "return_mode")
  let expectedReturn ← IO.ofExcept (JsonReader.run (DecoderValues.parseAbiPassMode "$.return_mode") expectedReturn.compress)
  unless abi.returnValue.mode == expectedReturn do throw (IO.userError "actual compiler return mode differs")
  let expectedArgs ← IO.ofExcept (oracle.getObjValAs? (Array Json) "argument_modes")
  unless abi.arguments.size == expectedArgs.size do throw (IO.userError "actual compiler argument count differs")
  for (actual,expected) in abi.arguments.zip expectedArgs do
    let expected ← IO.ofExcept (JsonReader.run (DecoderValues.parseAbiPassMode "$.argument_mode") expected.compress)
    unless actual.mode == expected do throw (IO.userError "actual compiler complete argument mode differs")
  let cases : Array (String × SourceTypes.Concrete × SourceTypes.Concrete) := #[
    ("unsafe",.functionPointer #[] (.tuple #[]) .Unsafe .Rust false,.tuple #[]),
    ("C ABI",.functionPointer #[] (.tuple #[]) .Safe (.C false) false,.tuple #[]),
    ("input tuple mismatch",.functionPointer #[.primitive "uint" "u8"] (.tuple #[]) .Safe .Rust false,.tuple #[]),
    ("Output mismatch",.functionPointer #[] (.primitive "uint" "u8") .Safe .Rust false,.tuple #[])]
  for (name,pointer,output) in cases do
    let (updated,pointer) ← IO.ofExcept (SourcePhysical.intern world pointer)
    let (updated,output) ← IO.ofExcept (SourcePhysical.intern updated output)
    match demand updated declaration.definition pointer output with
    | .error _ => IO.println s!"rejected {name}"
    | .ok _ => throw (IO.userError s!"accepted {name}")
  IO.println "actual std shortbacktrace FnOnce/Output ABI derived with no imported ABI answers"
