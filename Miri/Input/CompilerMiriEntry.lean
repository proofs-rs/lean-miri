import Miri.Input.CompilerProviders

/-! Pinned eval.rs::entry_fn (39–69). Prefer rustc's selected main; otherwise
require one compiler-owned local exported miri_start with its exact signature.
Caller-supplied entry configuration never substitutes for these queries. -/
namespace Miri.Input.CompilerMiriEntry
open Miri.Interpreter

def miriStart (compiler : CompilerProviders.Prepared) :
    Except String MIR.DefId := do
  -- Pinned eval.rs::entry_fn considers only a local exported miri_start
  -- after rustc declines to select main, and checks its exact Rust signature.
  let symbols ← compiler.foreignSymbols
  let candidates := symbols.candidates.filter fun candidate =>
    candidate.crateIndex == 0 && candidate.explicitSymbol && candidate.symbol == "miri_start"
  let #[candidate] := candidates | throw "missing or ambiguous local exported miri_start"
  let some fnInstance := candidate.fnInstance | throw "miri_start export is not a function"
  let .Item definition ← CompilerInstance.kindOf compiler.program.input.instances fnInstance
    | throw "miri_start export is not a monomorphic item"
  let some entry := compiler.main.entries.find? (·.definition == definition)
    | throw "miri_start lacks exact compiler entry signature queries"
  let signature ← entry.signature
  if signature.hasBoundVariables || signature.outputHasBoundVariables then
    throw "miri_start signature has bound variables"
  let typeShape := fun id => do
    let some node := compiler.program.input.types.find? (·.id == id)
      | throw "miri_start signature references a missing compiler type"
    pure node.shape
  let .functionPointer fnSig boundVariables ← typeShape signature.fnPointerType
    | throw "miri_start signature query is not a function pointer"
  unless signature.returnType == fnSig.output do
    throw "miri_start return query disagrees with its function pointer signature"
  unless boundVariables.isEmpty && fnSig.abi == .Rust && fnSig.safety == .Safe && !fnSig.cVariadic do
    throw "miri_start requires a non-variadic safe Rust ABI signature"
  let #[argc, argv] := fnSig.inputs | throw "miri_start requires exactly argc and argv"
  let .int (.known .isize) ← typeShape argc | throw "miri_start argc must be isize"
  let .int (.known .isize) ← typeShape fnSig.output | throw "miri_start return type must be isize"
  let .rawPointer inner .Not ← typeShape argv | throw "miri_start argv must be *const *const u8"
  let .rawPointer byte .Not ← typeShape inner | throw "miri_start argv must be *const *const u8"
  let .uint (.known .u8) ← typeShape byte | throw "miri_start argv must be *const *const u8"
  pure definition

def select (compiler : CompilerProviders.Prepared) :
    Except String (MIR.DefId × MainEntryType) := do
  if let some entry ← CompilerMain.sourceCompilerEntry compiler.main then
    return entry
  return (← miriStart compiler, .miriStart)

end Miri.Input.CompilerMiriEntry
