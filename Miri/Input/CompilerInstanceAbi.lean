import Miri.Input.CallResolution

/-! Exact fn_abi_of_instance evidence. A full instance, ordered additional
argument-type vector and explicit typing environment form the key. Runtime drop
and virtual calls use the same table as observed direct/variadic calls. -/
namespace Miri.Input.CompilerInstanceAbi
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  callee : CallInstance
  extra : Array MIR.TyId
  result : Except String Nat

structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  entries : Array Entry
  private index : Std.HashMap Nat (Array Nat) := {}

private def keyMatches (entries : Array Entry) (index : Nat)
    (callee : CallInstance) (extra : Array MIR.TyId) : Bool :=
  match entries[index]? with
  | some entry => entry.callee == callee && entry.extra == extra
  | none => false

private def matchingIndex (entries : Array Entry) (indices : Array Nat)
    (callee : CallInstance) (extra : Array MIR.TyId) : Option Nat :=
  indices.find? fun index => keyMatches entries index callee extra

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let records := program.input.queries.instanceAbis
  let ctx := LowerContext.ofDocument program.input
  let tables := program.compilerTables
  let mut entries := #[]
  let mut buckets : Std.HashMap Nat (Array Nat) := {}
  for record in records do
    let callee := record.instanceId
    let _ ← CompilerInstance.source ctx.instances callee
    let extra := record.extraArgumentTypes
    for id in extra do
      unless ctx.containsTypeId id do throw "extra ABI argument references missing compiler type"
    let result : Except String Nat := .ok record.abiId
    let candidates := buckets.getD callee #[]
    if let some previousIndex := matchingIndex entries candidates callee extra then
      let some previous := entries[previousIndex]? | throw "instance ABI bucket index invariant"
      match previous.result,result with
      | .ok old,.ok fresh => unless old == fresh do throw "conflicting exact instance ABI evidence"
      | .error old,.error fresh => unless old == fresh do throw "conflicting failed instance ABI evidence"
      | _,_ => throw "conflicting instance ABI query outcomes"
    else
      let index := entries.size
      entries := entries.push ⟨callee,extra,result⟩
      buckets := buckets.insert callee ((buckets.getD callee #[]).push index)
  pure ⟨runtime,program.withCompilerTables tables,entries,buckets⟩

def abiOfInstance (prepared : Prepared) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (FnAbi MIR.TyId) := do
  let found := matchingIndex prepared.entries
    (prepared.index.getD callee #[]) callee extra
  let some entryIndex := found
    | throw "missing exact full-instance/extra-argument FnAbi query"
  let some entry := prepared.entries[entryIndex]?
    | throw "instance ABI bucket index invariant"
  CallResolution.functionAbiId prepared.runtime (← entry.result)

def hooks (prepared : Prepared)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with fnAbiOfInstance := fun _ callee extra =>
      match abiOfInstance prepared callee extra with
      | .ok abi => pure abi
      | .error error => throw (.invalidProgram error) }
end Miri.Input.CompilerInstanceAbi
