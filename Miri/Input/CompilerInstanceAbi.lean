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

private def buildBuckets (entries : Array Entry) : Std.HashMap Nat (Array Nat) := Id.run do
  let mut buckets : Std.HashMap Nat (Array Nat) := {}
  for index in [:entries.size] do
    if let some entry := entries[index]? then
      let key := entry.callee
      buckets := buckets.insert key ((buckets.getD key #[]).push index)
  return buckets

set_option autoImplicit false in
private structure InstanceBuckets (entries : Array Entry) where
  mk ::
  buckets : Std.HashMap Nat (Array Nat)
  exact : buckets = buildBuckets entries

private def instanceBuckets (entries : Array Entry) : InstanceBuckets entries :=
  ⟨buildBuckets entries, rfl⟩

structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  entries : Array Entry
  /-- A private checked index tied to this exact immutable entries array. A
  manually constructed Prepared has no index and keeps the historical scan. -/
  private index : Option (InstanceBuckets entries) := none

private def keyMatches (entries : Array Entry) (index : Nat)
    (callee : CallInstance) (extra : Array MIR.TyId) : Bool :=
  match entries[index]? with
  | some entry => entry.callee == callee && entry.extra == extra
  | none => false

private def matchingIndex (entries : Array Entry) (indices : Array Nat)
    (callee : CallInstance) (extra : Array MIR.TyId) : Option Nat :=
  indices.find? fun index => keyMatches entries index callee extra

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let records ← (← program.input.raw.getObjVal? "compiler_instance_abis").getArr?
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  let mut buckets : Std.HashMap Nat (Array Nat) := {}
  for record in records do
    unless (← (← record.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "instance ABI query typing environment mismatch"
    let (callee,next) ← CompilerInstance.decode ctx tables record
    tables := next
    let extra ← (← (← record.getObjVal? "extra_argument_types").getArr?).mapM fun ty => do
      let id ← ty.getNat?
      unless ctx.containsTypeId id do throw "extra ABI argument references missing compiler type"
      pure id
    let result := do
      let query ← record.getObjVal? "abi_query"
      query.getNat?
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
  pure ⟨runtime,program.withCompilerTables tables,entries,some (instanceBuckets entries)⟩

def abiOfInstance (prepared : Prepared) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (FnAbi MIR.TyId) := do
  let found := match prepared.index with
    | some index => matchingIndex prepared.entries
        (index.buckets.getD callee #[]) callee extra
    | none => Array.findIdx? (fun (entry : Entry) =>
        entry.callee == callee && entry.extra == extra) prepared.entries
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
