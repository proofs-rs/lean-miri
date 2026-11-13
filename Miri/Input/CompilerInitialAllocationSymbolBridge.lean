import Miri.Input.CompilerInitialAllocationSymbols
import Miri.Input.CompilerInitialAllocationCodec

/-! Transactional raw-descriptor construction before strict snapshot decoding.
Only a successful result exposes the candidate type universe. Vtable binder
construction retains the full binder/body sequence using existing typed syntax.
Static source descriptors carry raw type/flags; compiler size/alignment answers
are forbidden by the strict Codec and cannot seed the execution World. -/
namespace Miri.Input.CompilerInitialAllocation.SymbolBridge
open Lean TypeArena
set_option autoImplicit false
structure Cache where
  functions : Array (Json × InstanceArena.Key) := #[]
  types : Array (Json × TypeId) := #[]
  predicates : Array (Json × Array VtablePredicate) := #[]
private def prepareKey (j : Json) (cache : Cache) (world : World) : Except String (Cache × World) := do
  match ← (← j.getObjVal? "kind").getStr? with
  | "memory" => pure (cache,world)
  | "static" =>
    let definition ← GenericMaterialCodec.readDefinition (← j.getObjVal? "definition")
    let _ ← world.definitionRef definition
    let .ok info := j.getObjVal? "static_info" | pure (cache,world)
    let rawType ← info.getObjVal? "source_type"
    if rawType == .null then pure (cache,world) else do
      let (ty,world) ← (RawSymbols.type rawType).run world
      pure ({cache with types := cache.types.push (rawType,ty)},world)
  | "function" =>
    let raw ← j.getObjVal? "instance"
    if cache.functions.any (fun row => row.1 == raw) then pure (cache,world) else do
      let (value,world) ← (RawSymbols.decodeInstance raw).run world
      pure ({cache with functions := cache.functions.push (raw,value)},world)
  | "type_id" =>
    let raw ← j.getObjVal? "type"
    if cache.types.any (fun row => row.1 == raw) then pure (cache,world) else do
      let (value,world) ← (RawSymbols.type raw).run world
      pure ({cache with types := cache.types.push (raw,value)},world)
  | "vtable" =>
    let rawType ← j.getObjVal? "type"
    let (ty,world) ← (RawSymbols.type rawType).run world
    let rawPredicates ← j.getObjVal? "predicates"
    let (predicates,world) ← (RawSymbols.predicates rawPredicates).run world
    pure ({cache with types := cache.types.push (rawType,ty),predicates := cache.predicates.push (rawPredicates,predicates)},world)
  | _ => throw "unknown raw snapshot global kind"
def decode (pointerBytes : UInt64) (littleEndian : Bool) (j : Json) (original : World) :
    Except String (Snapshot × World) := do
  let mut candidate := original
  let mut cache : Cache := {}
  for row in ← (← j.getObjVal? "globals").getArr? do
    let result ← prepareKey (← row.getObjVal? "value") cache candidate
    cache := result.1
    candidate := result.2
  for row in ← (← j.getObjVal? "dedup").getArr? do
    let result ← prepareKey (← row.getObjVal? "key") cache candidate
    cache := result.1
    candidate := result.2
  let symbols : Symbols := {
    pointerBytes, littleEndian
    function := fun raw => match cache.functions.find? (fun row => row.1 == raw) with
      | some row => .ok row.2 | none => .error "raw instance absent from candidate World"
    type := fun raw => match cache.types.find? (fun row => row.1 == raw) with
      | some row => .ok row.2 | none => .error "raw type absent from candidate World"
    predicates := fun raw => match cache.predicates.find? (fun row => row.1 == raw) with
      | some row => .ok row.2 | none => .error "raw predicates absent from candidate World" }
  let snapshot ← CompilerInitialAllocation.decode symbols j
  pure (snapshot,candidate)
end Miri.Input.CompilerInitialAllocation.SymbolBridge
