import Miri.Input.CompilerInitialSelectedMemoCodec
import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.RuntimeMetadata
import Miri.Input.RuntimeArrayTypes
import Miri.Input.SourceEnvironment

/-! Imported entries retain only typed identities/results. Neither Registered
nor Memo contains a MemoryState, AllocatorWorld, RuntimeArrayTypes.World or a
root Prepared carrying a historical type arena. All reads use current attach. -/
namespace Miri.Input.CompilerInitialSelectedMemo
open Lean Miri.Memory Miri.ABI CompilerInitialAllocation
set_option autoImplicit false
variable {P E K : Type}
inductive Answer where
  | value (type : TypeId) (value : UInt32)
  | allocation (type : TypeId) (root : AllocId)
  deriving Repr, DecidableEq
structure Registered where
  private mk ::
  definition : GenericSubstitution.DefinitionIdentity
  global : CtfeQueryBridge.GlobalId
  callee : Miri.Interpreter.CallInstance
  type : TypeId
private structure Entry where
  key : CtfeQueryBridge.QueryKey
  answer : Answer
  deriving DecidableEq
structure Memo where
  private mk ::
  run : Nat
  registered : Registered
  private entries : Array Entry
  blocked : Bool := false
  executions : Nat := 0
  lastPCs : Array (Nat × Nat) := #[]

def Memo.beginQuery (memo : Memo) : Memo := {memo with lastPCs := #[]}

def memoSize (memo : Memo) : Nat := memo.entries.size
def cached (memo : Memo) (key : CtfeQueryBridge.QueryKey) : Option Answer :=
  (memo.entries.find? (fun entry => decide (entry.key = key))).map (·.answer)
def queryKey (registered : Registered) (family : CtfeQueryBridge.Family)
    (mode : CompilerTypingEnv.Mode) : CtfeQueryBridge.QueryKey :=
  ⟨family,⟨⟨#[]⟩,mode⟩,registered.global⟩
private def sourceInstance (owner : GenericSubstitution.DefinitionIdentity) : Json :=
  Json.mkObj [("kind",Json.mkObj [("kind",toJson "item"),("definition",Json.mkObj
    [("crate",toJson owner.crateIndex),("index",toJson owner.index)])]),("arguments",Json.arr #[])]
private def isU32 (world : TypeArena.World) (type : TypeId) : Except String Unit := do
  let shape ← match ← world.lookupType type with
    | .constructed shape => pure (some shape) | .material node => world.materialKey node
  unless shape == some (.integer false .u32) do throw "selected memo source type is not actual World u32"
private def resultType (raw : Json) (expected : TypeId) (world : TypeArena.World) :
    Except String TypeArena.World := do
  let (actual,world) ← (RawSymbols.type raw).run world
  isU32 world actual
  unless actual == expected do throw "selected memo result type differs from declared source u32"
  pure world

def readAllocationValue (target : TargetDataLayout) (type : TypeId) (root : AllocId)
    (types : RuntimeArrayTypes.World) (world : AllocatorWorld P E K) : Except String UInt32 := do
  isU32 types.arena type
  let some global := world.memory.findGlobal? root | throw "selected memo allocation root is not a current global"
  let some (.memory allocation) := global.payload | throw "selected memo ConstAlloc is not actual memory"
  unless global.kind == .memory && allocation.byteSize == Size.ofBytes 4 && allocation.mutability == .Not do
    throw "selected memo ConstAlloc size/kind/mutability differs from u32"
  unless allocation.provenanceMap.ptrs.isEmpty &&
      (allocation.provenanceMap.byteFragments.getD #[]).isEmpty do
    throw "selected memo u32 ConstAlloc contains pointer provenance"
  let scalar ← (allocation.readScalar target (allocRange .ZERO (Size.ofBytes 4)) false).mapError toString
  scalar.toUInt32.mapError reprStr

private def importAllocation (target : TargetDataLayout) (u32Alignment : UInt64) (snapshot : Snapshot) (run : Nat)
    (sourceId : UInt64) (type : TypeId) (types : RuntimeArrayTypes.World)
    (world : AllocatorWorld P E K) : Except String AllocId := do
  let rows := snapshot.globals.filter (fun row => row.source == sourceId)
  let some row := rows[0]? | throw "cached ConstAlloc source ID absent from frozen global map"
  unless rows.size == 1 do throw "cached ConstAlloc source ID is ambiguous"
  let .memory expected := row.key | throw "cached ConstAlloc source global is not memory"
  let some root := CompilerInitialAllocation.runtime? world run sourceId
    | throw "cached ConstAlloc source ID has no actual run crosswalk"
  let actualKeys := world.symbolic.filter (fun entry => entry.1 == root)
  let some actual := actualKeys[0]? | throw "cached ConstAlloc has no installed typed global key"
  unless actualKeys.size == 1 && actual.2 == .memory expected do
    throw "cached ConstAlloc full frozen MemoryKey differs from installed source binding"
  unless expected.bytes.size == 4 && expected.alignment == u32Alignment && !expected.mutable &&
      expected.pointerBytes == (Size.fromBits target.pointerWidth.bits).bytes &&
      expected.littleEndian == (target.endian == .little) do
    throw "cached ConstAlloc source MemoryKey is outside exact u32 target layout"
  let some current := world.memory.findGlobal? root | throw "cached root global disappeared"
  let some (.memory allocation) := current.payload | throw "cached root memory payload disappeared"
  let backing ← (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len).mapError toString
  let alignment ← allocation.align.bytes.mapError reprStr
  let actual : MemoryKey := {
    bytes := backing, initMask := allocation.initializationMask, alignment := alignment,
    mutable := allocation.mutability == .Mut,
    pointerBytes := (Size.fromBits target.pointerWidth.bits).bytes,
    littleEndian := target.endian == .little, provenance := allocation.provenanceMap }
  unless actual == expected do throw "cached ConstAlloc current full payload differs from exact frozen MemoryKey"
  let _ ← readAllocationValue target type root types world
  pure root

/-- Exact captured slots only. A compatible memory global never creates an
entry, and a cached scalar never creates a root/allocation-family entry. -/
def importRaw (runtime : RuntimeMetadata) (snapshot : Snapshot) (run : Nat) (raw : Raw)
    (currentTypes : RuntimeArrayTypes.World) (world : AllocatorWorld P E K) :
    Except String (Memo × RuntimeArrayTypes.World) := do
  if world.memory.sourceAllocIdWorldActive then
    throw "selected initial memo cannot attach to prepared allocator profile"
  let target := runtime.target.base
  let u32Alignment ← runtime.target.i32Align.bytes.mapError reprStr
  unless target.pointerWidth.bits.toNat == 64 && target.endian == .little do
    throw "selected initial memo target scope is little-endian 64-bit"
  let some (_,next) := world.runs.find? (fun row => row.1 == run) | throw "selected memo source run absent"
  unless next == snapshot.next && snapshot.next != 0 do throw "selected memo initial source frontier differs"
  let (key,arena) ← (RawSymbols.decodeInstance (sourceInstance raw.definition)).run currentTypes.arena
  let .Item _ := key.kind | throw "selected memo source is not an actual Item"
  unless key.definition == raw.definition && key.arguments.isEmpty do throw "selected memo physical identity differs"
  let lookup : SourceEnvironment.Lookup := fun identity => do
    let some source := currentTypes.metadata.source.definitions.find? (fun source => source.crateIndex == identity.crateIndex && source.index == identity.index)
      | throw "selected memo declaration scope absent"
    let some material := source.sourceEnvironment | throw "selected memo source declaration predicates absent"
    pure material
  unless (← SourceEnvironment.instantiate lookup 16384 raw.definition #[]).isEmpty do
    throw "selected memo declaration has nonempty source predicates"
  let (type,arena) ← (RawSymbols.type raw.sourceType).run arena
  isU32 arena type
  let types := {currentTypes with arena}
  let (callee,types) ← (RuntimeArrayTypes.internInstance key.kind key.arguments).run types
  let registered : Registered := ⟨raw.definition,⟨key,none⟩,callee,type⟩
  let mut types := types
  let mut entries : Array Entry := #[]
  for slot in raw.slots do
    if let some answer := slot.answer then
      let (answer,arena) ← match answer with
        | .value bits rawType => do
          let arena ← resultType rawType type types.arena
          pure (Answer.value type bits,arena)
        | .allocation sourceId rawType => do
          let arena ← resultType rawType type types.arena
          let root ← importAllocation target u32Alignment snapshot run sourceId type {types with arena} world
          pure (Answer.allocation type root,arena)
      types := {types with arena}
      entries := entries.push ⟨queryKey registered slot.family slot.mode,answer⟩
  -- Validate captured successful scalar/allocation consistency without adding
  -- any absent key. The scalar remains the captured ScalarInt, not a heap guess.
  for entry in entries do
    if let .value _ bits := entry.answer then
      for allocationEntry in entries do
        if let .allocation allocationType root := allocationEntry.answer then
          unless (← readAllocationValue target allocationType root types world) == bits do
            throw "captured selected scalar differs from captured ConstAlloc bytes"
  pure (⟨run,registered,entries,false,0,#[]⟩,types)
/-- Current attach validates the typed identity handles, never restores a
historical arena or heap from the memo. -/
def validateCurrent (memo : Memo) (types : RuntimeArrayTypes.World) : Except String Unit := do
  isU32 types.arena memo.registered.type
  let actual ← match ← types.instances.lookup memo.registered.callee with
    | .material key | .constructed key => pure key
  unless actual == memo.registered.global.callee && actual.definition == memo.registered.definition do
    throw "selected memo attached to a different source instance/type World"

/-- Codegen's successful PostAnalysis retry copies a RESULT from its exact
cached dependency. No absent family or root identity is inferred. -/
def Memo.completeRetry (memo : Memo) (family : CtfeQueryBridge.Family) : Except String Memo := do
  let source := queryKey memo.registered family .postAnalysis
  let destination := queryKey memo.registered family .codegen
  let some answer := cached memo source | throw "selected PostAnalysis retry result absent"
  if (cached memo destination).isSome then pure memo
  else pure {memo with entries := memo.entries.push ⟨destination,answer⟩}

structure Registry where
  private mk ::
  run : Nat
  memos : Array Memo

def Registry.commitMemo (registry : Registry) (index : Nat) (memo : Memo) : Except String Registry := do
  let some previous := registry.memos[index]? | throw "selected memo registry index absent"
  unless memo.run == registry.run && memo.registered.global == previous.registered.global &&
      memo.registered.type == previous.registered.type && memo.registered.callee == previous.registered.callee do
    throw "selected memo registry update changes its source/run identity"
  if bounded : index < registry.memos.size then
    pure {registry with memos := registry.memos.set index memo bounded}
  else throw "selected memo registry index absent"

/-- Read every selected table transactionally. Duplicates/unsupported entries
reject the entire registry, never a filtered successful subset. -/
def importTables (runtime : RuntimeMetadata) (snapshot : Snapshot) (run : Nat) (tables : Array Json)
    (currentTypes : RuntimeArrayTypes.World) (world : AllocatorWorld P E K) :
    Except String (Registry × RuntimeArrayTypes.World) := do
  let mut types := currentTypes
  let mut memos : Array Memo := #[]
  for table in tables do
    let raw ← decode table
    let (memo,nextTypes) ← importRaw runtime snapshot run raw types world
    if memos.any (fun previous => decide (previous.registered.global = memo.registered.global)) then
      throw "selected initial memo repeats a GlobalId"
    memos := memos.push memo
    types := nextTypes
  pure (⟨run,memos⟩,types)

end Miri.Input.CompilerInitialSelectedMemo
