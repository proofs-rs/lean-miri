import Lean.Util.Profile
import Miri.Input.AllocationImage
import Miri.Interpreter.GlobalByteMachine
import Miri.Input.Decoder

/-! Import exact TCX byte/salt identity evidence. Probes that miss the imported
compiler image do not create runtime globals; subsequent reservation stays lazy.
Completeness is checked against every qualifying immutable imported allocation,
not inferred from a catalog that merely happens to contain some literals. -/
namespace Miri.Input.CompilerGlobalBytes
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
structure Prepared where
  strType : TyId
  keys : Array (Array UInt8 × Fin 32 × AllocId)

private def hexBytes (value : String) : Except String (Array UInt8) := do
  let chars := value.toList.toArray
  unless chars.size % 2 == 0 do throw "global byte query has odd hex length"
  let digit := fun c =>
    if c ≥ '0' && c ≤ '9' then Except.ok (c.toNat - '0'.toNat)
    else if c ≥ 'a' && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error "global byte query has invalid hex"
  let mut bytes := #[]
  for i in [:chars.size / 2] do
    let some hi := chars[2*i]? | throw "global byte hex high digit absent"
    let some lo := chars[2*i+1]? | throw "global byte hex low digit absent"
    bytes := bytes.push (UInt8.ofNat (16*(← digit hi)+(← digit lo)))
  pure bytes

private def matchesHex (hex : String) (bytes : Array UInt8) : Bool := Id.run do
  let text := hex.toUTF8
  unless text.size == 2 * bytes.size do return false
  let digit := fun n => UInt8.ofNat (if n < 10 then n + 48 else n + 87)
  for index in [:bytes.size] do
    let some raw := bytes[index]? | return false
    let some hi := text[2 * index]? | return false
    let some lo := text[2 * index + 1]? | return false
    let byte := raw.toNat
    unless hi == digit (byte / 16) && lo == digit (byte % 16) do
      return false
  return true

private def candidate (global : GlobalAllocation) : Except String (Option (Array UInt8)) := do
  let some (.memory allocation) := global.payload | return none
  if allocation.mutability != .Not || allocation.align != .ONE then return none
  unless allocation.provenanceMap.provenances.isEmpty do return none
  if allocation.len != 0 then
    let initialized ← allocation.initializationMask.isRangeInitialized
      (allocRange .ZERO allocation.byteSize) |>.mapError toString
    unless initialized.isOk do return none
  return some (← allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len |>.mapError toString)

/-- Attach immediately after graph import, before source runtime reservations.
The exported graph must be the same complete identity universe that was probed.
Compiler pool identity/serialization remains an explicit exporter trust boundary. -/
def prepare (program : LoweredProgram) (runtime : RuntimeMetadata)
    (memory : MemoryState P E K) : Except String Prepared := do
  if memory.activeInitialCompilerRun.isSome then
    throw "initial profile requires complete typed byte preparation, not the legacy catalog"
  if memory.byteGlobalKeysReady || !memory.byteGlobalKeys.isEmpty then
    throw "global byte keys already initialized"
  let source := program.input.queries.globalBytes
  unless source.saltCount == 32 do throw "global byte salt support differs from pinned source"
  let mut keys := #[]
  if let some world := program.input.compilerAllocIdWorld then
    unless memory.sourceAllocIdWorldActive do
      throw "prepared source AllocId world was not installed before byte-key attachment"
    let mut runtimeByGraph : Std.HashMap Nat AllocId := {}
    for (graphId, runtimeId) in memory.importedGlobalIds do
      if runtimeByGraph.contains graphId then throw "duplicate imported graph ID while preparing byte-key catalog"
      runtimeByGraph := runtimeByGraph.insert graphId runtimeId
    let mut seen : Std.HashMap (Array UInt8 × Nat) Bool := {}
    for row in world.dedupCatalog do
      if row.keyKind == .bytes then
        let some imageHex := row.byteImageHex | throw "prepared byte-key catalog row lacks its exact image"
        let some keyNode := program.input.allocations[row.keyAllocationId]? |
          throw "prepared byte-key catalog key allocation is absent"
        unless keyNode.id == row.keyAllocationId && keyNode.kind == .memory do
          throw "prepared byte-key catalog key graph identity/kind disagrees"
        let some (.memory image) := keyNode.data | throw "prepared byte-key catalog key is not memory"
        unless image.mutability == .immutable && image.alignBytes == 1 && image.relocations.isEmpty &&
            image.initializationRanges.all (·.initialized) do
          throw "prepared byte-key catalog key is not eligible immutable memory"
        let bytes ← image.bytesHex.checkedBytes
        unless matchesHex imageHex bytes do
          throw "prepared byte-key catalog image differs from its key allocation"
        for result in row.salts do
          if proof : result.salt < 32 then
            let some id := runtimeByGraph[result.allocationId]? | throw s!"missing runtime mapping for compiler allocation {result.allocationId}"
            unless memory.sourceAllocIdForRuntime? id == some result.sourceAllocId do
              throw "prepared byte result raw AllocId does not match the active memory world"
            if seen.contains (bytes, result.salt) then
              throw "prepared source AllocId world contains duplicate byte key/salt results"
            seen := seen.insert (bytes, result.salt) true
            keys := keys.push (bytes,⟨result.salt,proof⟩,id)
          else throw "prepared source AllocId world byte-key salt exceeds 31"
  else
    let ids := source.coveredAllocations
    let expected := program.input.allocations.map (·.id)
    let mut expectedIds : Std.HashMap Nat Bool := {}
    for id in expected do
      if expectedIds.contains id then throw "duplicate imported graph allocation identity"
      expectedIds := expectedIds.insert id true
    let mut coveredIds : Std.HashMap Nat Bool := {}
    for id in ids do
      if coveredIds.contains id then throw "duplicate global byte coverage identity"
      coveredIds := coveredIds.insert id true
    unless coveredIds.size == expectedIds.size &&
        ids.all expectedIds.contains do
      throw "global byte query coverage differs from imported graph"
    let mapped ← ids.mapM (AllocationImage.runtimeId memory)
    let actual := memory.globals.map (·.allocId)
    let mut actualIds : Std.HashMap UInt64 Bool := {}
    for id in actual do
      if actualIds.contains id.value then throw "duplicate imported runtime allocation identity"
      actualIds := actualIds.insert id.value true
    let mut mappedIds : Std.HashMap UInt64 Bool := {}
    for id in mapped do
      if mappedIds.contains id.value then throw "duplicate mapped runtime allocation identity"
      mappedIds := mappedIds.insert id.value true
    unless mappedIds.size == actualIds.size && mapped.all (fun id => actualIds.contains id.value) do
      throw "global byte keys must attach before runtime global reservations"
    let mut candidates := #[]
    for global in memory.globals do
      if let some bytes ← candidate global then candidates := candidates.push (bytes,global.allocId)
    let mut seen : Array (Array UInt8) := #[]
    for row in source.candidates do
      let bytes ← hexBytes row.bytesHex
      unless candidates.any (·.1 == bytes) do throw "global byte query contains a noncandidate allocation"
      if seen.contains bytes then throw "duplicate global byte query content"
      seen := seen.push bytes
      let salts := row.salts
      unless salts.size == 32 do throw "global byte candidate omits salt outcomes"
      for index in [:32] do
        let some result := salts[index]? | throw "global byte salt result absent"
        unless result.1 == index do throw "global byte salt index mismatch"
        if let some allocation := result.2 then
          let id ← AllocationImage.runtimeId memory allocation
          unless candidates.any (fun entry => entry.1 == bytes && entry.2 == id) do
            throw "global byte salt query refers to incompatible global contents"
          if proof : index < 32 then keys := keys.push (bytes,⟨index,proof⟩,id)
          else throw "global byte salt exceeds support"
    unless candidates.all (fun entry => seen.contains entry.1) do
      throw "global byte query omits imported candidate content"
  let strType := source.strType
  let node ← runtime.node strType |>.mapError toString
  unless node.shapeKind == .str do
    throw "global byte str type is not the compiler str primitive"
  pure ⟨strType,keys⟩

def attachProfiled (profile : Lean.Options) (program : LoweredProgram) (runtime : RuntimeMetadata) : MachineHooks.M K U Prepared := do
  let state ← get
  let prepared ← match profileit "startup.alloc_bytes" profile fun _ =>
      prepare program runtime state.machine.memory with
    | .ok value => pure value | .error error => throw (.unsupported error)
  modify fun state => {state with machine := {state.machine with memory :=
    {state.machine.memory with byteGlobalKeys := prepared.keys, byteGlobalKeysReady := true}}}
  pure prepared

def attach (program : LoweredProgram) (runtime : RuntimeMetadata) :
    MachineHooks.M K U Prepared :=
  attachProfiled {} program runtime

theorem attach_profile_identity {K U : Type} (program : LoweredProgram) (runtime : RuntimeMetadata) :
    attach (K := K) (U := U) program runtime =
      attachProfiled (K := K) (U := U) {} program runtime := rfl

def strLayout (runtime : RuntimeMetadata) (prepared : Prepared) : MachineHooks.M K U LocalLayout :=
  match runtime.lookup prepared.strType with
  | .ok value => pure value | .error error => throw (.unsupported (toString error))
end Miri.Input.CompilerGlobalBytes
