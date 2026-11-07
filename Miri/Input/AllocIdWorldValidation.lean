import Miri.Input.Model

/-! Relations of the typed prepared allocation-ID world. JSON transport checks
remain at the reader boundary; runtime installation never reparses raw JSON or
uses diagnostic payload equality to establish allocation identity. -/
namespace Miri.Input.AllocIdWorldValidation
open Miri.Interpreter

private def lowerHex (value : String) : Bool :=
  value.length % 2 == 0 && value.toList.all (fun c =>
    (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))

private def allocationNodeMatchesSourceKind (source : SourceAllocIdKind) (node : AllocationKind) : Bool :=
  match source,node with
  | .memory,.memory | .function,.function | .vtable,.vtable | .static,.static | .typeId,.typeId => true
  | .static,.other "static_initializer_error" => true
  | _,_ => false

private def validatePoolRow (row : SourceAllocIdPoolRow) (path : String) : Except String Unit := do
  let shape := match row.kind,row.status,row.allocationId with
    | .dangling,.dangling,none => row.opaqueAllocationId.isNone
    | .memory,.serialized,some _ | .function,.serialized,some _ | .vtable,.serialized,some _ |
      .static,.serialized,some _ | .typeId,.serialized,some _ => row.opaqueAllocationId.isNone
    | .memory,.opaque,none | .function,.opaque,none | .vtable,.opaque,none |
      .static,.opaque,none | .typeId,.opaque,none => true
    | _,_,_ => false
  unless shape do throw s!"{path}: inconsistent kind/status/allocation_id in source AllocId pool row"
  if row.kind == .memory then
    unless row.memoryMutability == some .immutable || row.memoryMutability == some .mutable do
      throw s!"{path}: unsupported memory projection mutability"
    unless row.memoryAlignBytes.isSome && row.memoryAllBytesInitialized.isSome && row.memoryHasProvenance.isSome do
      throw s!"{path}: missing memory projection dimensions"
  else unless row.memoryMutability.isNone && row.memoryAlignBytes.isNone &&
      row.memoryAllBytesInitialized.isNone && row.memoryHasProvenance.isNone do
    throw s!"{path}: non-memory row carries a memory projection"
  if let some bytes := row.byteImageHex then
    unless lowerHex bytes do throw s!"{path}.byte_image_hex: expected canonical lowercase hexadecimal"
  let eligible := row.kind == .memory && row.memoryMutability == some .immutable && row.memoryAlignBytes == some 1 &&
    row.memoryAllBytesInitialized == some true && row.memoryHasProvenance == some false
  match row.kind,eligible,row.byteImageHex with
  | .memory,true,some _ =>
    unless row.status == .serialized && row.allocationId.isSome do
      throw s!"{path}: eligible byte-memory key requires a serialized allocation node"
  | .memory,false,none => pure ()
  | .memory,_,_ => throw s!"{path}: inconsistent byte-memory eligibility and image"
  | _,_,none => pure ()
  | _,_,some _ => throw s!"{path}: byte-memory image is only valid for memory globals"

private def validateDedupRow (row : SourceAllocIdDedupRow) (path : String) : Except String Unit := do
  if let some image := row.byteImageHex then
    unless lowerHex image do throw s!"{path}.bytes_hex: expected canonical lowercase hexadecimal"
  match row.keyKind,row.byteImageHex with
  | .bytes,some _ => pure ()
  | .function,none | .vtable,none | .static,none | .typeId,none | .memory,none => pure ()
  | .bytes,none => throw s!"{path}.bytes_hex: required for byte-image dedup key"
  | _,some _ => throw s!"{path}.bytes_hex: only valid for byte-image dedup key"
  for salt in row.salts do
    unless salt.sourceAllocId != 0 do throw s!"{path}.salts.source_alloc_id: expected nonzero u64"

private def functionKey (input : ImportDocumentCore) (node : AllocationNode) (source : FunctionAllocation) :
    Except String CallInstance := do
  let metadata ← input.mirTables.allocationFunctions.lookup node.id |>.mapError (fun id => s!"function allocation metadata absent: {id}")
  let metadata ← metadata
  unless metadata.instanceId == source.instanceId && metadata.definitionId == source.definitionId do
    throw "function allocation source identity mismatch"
  let callee ← input.mirTables.instance source.instanceId
  unless metadata.callee == callee do throw "function allocation/full-instance generic arguments mismatch"
  unless input.mirTables.compiler.definitions[callee.defId]? == some source.definitionId do
    throw "function allocation/full-instance definition mismatch"
  return callee

private def vtableKey (input : ImportDocumentCore) (node : AllocationNode) (source : VtableAllocation) :
    Except String (TypeId × Array Nat) := do
  let some (some id) := input.vtableTables.allocationMetadata[node.id]? | throw "vtable allocation metadata absent"
  let metadata ← input.vtableTables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
  unless metadata.typeId == source.typeId do throw "vtable allocation type mismatch"
  let predicates ← input.vtableTables.predicateLists.lookup metadata.predicates |>.mapError (fun id => s!"invalid vtable predicates {id}")
  return (metadata.typeId,predicates.values)

/-- Validate typed identities, source projections, salt outcomes and completeness.
The original JSON envelope is diagnostic data, not a second semantic authority. -/
def validate (input : ImportDocumentCore) : Except String Unit := do
  let some world := input.compilerAllocIdWorld | return ()
  let nodes := input.allocations
  let lastNat := world.lastReservedSourceAllocId.toNat
  let nextNat := world.nextSourceAllocId.toNat
  let sentinelNat := world.finalSentinelSourceAllocId.toNat
  if lastNat == 0 || nextNat == 0 then throw "source AllocId frontier must be nonzero"
  unless sentinelNat == lastNat && nextNat == lastNat + 1 do
    throw "source AllocId sentinel, last reservation, and next counter disagree"
  unless world.rawPool.size == lastNat do throw "source AllocId pool does not cover its frontier"
  let mut nodeIndexByGraphId : Std.HashMap Nat Nat := {}
  let mut nodeIndexBySourceId : Std.HashMap Nat Nat := {}
  for (node, index) in nodes.toList.zipIdx do
    if nodeIndexByGraphId.contains node.id then throw "$.compiler_alloc_id_world: duplicate allocation graph identity"
    nodeIndexByGraphId := nodeIndexByGraphId.insert node.id index
    if let some sourceId := node.sourceAllocId then
      if nodeIndexBySourceId.contains sourceId.toNat then
        throw "$.compiler_alloc_id_world: duplicate source AllocId witness on allocation nodes"
      nodeIndexBySourceId := nodeIndexBySourceId.insert sourceId.toNat index
  let mut pool := #[]
  for (row, index) in world.rawPool.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.raw_pool[{index}]"
    validatePoolRow row rowPath
    unless row.sourceAllocId.toNat == index + 1 do
      throw s!"{rowPath}.source_alloc_id: pool rows must be ordered and contiguous from one"
    if row.status == .serialized then
      let some graphId := row.allocationId | throw s!"{rowPath}: serialized pool row lacks graph identity"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId do throw s!"{rowPath}: source AllocId disagrees with allocation node witness"
      unless node.status == .supported do throw s!"{rowPath}: serialized source global lacks supported allocation status"
      let expectedKind := match row.kind with
        | .memory => AllocationKind.memory
        | .function => .function
        | .vtable => .vtable
        | .static => .static
        | .typeId => .typeId
        | .dangling => .unknown
      unless node.kind == expectedKind do throw s!"{rowPath}: source global kind disagrees with allocation node"
      let expectedData : Bool := match row.kind, node.data with
        | .memory, some (.memory _) => true
        | .function, some (.function _) => true
        | .vtable, some (.vtable _) => true
        | .static, some (.static _) => true
        | .typeId, some (.typeId _) => true
        | _, _ => false
      unless expectedData do throw s!"{rowPath}: serialized source global lacks matching typed payload"
      if row.kind == .memory then
        let some projectionMutability := row.memoryMutability | throw s!"{rowPath}: memory projection mutability is absent"
        let some projectionAlign := row.memoryAlignBytes | throw s!"{rowPath}: memory projection alignment is absent"
        let some projectionInitialized := row.memoryAllBytesInitialized | throw s!"{rowPath}: memory projection initialization status is absent"
        let some projectionProvenance := row.memoryHasProvenance | throw s!"{rowPath}: memory projection provenance status is absent"
        let some (.memory image) := node.data | throw s!"{rowPath}: serialized memory node has no memory image"
        let actualMutability := image.mutability
        let actualInitialized := image.initializationRanges.all (·.initialized)
        let actualProvenance := !image.relocations.isEmpty
        unless projectionMutability == actualMutability && projectionAlign == image.alignBytes &&
            projectionInitialized == actualInitialized && projectionProvenance == actualProvenance do
          throw s!"{rowPath}: source byte-key projection disagrees with serialized memory image"
        let actualByteEligible := actualMutability == .immutable && image.alignBytes == 1 &&
          actualInitialized && !actualProvenance
        if actualByteEligible then
          unless row.byteImageHex == some image.bytesHex do
            throw s!"{rowPath}: eligible byte-memory projection differs from serialized bytes"
        else unless row.byteImageHex.isNone do
          throw s!"{rowPath}: ineligible memory image must not publish a byte key"
    else if let some graphId := row.opaqueAllocationId then
      unless row.status == .opaque do throw s!"{rowPath}.opaque_allocation_id: only valid for opaque rows"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.opaque_allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.opaque_allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId && node.status != .supported &&
          allocationNodeMatchesSourceKind row.kind node.kind do
        throw s!"{rowPath}.opaque_allocation_id: source witness does not identify an unsupported allocation of the same source kind"
    else if nodeIndexBySourceId.contains row.sourceAllocId.toNat then
      throw s!"{rowPath}: non-serialized source ID is attached to an allocation node"
    pool := pool.push row
  let some sentinel := pool[pool.size - 1]? | throw "$.compiler_alloc_id_world.raw_pool: sentinel row absent"
  unless sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone do
    throw "$.compiler_alloc_id_world.raw_pool: final reserved sentinel must be dangling"
  for node in nodes do
    let some sourceId := node.sourceAllocId | throw "$.compiler_alloc_id_world: every imported allocation must carry an exact source_alloc_id witness"
    let some row := pool[sourceId.toNat - 1]? | throw "$.compiler_alloc_id_world: allocation witness lies outside captured raw prefix"
    if node.status == .supported then
      unless row.status == .serialized && row.allocationId == some node.id do
        throw "$.compiler_alloc_id_world: supported allocation node is not covered by exactly one serialized pool row"
    else unless row.status == .opaque && row.opaqueAllocationId == some node.id do
      throw "$.compiler_alloc_id_world: unsupported allocation node is not covered by its opaque pool row"
  let mut dedup := #[]
  let mut byteRowByImage : Std.HashMap String Nat := {}
  let mut functionRowByInstance : Std.HashMap InstanceId Nat := {}
  let mut vtableRowsByType : Std.HashMap TypeId (Array (Array Nat)) := {}
  let mut staticDefinitionsSeen : Std.HashMap (Nat × Nat) Nat := {}
  let mut typeIdRowByType : Std.HashMap TypeId Nat := {}
  for (row, index) in world.dedupCatalog.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.dedup_catalog[{index}]"
    validateDedupRow row rowPath
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw s!"{rowPath}.key_kind: dedup key family is not available in this prepared profile"
    let some keyIndex := nodeIndexByGraphId[row.keyAllocationId]? | throw s!"{rowPath}.key_allocation_id: selected key node is not serialized"
    let some keyNode := nodes[keyIndex]? | throw s!"{rowPath}.key_allocation_id: selected key index is absent"
    let expectedKeyKind := match row.keyKind with
      | .bytes => AllocationKind.memory
      | .function => .function
      | .vtable => .vtable
      | .static => .static
      | .typeId => .typeId
      | _ => .unknown
    unless keyNode.kind == expectedKeyKind && keyNode.status == .supported do
      throw s!"{rowPath}: selected key node has incompatible kind/status"
    let expectedSaltCount := if row.keyKind == .static || row.keyKind == .typeId then 1 else 32
    unless row.salts.size == expectedSaltCount do
      throw s!"{rowPath}.salts: selected dedup key has the wrong number of source salt results"
    let mut seenResultAllocations : Std.HashMap Nat Bool := {}
    for (saltResult, saltIndex) in row.salts.toList.zipIdx do
      let expectedSalt := if row.keyKind == .static || row.keyKind == .typeId then 0 else saltIndex
      unless saltResult.salt == expectedSalt do
        throw s!"{rowPath}.salts[{saltIndex}].salt: unexpected source salt for selected dedup key"
      if seenResultAllocations.contains saltResult.allocationId then
        throw s!"{rowPath}.salts[{saltIndex}]: duplicate result allocation across source salts"
      seenResultAllocations := seenResultAllocations.insert saltResult.allocationId true
      let some poolRow := pool[saltResult.sourceAllocId.toNat - 1]? | throw s!"{rowPath}.salts: result AllocId outside captured pool"
      unless poolRow.status == .serialized && poolRow.allocationId == some saltResult.allocationId do
        throw s!"{rowPath}.salts: result must resolve to its unique serialized allocation node"
      let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result allocation node is absent"
      let some resultNode := nodes[resultIndex]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result node index is absent"
      unless resultNode.kind == expectedKeyKind && resultNode.status == .supported do
        throw s!"{rowPath}.salts[{saltIndex}]: result allocation has incompatible kind/status"
      if row.keyKind == .function then
        let some (.function keyFunction) := keyNode.data
          | throw s!"{rowPath}: function key witness lacks typed instance data"
        let some (.function resultFunction) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: function result lacks typed instance data"
        let keyInstance ← functionKey input keyNode keyFunction
        let resultInstance ← functionKey input resultNode resultFunction
        unless keyInstance == resultInstance do
          throw s!"{rowPath}.salts[{saltIndex}]: function result does not match the exact selected Instance key"
      if row.keyKind == .vtable then
        let some (.vtable keyVtable) := keyNode.data
          | throw s!"{rowPath}: vtable key witness lacks typed identity data"
        let some (.vtable resultVtable) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: vtable result lacks typed identity data"
        let keyIdentity ← vtableKey input keyNode keyVtable
        let resultIdentity ← vtableKey input resultNode resultVtable
        unless keyIdentity == resultIdentity do
          throw s!"{rowPath}.salts[{saltIndex}]: vtable result does not match the exact selected type/predicate key"
      if row.keyKind == .static then
        let some (.static keyStatic) := keyNode.data
          | throw s!"{rowPath}: static key witness lacks typed DefId data"
        let some (.static resultStatic) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: static result lacks typed DefId data"
        unless keyStatic.definitionId == resultStatic.definitionId do
          throw s!"{rowPath}.salts[{saltIndex}]: static result does not match the exact selected DefId key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: static key must provide its exact salt-zero typed witness"
      if row.keyKind == .typeId then
        let some (.typeId keyType) := keyNode.data
          | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
        let some (.typeId resultType) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: TypeId result lacks typed Ty data"
        unless keyType == resultType do
          throw s!"{rowPath}.salts[{saltIndex}]: TypeId result does not match the exact selected Ty key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: TypeId key must provide its exact salt-zero typed witness"
    if row.keyKind == .bytes then
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      let some (.memory image) := keyNode.data | throw s!"{rowPath}: byte key node has no memory image"
      let some keySourceId := keyNode.sourceAllocId | throw s!"{rowPath}: byte key node lacks a source identity"
      let some keyPoolRow := pool[keySourceId.toNat - 1]? | throw s!"{rowPath}: byte key node is absent from the source pool"
      unless keyPoolRow.memoryMutability == some .immutable && keyPoolRow.memoryAlignBytes == some 1 &&
          keyPoolRow.memoryAllBytesInitialized == some true && keyPoolRow.memoryHasProvenance == some false &&
          keyPoolRow.byteImageHex == some imageHex && keyNode.memory == some image && image.bytesHex == imageHex &&
          image.mutability == .immutable && image.alignBytes == 1 && image.relocations.isEmpty &&
          image.initializationRanges.all (·.initialized) do
        throw s!"{rowPath}: byte key image is not the exact immutable aligned initialized provenance-free source key"
      for saltResult in row.salts do
        let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
          | throw s!"{rowPath}.salts: byte-key result node is absent"
        let some resultNode := nodes[resultIndex]? | throw s!"{rowPath}.salts: result node index is absent"
        let some (.memory resultImage) := resultNode.data
          | throw s!"{rowPath}.salts: byte-key result is not a memory global"
        unless resultImage.bytesHex == imageHex && resultImage.alignBytes == 1 &&
            resultImage.mutability == .immutable && resultImage.relocations.isEmpty &&
            resultImage.initializationRanges.all (·.initialized) do
          throw s!"{rowPath}.salts: byte-key result does not contain the exact queried byte image"
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      if byteRowByImage.contains imageHex then throw s!"{rowPath}: duplicate exact byte-image key"
      byteRowByImage := byteRowByImage.insert imageHex dedup.size
    else if row.keyKind == .function then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed function key carries an unexpected byte image"
      let some (.function keyFunction) := keyNode.data
        | throw s!"{rowPath}: function key witness lacks typed instance data"
      if functionRowByInstance.contains keyFunction.instanceId then
        throw s!"{rowPath}: duplicate exact function Instance key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero function result is not its typed key witness"
      functionRowByInstance := functionRowByInstance.insert keyFunction.instanceId dedup.size
    else if row.keyKind == .vtable then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed vtable key carries an unexpected byte image"
      let some (.vtable keyVtable) := keyNode.data
        | throw s!"{rowPath}: vtable key witness lacks typed identity data"
      let (_,predicates) ← vtableKey input keyNode keyVtable
      let previous := vtableRowsByType[keyVtable.typeId]?.getD #[]
      if previous.contains predicates then
        throw s!"{rowPath}: duplicate exact compiler vtable type/predicate key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero vtable result is not its typed key witness"
      vtableRowsByType := vtableRowsByType.insert keyVtable.typeId (previous.push predicates)
    else if row.keyKind == .static then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed static key carries an unexpected byte image"
      let some (.static keyStatic) := keyNode.data
        | throw s!"{rowPath}: static key witness lacks typed DefId data"
      let defKey := (keyStatic.definitionId.crateIndex, keyStatic.definitionId.index)
      if staticDefinitionsSeen.contains defKey then
        throw s!"{rowPath}: duplicate exact static DefId key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero static result is not its typed key witness"
      staticDefinitionsSeen := staticDefinitionsSeen.insert defKey dedup.size
    else
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed TypeId key carries an unexpected byte image"
      let some (.typeId keyType) := keyNode.data
        | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
      if typeIdRowByType.contains keyType then
        throw s!"{rowPath}: duplicate exact TypeId Ty key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero TypeId result is not its typed key witness"
      typeIdRowByType := typeIdRowByType.insert keyType dedup.size
    dedup := dedup.push row
  for node in nodes do
    if node.status == .supported then
      if let some (.static static) := node.data then
        unless staticDefinitionsSeen.contains (static.definitionId.crateIndex, static.definitionId.index) do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected source static node lacks its exact salt-zero key outcome"
      if let some (.typeId ty) := node.data then
        unless typeIdRowByType.contains ty do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected TypeId node lacks its exact salt-zero key outcome"
  let mut completeFamilies := #[]
  for (kind, index) in world.completeKeyFamilies.toList.zipIdx do
    unless kind == .bytes do
      throw s!"$.compiler_alloc_id_world.complete_key_families[{index}]: this decoder only recognizes the source-validated byte_memory family"
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world.complete_key_families: duplicate key family"
    completeFamilies := completeFamilies.push kind
  unless completeFamilies.size == 1 && completeFamilies[0]? == some .bytes do
    throw "$.compiler_alloc_id_world.complete_key_families: prepared profile requires exactly byte_memory completeness"
  let mut unsupportedFamilies := #[]
  for (kind, index) in world.unsupportedKeyFamilies.toList.zipIdx do
    unless #[.function, .vtable, .static, .typeId, .memory].contains kind do
      throw s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]: unknown or inapplicable unsupported family"
    if unsupportedFamilies.contains kind then throw "$.compiler_alloc_id_world.unsupported_key_families: duplicate family"
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world: key family is both complete and unsupported"
    unsupportedFamilies := unsupportedFamilies.push kind
  for required in #[SourceAllocIdDedupKind.function, .vtable, .static, .typeId, .memory] do
    unless unsupportedFamilies.contains required do
      throw "$.compiler_alloc_id_world.unsupported_key_families: function/vtable/static/type_id/memory_const_allocation must remain explicitly unsupported"
  for row in dedup do
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw "$.compiler_alloc_id_world.dedup_catalog: unsupported selected key outcome family"
  if completeFamilies.contains .bytes then
    for row in pool do
      if row.kind == .memory then
        unless row.memoryMutability.isSome && row.memoryAlignBytes.isSome &&
            row.memoryAllBytesInitialized.isSome && row.memoryHasProvenance.isSome do
          throw "$.compiler_alloc_id_world.raw_pool: byte_memory completeness requires all source memory projection dimensions"
        let eligible := row.memoryMutability == some .immutable && row.memoryAlignBytes == some 1 &&
          row.memoryAllBytesInitialized == some true && row.memoryHasProvenance == some false
        if eligible then
          unless row.status == .serialized do
            throw "$.compiler_alloc_id_world.raw_pool: eligible byte-memory global is not serialized"
          let some imageHex := row.byteImageHex | throw "$.compiler_alloc_id_world.raw_pool: eligible byte key has no exact image"
          let some keyIndex := byteRowByImage[imageHex]? | throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits an eligible image"
          let some key := dedup[keyIndex]? | throw "$.compiler_alloc_id_world.dedup_catalog: key index is absent"
          unless key.salts.size == 32 && (List.range 32).all (fun salt => key.salts.any (·.salt == salt)) do
            throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits a full salt row for an eligible image"
  pure ()

end Miri.Input.AllocIdWorldValidation
