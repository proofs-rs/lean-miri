import Miri.Input.Model.Types

namespace Miri.Input

def validateCompilerAllocIdWorld (nodes : Array AllocationNode)
    (world : CompilerAllocIdWorld) : Except String Unit := do
  let lastNat := world.lastReservedSourceAllocId.toNat
  let nextNat := world.nextSourceAllocId.toNat
  unless lastNat > 0 && world.finalSentinelSourceAllocId == world.lastReservedSourceAllocId &&
      nextNat == lastNat + 1 do
    throw "$.compiler_alloc_id_world.frontier: sentinel, last reservation, and next counter disagree"
  unless world.rawPool.size == lastNat do
    throw "$.compiler_alloc_id_world.raw_pool: must contain exactly the raw ID prefix 1..=frontier"
  let mut nodeIndexByGraphId : Std.HashMap Nat Nat := {}
  let mut nodeIndexBySourceId : Std.HashMap Nat Nat := {}
  for (node, index) in nodes.toList.zipIdx do
    if nodeIndexByGraphId.contains node.id then throw "$.compiler_alloc_id_world: duplicate allocation graph identity"
    nodeIndexByGraphId := nodeIndexByGraphId.insert node.id index
    if let some sourceId := node.sourceAllocId then
      if nodeIndexBySourceId.contains sourceId.toNat then
        throw "$.compiler_alloc_id_world: duplicate source AllocId witness on allocation nodes"
      nodeIndexBySourceId := nodeIndexBySourceId.insert sourceId.toNat index
  let pool := world.rawPool
  for (row, index) in pool.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.raw_pool[{index}]"
    unless row.sourceAllocId.toNat == index + 1 do
      throw s!"{rowPath}.source_alloc_id: pool rows must be ordered and contiguous from one"
    if row.status == .serialized then
      let some graphId := row.allocationId | throw s!"{rowPath}: serialized pool row lacks graph identity"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId do throw s!"{rowPath}: source AllocId disagrees with allocation node witness"
      let expectedKind ← match row.kind with
        | .memory => pure AllocationKind.memory
        | .function => pure AllocationKind.function
        | .vtable => pure AllocationKind.vtable
        | .static => pure AllocationKind.static
        | .typeId => pure AllocationKind.typeId
        | .dangling => throw s!"{rowPath}: dangling source global cannot be serialized"
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
    else if nodeIndexBySourceId.contains row.sourceAllocId.toNat then
      throw s!"{rowPath}: non-serialized source ID is attached to an allocation node"
  let some sentinel := pool[pool.size - 1]? | throw "$.compiler_alloc_id_world.raw_pool: sentinel row absent"
  unless sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone do
    throw "$.compiler_alloc_id_world.raw_pool: final reserved sentinel must be dangling"
  for node in nodes do
    let some sourceId := node.sourceAllocId | throw "$.compiler_alloc_id_world: every imported allocation must carry an exact source_alloc_id witness"
    let some row := pool[sourceId.toNat - 1]? | throw "$.compiler_alloc_id_world: allocation witness lies outside captured raw prefix"
    unless row.status == .serialized && row.allocationId == some node.id do
      throw "$.compiler_alloc_id_world: allocation node is not covered by exactly one serialized pool row"
  let dedup := world.dedupCatalog
  let mut byteRowByImage : Std.HashMap String Nat := {}
  let mut functionRowByInstance : Std.HashMap InstanceId Nat := {}
  let mut vtableRowsByType : Std.HashMap TypeId (Array (Array Nat)) := {}
  let mut staticDefinitionsSeen : Std.HashMap Nat Nat := {}
  let mut typeIdRowByType : Std.HashMap TypeId Nat := {}
  for (row, index) in dedup.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.dedup_catalog[{index}]"
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw s!"{rowPath}.key_kind: dedup key family is not available in this prepared profile"
    let some keyIndex := nodeIndexByGraphId[row.keyAllocationId]? | throw s!"{rowPath}.key_allocation_id: selected key node is not serialized"
    let some keyNode := nodes[keyIndex]? | throw s!"{rowPath}.key_allocation_id: selected key index is absent"
    let expectedKeyKind ← match row.keyKind with
      | .bytes => pure AllocationKind.memory
      | .function => pure AllocationKind.function
      | .vtable => pure AllocationKind.vtable
      | .static => pure AllocationKind.static
      | .typeId => pure AllocationKind.typeId
      | _ => throw s!"{rowPath}: unavailable dedup key family"
    unless keyNode.kind == expectedKeyKind do
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
      unless resultNode.kind == expectedKeyKind do
        throw s!"{rowPath}.salts[{saltIndex}]: result allocation has incompatible kind/status"
      if row.keyKind == .function then
        let some (.function keyFunction) := keyNode.data
          | throw s!"{rowPath}: function key witness lacks typed instance data"
        let some (.function resultFunction) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: function result lacks typed instance data"
        unless keyFunction.instanceId == resultFunction.instanceId do
          throw s!"{rowPath}.salts[{saltIndex}]: function result does not match the exact selected Instance key"
      if row.keyKind == .vtable then
        let some (.vtable keyVtable) := keyNode.data
          | throw s!"{rowPath}: vtable key witness lacks typed identity data"
        let some (.vtable resultVtable) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: vtable result lacks typed identity data"
        unless keyVtable.typeId == resultVtable.typeId && keyVtable.predicates == resultVtable.predicates do
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
      byteRowByImage := byteRowByImage.insert imageHex index
    else if row.keyKind == .function then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed function key carries an unexpected byte image"
      let some (.function keyFunction) := keyNode.data
        | throw s!"{rowPath}: function key witness lacks typed instance data"
      if functionRowByInstance.contains keyFunction.instanceId then
        throw s!"{rowPath}: duplicate exact function Instance key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero function result is not its typed key witness"
      functionRowByInstance := functionRowByInstance.insert keyFunction.instanceId index
    else if row.keyKind == .vtable then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed vtable key carries an unexpected byte image"
      let some (.vtable keyVtable) := keyNode.data
        | throw s!"{rowPath}: vtable key witness lacks typed identity data"
      let previous := vtableRowsByType[keyVtable.typeId]?.getD #[]
      if previous.contains keyVtable.predicates then
        throw s!"{rowPath}: duplicate exact compiler vtable type/predicate key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero vtable result is not its typed key witness"
      vtableRowsByType := vtableRowsByType.insert keyVtable.typeId (previous.push keyVtable.predicates)
    else if row.keyKind == .static then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed static key carries an unexpected byte image"
      let some (.static keyStatic) := keyNode.data
        | throw s!"{rowPath}: static key witness lacks typed DefId data"
      let defKey := keyStatic.definitionId
      if staticDefinitionsSeen.contains defKey then
        throw s!"{rowPath}: duplicate exact static DefId key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero static result is not its typed key witness"
      staticDefinitionsSeen := staticDefinitionsSeen.insert defKey index
    else
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed TypeId key carries an unexpected byte image"
      let some (.typeId keyType) := keyNode.data
        | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
      if typeIdRowByType.contains keyType then
        throw s!"{rowPath}: duplicate exact TypeId Ty key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero TypeId result is not its typed key witness"
      typeIdRowByType := typeIdRowByType.insert keyType index
  for node in nodes do
    if let some (.function fn) := node.data then
      unless functionRowByInstance.contains fn.instanceId do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected function node lacks its exact full-salt key outcomes"
    if let some (.vtable vtable) := node.data then
      unless (vtableRowsByType[vtable.typeId]?.getD #[]).contains vtable.predicates do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected vtable node lacks its exact full-salt key outcomes"
    if let some (.static static) := node.data then
      unless staticDefinitionsSeen.contains static.definitionId do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected source static node lacks its exact salt-zero key outcome"
    if let some (.typeId ty) := node.data then
      unless typeIdRowByType.contains ty do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected TypeId node lacks its exact salt-zero key outcome"
  let completeFamilies := world.completeKeyFamilies
  let nonExhaustiveFamilies := world.nonExhaustiveKeyFamilies
  unless completeFamilies == #[.bytes] do
    throw "$.compiler_alloc_id_world.complete_key_families: prepared profile requires exactly byte_memory completeness"
  let mut seenFamilies : Array SourceAllocIdDedupKind := #[]
  for kind in nonExhaustiveFamilies do
    unless #[.function, .vtable, .static, .typeId, .memory].contains kind do
      throw "$.compiler_alloc_id_world.non_exhaustive_key_families: unknown or inapplicable non-exhaustive family"
    if seenFamilies.contains kind then throw "$.compiler_alloc_id_world.non_exhaustive_key_families: duplicate family"
    seenFamilies := seenFamilies.push kind
  for required in #[SourceAllocIdDedupKind.function, .vtable, .static, .typeId, .memory] do
    unless nonExhaustiveFamilies.contains required do
      throw "$.compiler_alloc_id_world.non_exhaustive_key_families: function/vtable/static/type_id/memory_const_allocation must remain explicitly non-exhaustive"
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
          unless byteRowByImage.contains imageHex do
            throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits an eligible image"

end Miri.Input
