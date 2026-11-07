import Miri.Input.DecoderValues

namespace Miri.Input.ReferenceValidation
open Lean DecoderValues

/-- Source order need not coincide with dense ID order. -/
structure TableRef (ids : Array Nat) where
  sourceId : Nat
  position : Fin ids.size
  identifies : ids[position] = sourceId
  bounded : sourceId < ids.size

structure IdIndex (ids : Array Nat) where
  private positions : Std.HashMap Nat (Fin ids.size)
  bounds : ∀ position : Fin ids.size, ids[position] < ids.size

def IdIndex.build (ids : Array Nat) (bounds : ∀ position : Fin ids.size, ids[position] < ids.size) : IdIndex ids := Id.run do
  let mut positions := {}
  for h : index in [:ids.size] do
    have bound := Membership.mem.upper h
    positions := positions.insert ids[index] ⟨index, bound⟩
  return ⟨positions, bounds⟩

def IdIndex.reference? (index : IdIndex ids) (id : Nat) : Option (TableRef ids) := do
  let position ← index.positions[id]?
  if identifies : ids[position] = id then
    return ⟨id, position, identifies, by simpa [identifies] using index.bounds position⟩
  else none

theorem TableRef.exists_in_source (reference : TableRef ids) : reference.sourceId ∈ ids := by
  rw [← reference.identifies]
  exact Array.getElem_mem reference.position.isLt

structure Tables where
  types : Array Nat
  allocations : Array Nat
  instances : Array Nat

inductive GlobalRef (tables : Tables) where
  | type (reference : TableRef tables.types)
  | allocation (reference : TableRef tables.allocations)
  | instance (reference : TableRef tables.instances)

structure GlobalOccurrence (tables : Tables) where
  path : String
  reference : GlobalRef tables

structure BodyReferences where
  source : Json
  path : String
  localRows : Array Json
  blockRows : Array Json
  localsSource : arrayField source "locals" path = .ok localRows
  blocksSource : arrayField source "basic_blocks" path = .ok blockRows
  locals : Array (String × Fin localRows.size)
  blocks : Array (String × Fin blockRows.size)

structure Summary where
  tables : Tables
  global : Array (GlobalOccurrence tables)
  bodies : Array BodyReferences
  typeIndex : IdIndex tables.types
  allocationIndex : IdIndex tables.allocations
  instanceIndex : IdIndex tables.instances

def Tables.shape (tables : Tables) : ProgramShape :=
  ⟨tables.types.size, tables.allocations.size, tables.instances.size⟩

def BodyReferences.shape (body : BodyReferences) : BodyShape :=
  ⟨body.localRows.size, body.blockRows.size⟩

structure BodyIndex (body : BodyReferences) where
  locals : Std.HashMap Nat (Fin body.localRows.size)
  blocks : Std.HashMap Nat (Fin body.blockRows.size)

@[noinline] def BodyReferences.index (body : BodyReferences) : BodyIndex body :=
  ⟨body.locals.foldl (fun table item => table.insert item.2.val item.2) {},
    body.blocks.foldl (fun table item => table.insert item.2.val item.2) {}⟩

def Summary.resolver (summary : Summary) (body : BodyReferences) (index : BodyIndex body) :
    ReferenceContext.Resolver (.checked summary.tables.shape body.shape) :=
  fun kind id =>
  match kind with
  | .type => do
    let some reference := summary.typeIndex.reference? id | throw s!"missing validated type {id}"
    return ⟨reference.sourceId, reference.bounded⟩
  | .allocation => do
    let some reference := summary.allocationIndex.reference? id | throw s!"missing validated allocation {id}"
    return ⟨reference.sourceId, reference.bounded⟩
  | .instance => do
    let some reference := summary.instanceIndex.reference? id | throw s!"missing validated instance {id}"
    return ⟨reference.sourceId, reference.bounded⟩
  | .local => do
    let some reference := index.locals[id]?
      | throw s!"missing validated local {id}"
    return reference
  | .block => do
    let some reference := index.blocks[id]?
      | throw s!"missing validated block {id}"
    return reference

private structure Indices (tables : Tables) where
  types : IdIndex tables.types
  allocations : IdIndex tables.allocations
  instances : IdIndex tables.instances

private structure GlobalState (tables : Tables) where
  visited : Std.HashSet JsonTraversalCache.IdentityKey := {}
  references : Array (GlobalOccurrence tables) := #[]

private def validateDense (ids : Array Nat) (what : String) : Except String (IdIndex ids) := do
  let mut seen : Std.HashSet Nat := {}
  for id in ids do
    if seen.contains id then throw s!"{what}: duplicate IDs"
    seen := seen.insert id
  if bounds : ∀ position : Fin ids.size, ids[position] < ids.size then
    return IdIndex.build ids bounds
  else
    let some id := ids.find? (fun id => id >= ids.size)
      | throw s!"{what}: IDs must be dense from zero"
    throw s!"{what}: IDs must be dense from zero; found {id} with {ids.size} entries"

private partial def validateReferencesAux (node : JsonTraversalCache.Node) (path : String)
    (indices : Indices tables) (state : GlobalState tables) : Except String (GlobalState tables) := do
  let j := node.value
  let memoKey := node.identity
  if statusOf? j == some "debug_payload" then return state
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && node.shouldMemo && state.visited.contains memoKey then return state
  let mut state := state
  match j with
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      state ← validateReferencesAux (node.child index value) s!"{path}[{index}]" indices state
  | .obj fields =>
    let entries := fields.toList
    match entries with
    | [("type_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.type_id: malformed type reference ({e})"
      let some reference := indices.types.reference? id
        | throw s!"{path}: dangling type reference {id}"
      state := { state with references := state.references.push ⟨path, .type reference⟩ }
      return if node.shouldMemo then { state with visited := state.visited.insert memoKey } else state
    | [("allocation_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.allocation_id: malformed allocation reference ({e})"
      let some reference := indices.allocations.reference? id
        | throw s!"{path}: dangling allocation reference {id}"
      state := { state with references := state.references.push ⟨path, .allocation reference⟩ }
      return if node.shouldMemo then { state with visited := state.visited.insert memoKey } else state
    | _ => pure ()
    for ((key, value), childIndex) in entries.zipIdx do
      if key == "instance_id" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: malformed instance ID ({e})"
        let some reference := indices.instances.reference? id
          | throw s!"{joinPath path key}: dangling instance reference {id}"
        state := { state with references := state.references.push ⟨joinPath path key, .instance reference⟩ }
      state ← validateReferencesAux (node.child childIndex value) (joinPath path key) indices state
  | _ => pure ()
  return if isContainer && node.shouldMemo then { state with visited := state.visited.insert memoKey } else state

private abbrev BodyCheck (locals blocks : Nat) :=
  StateT (Array (String × Fin locals) × Array (String × Fin blocks)) (Except String)

private partial def validateMirIndices (j : Json) (path : String)
    (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    let mut index := 0
    for value in values do
      validateMirIndices value s!"{path}[{index}]" localCount blockCount
      index := index + 1
  | .obj fields =>
    for (key, value) in fields.toList do
      if key == "local" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: expected local index ({e})"
        if bound : id < localCount then
          modify fun state => (state.1.push (joinPath path key, ⟨id, bound⟩), state.2)
        else throw s!"{joinPath path key}: local {id} is out of range (locals={localCount})"
      if ["block", "target", "otherwise", "real_target", "imaginary_target", "resume"].contains key then
        if let .ok id := value.getNat? then
          if bound : id < blockCount then
            modify fun state => (state.1, state.2.push (joinPath path key, ⟨id, bound⟩))
          else throw s!"{joinPath path key}: basic block {id} is out of range (blocks={blockCount})"
      if key == "projection" then
        let projections ← value.getArr? |>.mapError fun e => s!"{joinPath path key}: expected projection array ({e})"
        for (projection, index) in projections.toList.zipIdx do
          let pPath := s!"{joinPath path key}[{index}]"
          let kind ← fieldString projection "kind" pPath
          if kind == "Index" then
            let id ← fieldNat projection "local" pPath
            if bound : id < localCount then
              modify fun state => (state.1.push (pPath ++ ".local", ⟨id, bound⟩), state.2)
            else throw s!"{pPath}.local: local {id} is out of range (locals={localCount})"
          if kind == "ConstantIndex" then
            let _ ← fieldNat projection "offset" pPath
            let _ ← fieldNat projection "min_length" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Subslice" then
            let _ ← fieldNat projection "from" pPath
            let _ ← fieldNat projection "to" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Field" then
            let _ ← fieldNat projection "index" pPath
            let _ ← field projection "field_type" pPath
          if kind == "Downcast" then
            let _ ← fieldNat projection "variant_index" pPath
          if kind == "OpaqueCast" then let _ ← field projection "cast_type" pPath
          if kind == "UnwrapUnsafeBinder" then let _ ← field projection "inner_type" pPath
          if isKnownProjection kind then let _ ← field projection "resulting_type" pPath
      validateMirIndices value (joinPath path key) localCount blockCount
  | _ => pure ()

private def checkBlockIndex (value : Json) (path : String) (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  let id ← value.getNat? |>.mapError fun e => s!"{path}: expected basic-block index ({e})"
  if (← get).2.any (fun item => item.1 == path && item.2.val == id) then return
  if bound : id < blockCount then
    modify fun state => (state.1, state.2.push (path, ⟨id, bound⟩))
  else throw s!"{path}: basic block {id} is out of range (blocks={blockCount})"

private def checkRequiredEdge (j : Json) (key path : String) (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  checkBlockIndex (← field j key path) (joinPath path key) localCount blockCount

private def checkOptionalEdge (j : Json) (key path : String) (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  match optionalField j key with
  | none => throw s!"{path}: missing optional edge field `{key}`"
  | some .null => pure ()
  | some value => checkBlockIndex value (joinPath path key) localCount blockCount

private def validateUnwind (j : Json) (path : String) (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  let kind ← fieldString j "kind" path
  if kind == "Cleanup" then checkRequiredEdge j "target" path localCount blockCount

private def validateTerminatorEdges (j : Json) (path : String) (localCount blockCount : Nat) : BodyCheck localCount blockCount Unit := do
  let variant ← fieldString j "variant" path
  match variant with
  | "Goto" => checkRequiredEdge j "target" path localCount blockCount
  | "SwitchInt" =>
    checkRequiredEdge j "otherwise" path localCount blockCount
    let targets ← arrayField j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkRequiredEdge target "target" s!"{joinPath path "targets"}[{index}]" localCount blockCount
  | "Drop" =>
    checkRequiredEdge j "target" path localCount blockCount
    checkOptionalEdge j "async_drop" path localCount blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") localCount blockCount
  | "Call" =>
    checkOptionalEdge j "target" path localCount blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") localCount blockCount
  | "Assert" =>
    checkRequiredEdge j "target" path localCount blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") localCount blockCount
  | "Yield" =>
    checkRequiredEdge j "resume" path localCount blockCount
    checkOptionalEdge j "drop" path localCount blockCount
  | "InlineAsm" =>
    let targets ← arrayField j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkBlockIndex target s!"{joinPath path "targets"}[{index}]" localCount blockCount
  | "FalseEdge" =>
    checkRequiredEdge j "real_target" path localCount blockCount
    checkRequiredEdge j "imaginary_target" path localCount blockCount
  | "FalseUnwind" =>
    checkRequiredEdge j "real_target" path localCount blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") localCount blockCount
  | _ => pure ()

private def validateBody (j : Json) (path : String) : Except String BodyReferences := do
  match localsSource : arrayField j "locals" path with
  | .error error => throw error
  | .ok locals =>
    match blocksSource : arrayField j "basic_blocks" path with
    | .error error => throw error
    | .ok blocks => do
      let (_, references) ← (do
        if locals.isEmpty then throw s!"{joinPath path "locals"}: MIR body must declare the return local"
        if blocks.isEmpty then throw s!"{joinPath path "basic_blocks"}: MIR body must contain a start block"
        let mut index := 0
        for localDecl in locals do
          let id ← fieldNat localDecl "local" s!"{joinPath path "locals"}[{index}]"
          if id != index then throw s!"{joinPath path "locals"}[{index}]: local declarations must be densely ordered"
          index := index + 1
        if let some spread ← optionalNat j "spread_arg" path then
          if bound : spread < locals.size then
            modify fun state => (state.1.push (joinPath path "spread_arg", ⟨spread, bound⟩), state.2)
          else throw s!"{joinPath path "spread_arg"}: local {spread} is out of range (locals={locals.size})"
        index := 0
        for block in blocks do
          let blockPath := s!"{joinPath path "basic_blocks"}[{index}]"
          let id ← fieldNat block "block" blockPath
          if id != index then throw s!"{blockPath}: basic blocks must be densely ordered"
          let statements ← arrayField block "statements" blockPath
          for (statement, stmtIndex) in statements.toList.zipIdx do
            let kind ← field statement "kind" s!"{blockPath}.statements[{stmtIndex}]"
            validateMirIndices kind s!"{blockPath}.statements[{stmtIndex}].kind" locals.size blocks.size
          let termWrapper ← field block "terminator" blockPath
          if termWrapper == .null then throw s!"{blockPath}: missing terminator"
          let term ← field termWrapper "kind" s!"{blockPath}.terminator"
          validateMirIndices term s!"{blockPath}.terminator.kind" locals.size blocks.size
          validateTerminatorEdges term s!"{blockPath}.terminator.kind" locals.size blocks.size
          index := index + 1
        : BodyCheck locals.size blocks.size Unit).run (#[], #[])
      return ⟨j, path, locals, blocks, localsSource, blocksSource, references.1, references.2⟩

private partial def validateAllBodiesAux (node : JsonTraversalCache.Node) (path : String)
    (state : Std.HashSet JsonTraversalCache.IdentityKey × Array BodyReferences) :
    Except String (Std.HashSet JsonTraversalCache.IdentityKey × Array BodyReferences) := do
  let j := node.value
  let memoKey := node.identity
  if statusOf? j == some "debug_payload" then return state
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && node.shouldMemo && state.1.contains memoKey then return state
  let mut state := state
  match j with
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      state ← validateAllBodiesAux (node.child index value) s!"{path}[{index}]" state
  | .obj fields =>
    let hasLocals := (j.getObjVal? "locals").isOk
    let hasBlocks := (j.getObjVal? "basic_blocks").isOk
    if hasLocals != hasBlocks then throw s!"{path}: body requires both locals and basic_blocks"
    if hasLocals && hasBlocks then state := (state.1, state.2.push (← validateBody j path))
    for ((key, value), childIndex) in fields.toList.zipIdx do
      state ← validateAllBodiesAux (node.child childIndex value) (joinPath path key) state
  | _ => pure ()
  return if isContainer && node.shouldMemo then (state.1.insert memoKey, state.2) else state

private def tableIds (input : Json) (table key : String) : Except String (Array Nat) := do
  let rows ← arrayField input table "$"
  rows.toList.zipIdx.toArray.mapM fun (row, index) => fieldNat row key s!"$.{table}[{index}]"

private def run (node : JsonTraversalCache.Node) : Except String Summary := do
  let tables : Tables := ⟨← tableIds node.value "types" "type_id",
    ← tableIds node.value "allocations" "allocation_id", ← tableIds node.value "instances" "instance_id"⟩
  let typeIndex ← validateDense tables.types "type IDs"
  let allocationIndex ← validateDense tables.allocations "allocation IDs"
  let instanceIndex ← validateDense tables.instances "instance IDs"
  let (_, bodies) ← validateAllBodiesAux node "$" ({}, #[])
  let indices : Indices tables := ⟨typeIndex, allocationIndex, instanceIndex⟩
  let globals ← validateReferencesAux node "$" indices {}
  return ⟨tables, globals.references, bodies, typeIndex, allocationIndex, instanceIndex⟩

structure Checked (node : JsonTraversalCache.Node) where
  private mk ::
  summary : Summary
  exact : run node = .ok summary

def Checked.source (_checked : Checked node) : Json := node.value

/-- The existential witness avoids retaining the traversal cache at runtime. -/
structure ForSource (source : Json) where
  summary : Summary
  exact : ∃ node, node.value = source ∧ run node = .ok summary

def Checked.forSource (checked : Checked node) (source : Json) (same : node.value = source) :
    ForSource source :=
  ⟨checked.summary, ⟨node, same, checked.exact⟩⟩

def validateUsing (node : JsonTraversalCache.Node) : Except String (Checked node) :=
  match checked : run node with
  | .error error => .error error
  | .ok summary => .ok ⟨summary, checked⟩

def validate (source : Json) : Except String (ForSource source) := do
  let checked ← validateUsing (.uncached source)
  return checked.forSource source rfl

end Miri.Input.ReferenceValidation
