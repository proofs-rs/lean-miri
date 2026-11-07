import Miri.Input.Reader.Table
import Miri.Input.DecoderValues
import Miri.Input.Reader.Generics

namespace Miri.Input.Reader.VtableReader
open Lean Miri.MIR

structure Environment where
  catalog : Catalog
  instances : Array (Except String Miri.Interpreter.CallInstance)
  predicates : Array CompilerPredicateEvidence
  typeCount : Nat
  allocationCount : Nat
structure State where
  tables : VtableTables
  compiler : MIRReader.State
  emptyList : Option Nat := none
abbrev Decode := ReaderT Environment (StateT State (Except String))

private def field (input : Json) (key path : String) : Decode Json := do
  let catalog := (← read).catalog
  catalog.inspect (← catalog.field input key path) path
private def rawField (input : Json) (key path : String) : Decode Json := do
  (← read).catalog.field input key path
private def text (input : Json) (key path : String) : Decode String := do
  (← field input key path).getStr?
private def natural (input : Json) (key path : String) : Decode Nat := do
  (← field input key path).getNat?
private def boolean (input : Json) (key path : String) : Decode Bool := do
  (← field input key path).getBool?
private def optionalNat (input : Json) (key path : String) : Decode (Option Nat) := do
  let catalog := (← read).catalog
  match ← catalog.optionalField input key path with
  | none | some .null => return none
  | some value => some <$> catalog.natural value path
private def status (input : Json) (key path : String) : Decode PayloadStatus := do
  return DecoderValues.parseStatus (← text input key path)
private def typeId (input : Json) (path : String) : Decode Nat := do
  let id ← natural input "type_id" path
  unless id < (← read).typeCount do throw s!"{path}: invalid type ID {id}"
  return id
private def predicateId (input : Json) (path : String) : Decode Nat := do
  let id ← natural input "predicate_id" path
  unless id < (← read).predicates.size do throw s!"{path}: invalid predicate ID {id}"
  return id
private def cached (getTable : State → SharedTable α) (putTable : State → SharedTable α → State)
    (decode : Json → String → Decode α) (input : Json) (path : String) : Decode Nat := fun environment =>
  environment.catalog.readCached getTable putTable (fun input path => decode input path environment) input path

private def list (input : Json) (path : String) : Decode Nat := do
  let catalog := (← read).catalog
  let values ← catalog.array input path
  if values.isEmpty && (← catalog.sharedId? input path).isNone then
    if let some id := (← get).emptyList then return id
  let id ← cached (·.tables.predicateLists) (fun state table =>
      {state with tables := {state.tables with predicateLists := table}}) (fun input path => do
    let values ← (← read).catalog.array input path
    return {values := ← values.mapIdxM (fun index value => predicateId value s!"{path}[{index}]")}) input path
  if values.isEmpty && (← catalog.sharedId? input path).isNone then modify fun state => {state with emptyList := some id}
  return id

private def principal (input : Json) (path : String) : Decode (Option Nat) := do
  let value ← field input "principal_predicate" path
  if value == .null then return none
  let id ← predicateId value path
  let some entry := (← read).predicates[id]? | throw s!"{path}: predicate absent"
  unless entry.status == .supported && entry.kind == .trait do throw s!"{path}: principal is not a supported trait"
  return some id

private def recordPrincipal (id : Nat) (principal : Option Nat) (path : String) : Decode Unit := do
  let state ← get
  let value ← state.tables.predicateLists.lookup id |>.mapError (fun id => s!"{path}: invalid predicate list {id}")
  if let some previous := value.principal then
    unless previous == principal do throw s!"{path}: conflicting principal for predicate list"
  if bound : id < state.tables.predicateLists.size then
    let table := state.tables.predicateLists.set id (some {value with principal := some principal}) bound
    set {state with tables := {state.tables with predicateLists := table}}
  else throw s!"{path}: predicate list absent"

private def entry (input : Json) (path : String) : Decode VtableEntryData := do
  let environment ← read
  let kind := DecoderValues.vtableEntryKind (← text input "kind" path)
  let status ← status input "status" path
  let instanceId ← optionalNat input "instance_id" path
  let allocationId ← match ← environment.catalog.optionalField input "allocation" path with
    | none | some .null => pure none
    | some value =>
      let id ← environment.catalog.natural (← environment.catalog.field value "allocation_id" path) path
      unless id < environment.allocationCount do throw s!"{path}: invalid vtable allocation {id}"
      pure (some id)
  if kind == .method && status == .supported then
    let some id := instanceId | throw s!"{path}: vtable method instance absent"
    let some result := environment.instances[id]? | throw s!"{path}: invalid vtable instance {id}"
    let callee ← result
    let definitionInput ← rawField input "def_id" path
    let argumentsInput ← rawField input "generic_args" path
    let state ← get
    let decode : MIRReader.Decode Unit := do
      let definition ← RegionReader.definition environment.catalog definitionInput path
      let argsId ← GenericReader.arguments environment.catalog environment.typeCount argumentsInput path
      let compiler ← get
      let args ← compiler.arguments.lookup argsId |>.mapError (fun id => s!"{path}: invalid generic arguments {id}")
      unless definition == callee.defId && args == callee.args do
        throw s!"{path}: vtable method/full-instance mismatch"
    let (_,compiler) ← decode.run state.compiler
    set {state with compiler}
  return {kind,status,instanceId,allocationId}

private def entryList (input : Json) (path : String) : Decode Nat :=
  cached (·.tables.entryLists) (fun state table => {state with tables := {state.tables with entryLists := table}})
    (fun input path => do
      let values ← (← read).catalog.array input path
      values.mapIdxM fun index value => entry value s!"{path}[{index}]") input path

private def metadata (input : Json) (path : String) : Decode Nat :=
  cached (·.tables.metadata) (fun state table => {state with tables := {state.tables with metadata := table}})
    (fun input path => do
      let predicates ← list (← rawField input "predicates" path) path
      let principal ← principal input path
      recordPrincipal predicates principal path
      return {
        status := ← status input "status" path
        typeId := ← typeId (← rawField input "type" path) path
        predicates, principal
        layoutStatus := ← status input "layout_status" path
        sizeBytes := ← optionalNat input "size_bytes" path
        alignBytes := ← optionalNat input "align_bytes" path
        entries := ← entryList (← rawField input "entries" path) path }) input path

private def query (input : Json) (path : String) : Decode VtableQueryData := do
  unless (← status input "status" path) == .supported do throw s!"{path}: vtable erasure query unavailable"
  let inputTypeId ← typeId (← rawField input "input_type" path) path
  let inputPredicates ← list (← rawField input "input_predicates" path) path
  let catalog := (← read).catalog
  let metadata ← match ← catalog.optionalField input "vtable_metadata" path with
    | none | some .null => pure none
    | some value => some <$> metadata value s!"{path}.vtable_metadata"
  if let some id := metadata then
    let value ← (← get).tables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
    unless value.typeId == inputTypeId && value.predicates == inputPredicates do
      throw s!"{path}: vtable metadata does not match its query key"
  let allocationId ← optionalNat input "vtable_allocation_id" path
  if let some id := allocationId then
    unless id < (← read).allocationCount do throw s!"{path}: invalid allocation ID {id}"
  return {
    inputTypeId, inputPredicates, metadata, allocationId
    outputTypeId := ← typeId (← rawField input "output_type" path) path
    outputPredicates := ← list (← rawField input "output_predicates" path) path
    typeMonomorphic := ← boolean input "output_type_monomorphic_enough" path
    predicatesMonomorphic := ← boolean input "output_predicates_monomorphic_enough" path
    queryId := ← optionalNat input "query_id" path }

private def parse (types : Array TypeNode) (allocations : Array AllocationNode) :
    Decode (Array TypeNode) := do
  let catalog := (← read).catalog
  let rawTypes ← catalog.array (← catalog.field catalog.root "types" "$") "types"
  unless rawTypes.size == types.size do throw "type table mismatch"
  let mut result := #[]
  for (raw,index) in rawTypes.toList.zipIdx do
    let some source := types[index]? | throw "type row absent"
    if source.shapeKind == .dynamicTraitObject then
      let shape ← rawField raw "shape" "type"
      let predicates ← list (← rawField shape "predicates" "type") "type.predicates"
      recordPrincipal predicates (← principal shape "type") "type"
      result := result.push {source with relations := {source.relations with predicates := some predicates}}
    else result := result.push source
  let rawAllocations ← catalog.array (← catalog.field catalog.root "allocations" "$") "allocations"
  unless rawAllocations.size == allocations.size do throw "allocation table mismatch"
  for (raw,index) in rawAllocations.toList.zipIdx do
    let some source := allocations[index]? | throw "allocation row absent"
    match source.data with
    | some (.vtable _) =>
      let id ← metadata raw s!"allocations[{index}]"
      let state ← get
      if bound : source.id < state.tables.allocationMetadata.size then
        let allocationMetadata := state.tables.allocationMetadata.set source.id (some id) bound
        set {state with tables := {state.tables with allocationMetadata}}
      else throw "vtable source allocation ID outside table"
    | _ => pure ()
  let rawQueries ← catalog.array (← catalog.field catalog.root "compiler_vtable_queries" "$") "compiler_vtable_queries"
  let mut queries := #[]
  for (raw,index) in rawQueries.toList.zipIdx do
    let value ← try pure (.ok (← query raw s!"compiler_vtable_queries[{index}]")) catch reason => pure (.error reason)
    queries := queries.push value
  modify fun state => {state with tables := {state.tables with queries}}
  return result

end Miri.Input.Reader.VtableReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readVtables (catalog : Catalog) (mir : MIRInputTables)
    (predicates : Array CompilerPredicateEvidence) (types : Array TypeNode) (allocations : Array AllocationNode) :
    Except String (Array TypeNode × VtableTables) := do
  let environment : VtableReader.Environment := {catalog,instances := mir.instances,predicates,typeCount := types.size,allocationCount := allocations.size}
  let empty := fun {α : Type} => (Array.replicate catalog.nodes.size none : SharedTable α)
  let initial : VtableReader.State := {compiler := MIRReader.initial catalog.nodes.size mir.compiler, tables := {allocationMetadata := Array.replicate allocations.size none, predicateLists := empty,entryLists := empty,metadata := empty}}
  let (types,state) ← (VtableReader.parse types allocations environment).run initial
  unless state.compiler.compiler = mir.compiler do throw "vtable methods require unprepared compiler identities"
  return (types,state.tables)

end Miri.Input.Reader
