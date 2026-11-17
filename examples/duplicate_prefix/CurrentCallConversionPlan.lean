import duplicate_prefix.DuplicatePrefixSliceArgument
import duplicate_prefix.GlobalAddressLiveErrorExclusion

/-! The selected conversion order is computed from INITIAL current data.
Live allocations have priority over old compiler descriptors. Current memory
and internal-static payloads are selected in source-then-return order; a source
materialization of the return allocation suppresses a second conversion.
Queries remain separately observable, including errors. Extracting a list is
not a proof that either query, materialization, or call succeeds. -/
namespace DuplicatePrefix.CurrentCallConversionPlan
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter
open Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

abbrev Before := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

/-- The exact primitive allocation query, with the fixed target's 8-byte
pointer arithmetic. No reference ownership or operation outcome is supplied. -/
def query (before : Before) (pointer : Pointer Provenance) (length : UInt64) :
    Except AddressStateError (Option AllocId) :=
  (before.user.addresses.ptrGetAlloc pointer length.toInt64
    (GlobalAddressLiveErrorExclusion.lookup before.memory) ⟨Size.ofBytes 8⟩).map
      (fun selected=>selected.map Prod.fst)

def sourceQuery (before : Before) (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) :
    Except AddressStateError (Option AllocId) :=
  match argument with
  | .integer _=>.ok none
  | .pointer pointer=>query before pointer length

def returnQuery (before : Before) (place : MPlaceTy Provenance) :
    Except AddressStateError (Option AllocId) :=
  match place.mplace.ptr.provenance with
  | none=>.ok none
  | some provenance=>query before {provenance:=provenance,offset:=place.mplace.ptr.offset} 1

/-- Only an absent data allocation invokes the selected CTFE converter. The
initializer is the fixed provider's ACTUAL row, not an assumed evaluation. -/
def payload (before : Before) (id : AllocId) : Option (Allocation CtfeProvenance Unit) :=
  if (before.memory.live.find? (fun row=>row.1==id)).isSome then none
  else if before.memory.hasFunctionPointer id || before.memory.hasVaListId id then none
  else do
    let descriptor←before.memory.findGlobal? id
    match descriptor.kind,descriptor.payload with
    | .memory,some (.memory source)=>some source
    | .static,some (.static definition true false false)=>
        (PreparedReflection.actual.image.initializers.find? (fun row=>row.1==definition)).map Prod.snd
    | _,_=>none

/-- IDs are retained alongside payloads so equality suppresses exactly the
second allocation conversion, rather than deduplicating relocation requests. -/
def rowsFromIds (before : Before) (sourceId returnId : Option AllocId) :
    List (AllocId × Allocation CtfeProvenance Unit) :=
  let source:=sourceId.bind fun id=>(payload before id).map fun value=>(id,value)
  let ret:=returnId.bind fun id=>
    if source.any (fun row=>row.1==id) then none else (payload before id).map fun value=>(id,value)
  source.toList ++ ret.toList

/-- Error branches remain visible through sourceQuery/returnQuery; the domain's
independent selected-pointer representation must establish their real results.
No converter requests are invented for query misses or integer sources. -/
def selectedRows (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (length : UInt64) (place : MPlaceTy Provenance) : List (AllocId × Allocation CtfeProvenance Unit) :=
  rowsFromIds before ((sourceQuery before argument length).toOption.bind id)
    ((returnQuery before place).toOption.bind id)

def selectedPayloads (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (length : UInt64) (place : MPlaceTy Provenance) : List (Allocation CtfeProvenance Unit) :=
  (selectedRows before argument length place).map Prod.snd

/-- Duplicate relocation occurrences remain in their exact array iteration
order. This is deliberately not the conservative conversionTargets budget. -/
def selectedIds (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (length : UInt64) (place : MPlaceTy Provenance) : List AllocId :=
  (selectedPayloads before argument length place).flatMap fun source=>
    source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId)

theorem payload_live (before : Before) (id : AllocId)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : payload before id=none := by
  simp only [payload,present,Option.isSome_some,↓reduceIte]

theorem payload_memory (before : Before) (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (descriptor : before.memory.findGlobal? id=some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    payload before id=some source := by
  simp only [payload,absent,Option.isSome_none,noFunction,noVaList,Bool.false_or,
    Bool.false_eq_true,↓reduceIte,descriptor,bind,Option.bind_some]

theorem payload_static (before : Before) (id : AllocId) (definition : Nat)
    (source : Allocation CtfeProvenance Unit)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (descriptor : before.memory.findGlobal? id=some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initializer : PreparedReflection.actual.image.initializers.find? (fun row=>row.1==definition)=some (definition,source)) :
    payload before id=some source := by
  simp only [payload,absent,Option.isSome_none,noFunction,noVaList,Bool.false_or,
    Bool.false_eq_true,↓reduceIte,descriptor,bind,Option.bind_some,initializer,Option.map_some]

theorem same_id_once (before : Before) (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : payload before id=some source) :
    rowsFromIds before (some id) (some id)=[(id,source)] := by
  simp [rowsFromIds,selected]

theorem distinct_ids (before : Before) (sourceId returnId : AllocId)
    (source ret : Allocation CtfeProvenance Unit) (different : sourceId≠returnId)
    (sourcePayload : payload before sourceId=some source) (returnPayload : payload before returnId=some ret) :
    rowsFromIds before (some sourceId) (some returnId)=[(sourceId,source),(returnId,ret)] := by
  simp [rowsFromIds,sourcePayload,returnPayload,different]

theorem no_source (before : Before) (returnId : Option AllocId) :
    rowsFromIds before none returnId=
      (returnId.bind fun id=>(payload before id).map fun source=>(id,source)).toList := by
  simp [rowsFromIds]

theorem selected_of_queries (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (length : UInt64) (place : MPlaceTy Provenance) (sourceId returnId : Option AllocId)
    (source : sourceQuery before argument length=.ok sourceId)
    (ret : returnQuery before place=.ok returnId) :
    selectedRows before argument length place=rowsFromIds before sourceId returnId := by
  simp only [selectedRows,source,ret,Except.toOption,Option.bind_some,id]

end DuplicatePrefix.CurrentCallConversionPlan

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionPlan.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved selected conversion plan dependency {name}: {dependency}"
