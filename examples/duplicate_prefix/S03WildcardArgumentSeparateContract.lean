import duplicate_prefix.S03WildcardArgumentSeparateComplete
import duplicate_prefix.S03WildcardArgumentResources

namespace DuplicatePrefix.S03WildcardArgumentSeparateContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original wildcard hit in a live allocation distinct from the concrete
return destination, for every count. Initial Hit/live metadata are supplied by
Candidate classification; the raw driver derives all later facts and success. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == hit.id) = some (hit.id,entry))
    (separate : input.contract.destination.id ≠ hit.id)
    (tag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let facts := S03WildcardArgumentResources.of_contract input wildcard
  have same : input.contract.tracker = input.contract.destination.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans input.contract.destination.enabled)
  have member : (hit.id,entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.contract.tracker.global :=
    ⟨input.contract.runtime.formed _ member,input.contract.runtime.coherent _ member,input.contract.runtime.possible _ member,
      input.contract.resources.tagsBelow _ member⟩
  rw [same] at runtime
  have margin := input.contract.resources.nodeRoom _ member
  dsimp only at margin
  have info := MemoryCopyBridge.live_alloc_info before.memory hit.id entry live
  have infoEq := Except.ok.inj (hit.known.symm.trans info)
  have size : hit.info.size = entry.allocation.byteSize := congrArg AllocationInfo.size infoEq
  have inverse := hit.geometry
  rw [size] at inverse
  let initial : S03WildcardArgumentSeparatePacket.Initial options limits remaining span before pointer place := {
    model := input.contract.model,destination := input.contract.destination,
    runtime := facts.runtime,distinct := facts.distinct,order := facts.order,returnRoom := facts.returnRoom,
    first := facts.first,second := facts.second,tagMargin := facts.tagMargin,
    argumentId := hit.id,argumentEntry := entry,argumentLive := live,separate := separate,
    argumentWildcard := wildcard,nonnull := facts.nonnull,argumentBase := hit.base,argumentCached := hit.cached,
    addressMode := facts.addressMode,inverse := inverse,exposed := hit.exposed,
    argumentRuntime := runtime,argumentMargin := margin,tag := tag,returnConcrete := returnConcrete,
    dynamicFuel := facts.dynamicFuel,validityFuel := facts.validityFuel,budget := facts.budget,
    dynamicEq := facts.dynamicEq,validityEq := facts.validityEq,dispatchEq := facts.dispatchEq,
    notConstructed := input.slice_not_constructed,extras := input.return_extras,
    thread := input.contract.thread,active := input.contract.active,noCache := input.contract.emptyHarnessCache }
  exact S03WildcardArgumentSeparateComplete.complete initial count

end
end DuplicatePrefix.S03WildcardArgumentSeparateContract
