import duplicate_prefix.GeneralBorrowPositiveWildcardSparseArgumentCopy
import duplicate_prefix.PositiveRootArguments
import duplicate_prefix.RootArgumentsTwo
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseFunctionArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open PositiveRootArguments

def resultMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (len : UInt64) :=
  {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory machine.memory id entry
      (GeneralBorrowPositiveWildcardSparseArgumentCopy.finalTree entry.allocation.extra tracker len)}

theorem body
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (global : GlobalState)
    (base len n : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (head : UniIndex) (extras : List UniIndex)
    (leafGeometry : GeneralBorrowSparseExposedLeafState.Geometry entry.allocation.extra head extras)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal ⟨global,.FnEntry⟩ global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag) n).frame
        (resultMachine machine ⟨global,.FnEntry⟩ fresh id entry len)) := by
  let l1 := firstLive root
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
  let d1 := PositiveRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag
  let m1 := resultMachine machine ⟨global,.FnEntry⟩ fresh id entry len
  have live1 : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by
    simp [l1,firstLive,live,write,i1]
  have cached1 : (l1.frame.locals[1]'(l1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp [l1,firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,i1]
  have rawCopy := GeneralBorrowPositiveWildcardSparseArgumentCopy.copy_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id entry base len positive nonzero signedFits bounds frames l1.frame machine
    ⟨global,.FnEntry⟩ enabled rfl borrowFrame frameBorrow fresh 1 (l1.valid i1) .uninit live1 cached1
    l1.noClocks ghost shallow cachedAddress present race
    position positionValid ordered addressRow addressMode exposedAlloc head extras leafGeometry well treeBounds sourceRaw tagFresh noFree fits metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView (by simp)
  have copy1 : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames l1.frame machine) = .ok () (Storage.withCurrent frames d1.frame m1) := by
    simpa only [d1,PositiveRootArguments.firstDone,protectedRoot,write,i1,GeneralBorrowPositiveWildcardSparseArgumentCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set_self,Array.set_set,
      m1,resultMachine] using rawCopy
  have nextDead : (d1.frame.locals[2]'(d1.valid i2)).value = .dead := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using dead2
  have nextCache : (d1.frame.locals[2]'(d1.valid i2)).layout = none := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using cache2
  exact RootArgumentsTwo.body options limits remaining span debugOff validityFuel validationEq frames root d1 machine m1
    value n dead1 cache1 nextDead nextCache ghost shallow ghost shallow copy1
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseFunctionArguments
