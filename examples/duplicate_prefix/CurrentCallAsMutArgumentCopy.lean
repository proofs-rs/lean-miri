import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.AsMutPushPreserves
import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnRuntime
import duplicate_prefix.AsMutCallStep
import duplicate_prefix.S05ConcreteFnEntryRaw
import duplicate_prefix.CurrentCallTypedFnEntry
import duplicate_prefix.GenericAsMutCallFrontend
import duplicate_prefix.GeneralBorrowRawAsMutShape
import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.AsMutCallCore
import duplicate_prefix.AsMutEntryFacts
import duplicate_prefix.AsMutFinish
import duplicate_prefix.AsMutLocalStages
import duplicate_prefix.AsMutPush
import duplicate_prefix.CallLocalRead
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins
import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.GeneralBorrowRawFnEntryExecution
import duplicate_prefix.MetadataArgument
import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ScopedFrame

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Validity
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual protected mutable FnEntry validation from internal operation certificates.
Physical storage, cache and fuel conditions stay explicit; the actual
initializer uses the sparse allocator's chosen slot, including reuse. -/
theorem positive
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let cfg := config options remaining span
    let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
    let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let finalTree := child.tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata cacheOrigins
  have info := RootReferenceInfo.facts options remaining span ctx false
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have readDone : read.status = .Completed := literalReadCompleted
  have childDone : child.outcome = .ok () := childDone
  have childComplete : read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) ChildBorrow.fnEntryPolicy.outsidePermission true =
        ⟨child.tree,.ok ()⟩ := GeneralBorrowFreshReborrowStages.child_complete child childDone
  exact ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
      ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy GeneralBorrowFreshChild.inside
      rfl (by decide +kernel) (by exact ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
      info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
      info.sized info.readable "&mut [u8]" info.named info.classified
      id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode
      borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race read.tree child.tree
      rfl readDone childComplete metadata notConstructed
end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Validity
namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Argument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def copiedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

def finalTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64) :=
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree

/-- Actual mutable MIR argument copy with real protected FnEntry runtime validation on
a general multiple-root forest using internal operation certificates;
physical/compiler/fuel premises stay explicit. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)))
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame]
  have postCached : copied.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have checked := (CurrentCallAsMutArgumentCopy.Validity.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames copied machine
    tracker enabled mode borrowFrame frameBorrow fresh literalReadCompleted childDone capacity localId postValid postLive postCached ghost shallow
    cachedAddress present race metadata cacheOrigins)
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Argument

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.PassArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess RootArgumentEntry
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem reference_storage_trivial : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime 3 = .ok true := by decide +kernel

theorem pass_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (dead : frame.locals[1].value = .dead)
    (cached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)))
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let liveFrame := RootArgumentEntry.liveFrame frame 1 valid
    let copied := CurrentCallAsMutArgumentCopy.Argument.copiedFrame liveFrame 1 value (by simpa only [liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ 3 false
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set 1
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := (copied.locals[1]'(by simpa only [copied,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)} resultMachine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have typed : frame.body.locals[1]? = some 3 := by rw [body];rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames frame machine 1 3 valid
    typed reference_storage_trivial dead noClocks
  have postValid : (1 : MIR.LocalId) < (liveFrame frame 1 valid).locals.size := by simpa only [liveFrame,Array.size_set] using valid
  have postCached : ((liveFrame frame 1 valid).locals[1]'postValid).layout = some ActualReferenceMetadata.reference := by
    simpa only [liveFrame,Array.getElem_set_self] using cached
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff frames
    (liveFrame frame 1 valid) machine 1 ActualReferenceMetadata.reference postValid postCached ActualReferenceMetadata.reference_sized
  have compat : h.checkArgumentCompat () (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact AsMutEntryFacts.argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1,#[]⟩ 3 _ _ _ _ _
  · change (3 == (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (ActualReferenceMetadata.reference.layout == (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact CurrentCallAsMutArgumentCopy.Argument.copy_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds frames
      (liveFrame frame 1 valid) machine tracker enabled mode borrowFrame frameBorrow fresh literalReadCompleted childDone capacity 1 postValid .uninit
      (by simp [liveFrame,Array.getElem_set_self]) postCached noClocks ghost shallow cachedAddress present race metadata cacheOrigins _ rfl

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.PassArgument

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Install
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def spanFrame (frame : CompilerFrameContext.ActualFrame) :=
  {frame with location := .unwinding ⟨613⟩}
def cacheFrame (frame : CompilerFrameContext.ActualFrame) (valid : (1 : MIR.LocalId) < frame.locals.size) :=
  LocalOperands.cachedLayoutFrame (spanFrame frame) 1 ActualReferenceMetadata.reference valid

def resultFrame (frame : CompilerFrameContext.ActualFrame) (valid : (1 : MIR.LocalId) < frame.locals.size)
    (value adjusted : Immediate Provenance) (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  let cached := cacheFrame frame valid
  let live := RootArgumentEntry.liveFrame cached 1 (by simpa [cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid)
  let copied := CurrentCallAsMutArgumentCopy.Argument.copiedFrame live 1 value (by simpa [live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid)
  {(TypedBorrowSteps.registeredFrame copied borrowFrame id tag) with
   locals := (copied.locals.set 1 {value := .live (.immediate adjusted),layout := (copied.locals[1]'(by simpa [copied,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid)).layout}
      (by simpa [copied,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid))}

def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  AsMutCallCore.spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ ty.ty false
  pure (1,1)

theorem install
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead)
    (uncached : frame.locals[1].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)))
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have query := AsMutLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨613⟩
  change AsMutCallCore.spanAt h ⟨613⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := AsMutLocalStages.layout1 options limits (remaining+1) span frames (spanFrame frame) machine
    body identity callee valid uncached
  have cachedValid : (1 : MIR.LocalId) < (cacheFrame frame valid).locals.size := by
    simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid
  have cached : (cacheFrame frame valid).locals[1].layout = some ActualReferenceMetadata.reference := by
    simp [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self]
  have deadCached : (cacheFrame frame valid).locals[1].value = .dead := by
    simpa [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,spanFrame] using dead
  have passed := CurrentCallAsMutArgumentCopy.PassArgument.pass_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames (cacheFrame frame valid)
    machine tracker enabled mode borrowFrame frameBorrow fresh literalReadCompleted childDone capacity cachedValid body deadCached cached noClocks ghost shallow
    cachedAddress present race metadata cacheOrigins
  dsimp only [spanFrame] at layout
  dsimp only [cacheFrame,spanFrame] at passed
  unfold action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [setspan]
  dsimp only
  rw [layout]
  dsimp only
  rw [ActualReferenceMetadata.reference_ty]
  rw [passed]
  simp only [pure,Pure.pure,EStateM.pure]
  congr 1

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Install

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.ScopedInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem install
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead)
    (uncached : frame.locals[1].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)))
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (CurrentCallAsMutArgumentCopy.Install.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (CurrentCallAsMutArgumentCopy.Install.resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let h := ExecutionMachine.callHooks cfg limits
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let enteredTracker := {tracker with retagMode := RetagPolicy.RetagMode.FnEntry}
  let enteredMachine := ScopedFrame.entered machine tracker .FnEntry
  let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine enteredMachine enteredTracker fresh)
      (ReferenceBorrowDriver.allocatedTracker enteredTracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let resultFrame := CurrentCallAsMutArgumentCopy.Install.resultFrame frame valid value adjusted borrowFrame id tracker.global.nextPointerTag
  let nextTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker enteredTracker fresh) tracker.global.nextPointerTag
  have installed := CurrentCallAsMutArgumentCopy.Install.install options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame
    enteredMachine enteredTracker rfl rfl borrowFrame frameBorrow fresh literalReadCompleted childDone capacity valid body identity callee dead uncached
    noClocks ghost shallow cachedAddress present race metadata cacheOrigins
  have body : CurrentCallAsMutArgumentCopy.Install.action h value
      {(Storage.withCurrent frames frame machine) with machine := ScopedFrame.entered machine tracker .FnEntry} =
      .ok (1,1) (Storage.withCurrent frames resultFrame resultMachine) := installed
  have scope := ScopedFrame.changed_state (CurrentCallAsMutArgumentCopy.Install.action h value) (Storage.withCurrent frames frame machine)
    (Storage.withCurrent frames resultFrame resultMachine) tracker nextTracker .FnEntry (1,1) enabled rfl body
  change MachineHooks.withRetagMode .FnEntry (CurrentCallAsMutArgumentCopy.Install.action h value) (Storage.withCurrent frames frame machine) = _
  simpa only [Storage.withCurrent,resultMachine,resultFrame,nextTracker,enteredMachine,enteredTracker,
    ScopedFrame.entered,TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker] using scope

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.ScopedInstall

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Tail
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
open AsMutCallCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : RootHooks) (value : Immediate Provenance) (destinationOp : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (CurrentCallAsMutArgumentCopy.Install.action h value)
  spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.asMutPtrAbi.ret HelperCompilerFacts.asMutPtrAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == HelperCompilerFacts.asMutPtrAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem core_eq (h : RootHooks) (value : Immediate Provenance) (destination : RuntimeStackPlace Provenance) :
    AsMutCallCore.core h ⟨.immediate value,ActualReferenceMetadata.reference⟩ destination = (do
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue)
      action h value destinationOp) := by
  unfold AsMutCallCore.core action CurrentCallAsMutArgumentCopy.Install.action
  simp only [bind_assoc]
  rfl
theorem run
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead)
    (uncached : frame.locals[1].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)))

    (old : Immediate Provenance) (destLayout : LocalLayout)
    (preamble : MIR.SpanRef) (located : frame.location = .unwinding preamble)
    (track : frame.trackCallerArg = none)
    (dead0 : (frame.locals[0]'(by have bound : (1 : Nat) < frame.locals.size := valid; omega)).value = .dead) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      value ⟨.immediate old,destLayout⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        (AsMutDone.doneFrame {(CurrentCallAsMutArgumentCopy.Install.resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) with location := .unwinding preamble}) resultMachine) := by
  have bound : (1 : Nat) < frame.locals.size := valid
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let result := CurrentCallAsMutArgumentCopy.Install.resultFrame frame valid value adjusted borrowFrame id tracker.global.nextPointerTag
  let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  have same : {frame with trackCallerArg := none} = frame := by rw [←track]
  have getframe := CallEntryLocals.get_frame options limits (remaining+1) span frames frame machine
  have setframe := CallEntryLocals.set_frame options limits (remaining+1) span frames frame frame machine
  have installed := CurrentCallAsMutArgumentCopy.ScopedInstall.install options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled
    defaultMode borrowFrame frameBorrow fresh literalReadCompleted childDone capacity valid body identity callee dead uncached noClocks ghost shallow
    cachedAddress present race metadata cacheOrigins
  have resultBody : result.body = HelperCompilerFacts.asMutPtrBody.body := body
  have resultIdentity : result.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity := identity
  have resultCallee : result.functionInstance = HelperCompilerFacts.asMutPtrCall.callee := callee
  have resultValid : 0 < result.locals.size := by
    simp only [result,CurrentCallAsMutArgumentCopy.Install.resultFrame,CurrentCallAsMutArgumentCopy.Install.cacheFrame,CurrentCallAsMutArgumentCopy.Install.spanFrame,
      LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set]
    omega
  have resultDead : result.locals[0].value = .dead := by
    simpa [result,CurrentCallAsMutArgumentCopy.Install.resultFrame,CurrentCallAsMutArgumentCopy.Install.cacheFrame,CurrentCallAsMutArgumentCopy.Install.spanFrame,
      LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,CurrentCallAsMutArgumentCopy.Argument.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set] using dead0
  have resultClocks : result.extra.dataRace = none := noClocks
  have finished := AsMutFinish.finish options limits (remaining+1) span frames result resultMachine preamble
    resultBody resultIdentity resultCallee resultValid resultDead resultClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [getframe]
  dsimp only
  rw [located]
  simp only [pure,Pure.pure,EStateM.pure,bind,EStateM.bind]
  rw [←located,same,setframe]
  dsimp only
  rw [installed]
  dsimp only
  change AsMutFinish.action h preamble (Storage.withCurrent frames result resultMachine) = _
  exact finished

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Tail

namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Entry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawFrame (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :=
  let supply := AsMutPush.fresh state.machine
  AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2

theorem raw_size (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :
    (rawFrame options state destination).locals.size = 5 := by with_unfolding_all rfl

def initialized (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (value adjusted : Immediate Provenance) (id : AllocId) (tag : BorTag) :=
  AsMutDone.doneFrame {(CurrentCallAsMutArgumentCopy.Install.resultFrame (rawFrame options state destination)
    (by rw [raw_size];decide) value adjusted {} id tag) with location := .unwinding AsMutEntryFacts.asMutPreamble}

theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destId : MIR.LocalId) (destValid : destId < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[destId].value = .live (.immediate old))
    (destCached : caller.locals[destId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let before := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let before := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let frame := rawFrame options before destination
  let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debugOff frames caller machine destId
    CopyCompilerFacts.destPointerLayout old destValid destLive destCached (by decide +kernel) callerClocks ghost
  have pushed := AsMutPush.actual_push options () (remaining+1) span before destination thread index current active top topPresent
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postCached : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postPresent : postMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact present
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact race
  have postMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame postMachine)).metadata = PreparedReflection.actual.runtime := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact metadata
  have postOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame postMachine)) := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact cacheOrigins
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
  have frameBorrow : frame.extra.borrowTracker = some ({} : FrameState) := by
    simp [frame,rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,enabled]
  have frameSize : frame.locals.size = 5 := raw_size options before destination
  have tail := CurrentCallAsMutArgumentCopy.Tail.run options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds
    (frames.push caller) frame postMachine tracker postTracked defaultMode {} frameBorrow fresh literalReadCompleted childDone capacity
    (by rw [frameSize];decide) rfl rfl rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl) frameRace
    postGhost postShallow postCached postPresent postRace postMetadata postOrigins old CopyCompilerFacts.destPointerLayout
    AsMutEntryFacts.asMutPreamble rfl rfl (by with_unfolding_all rfl)
  dsimp only
  rw [AsMutCallCore.actual_entry_eq,CurrentCallAsMutArgumentCopy.Tail.core_eq]
  simp only [bind,EStateM.bind]
  rw [read]
  dsimp only
  have pushActual : h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before =
      .ok () (AsMutPush.completed options.userRelevantCrates before destination current) := by
    change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
      (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debugOff]
    exact pushed
  dsimp only [h,before,destination] at pushActual
  rw [pushActual]
  exact tail

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Entry
namespace DuplicatePrefix.CurrentCallAsMutArgumentCopy.Body
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual protected helper initialization followed by all ten pure MIR statements.
The body leaves memory/tracker unchanged and returns the actual fresh-child pointer;
protector release and return are intentionally subsequent operations. -/
theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destId : MIR.LocalId) (destValid : destId < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[destId].value = .live (.immediate old))
    (destCached : caller.locals[destId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let before := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push caller)
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (frames.push caller) frame resultMachine)
        (Storage.withCurrent (frames.push caller) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  have notConstructed := DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ metadata cacheOrigins
  let before := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let pointer : Pointer Provenance := Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm
  let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
  let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have entered := CurrentCallAsMutArgumentCopy.Entry.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    literalReadCompleted childDone capacity destId destValid old destLive destCached callerClocks ghost shallow cachedAddress present race
    metadata cacheOrigins thread index current active top topPresent
  have fields : resultMachine.user.payload.ghost = machine.user.payload.ghost ∧
      resultMachine.user.payload.validation = machine.user.payload.validation ∧
      resultMachine.user.addresses = machine.user.addresses ∧
      resultMachine.user.payload.payload.user = machine.user.payload.payload.user := by
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,postMachine,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced postMachine.memory id resultEntry
  have carrier : AsMutPtrCarrier.Valid resultMachine (.inl pointer) len :=
    .positive id tracker.global.nextPointerTag base offset len resultEntry (by rw [fields.2.2.1];exact cachedAddress)
      resultPresent positive nonzero signedFits bounds
  have slots := GeneralBorrowRawAsMutShape.locals options before destination value adjusted id tracker.global.nextPointerTag
  have frameFacts := GeneralBorrowRawAsMutShape.fixed options before destination value adjusted id tracker.global.nextPointerTag
  have size : frame.locals.size = 5 := by rw [show frame.locals = _ from slots];rfl
  have frameRace : frame.extra.dataRace = none := by
    change ((AsMutPush.fresh before.machine).1.dataRace.map _) = none
    change machine.dataRace.map _ = none
    rw [race];rfl
  obtain ⟨done,trace,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,source,sizeDone,location,pointerDone,dead2,dead3,dead4⟩ :=
    AsMutPtrBody.actual_ten_statements options limits remaining span debugOff validityFuel validationEq
      (frames.push caller) frame resultMachine pointer len carrier size
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      frameFacts.1 frameFacts.2.1 frameFacts.2.2.1 frameFacts.2.2.2.1 frameRace
      (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      rfl defaultMode (fields.1.trans ghost) (fields.2.1.trans shallow) dynamicFuel fuelEq cmp
      (by change resultMachine.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2];exact metadata)
      (by change resultMachine.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2];exact notConstructed)
  exact ⟨done,entered,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,source,sizeDone,dead2,dead3,dead4⟩

theorem caller_before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none) :
    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator (Storage.withCurrent #[] caller machine) =
      .ok () (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  let root := AsMutUncachedCall.cachedCaller caller destValid
  have rootValid : (15 : MIR.LocalId) < root.locals.size := by
    simpa [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have rootLive : root.locals[15].value = .live (.immediate old) := by
    simpa [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using destLive
  have rootCached : root.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  obtain ⟨done,entered,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4⟩ :=
    before_return options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds #[] root machine tracker enabled defaultMode fresh
      literalReadCompleted childDone capacity 15 rootValid old rootLive rootCached callerClocks ghost shallow cachedAddress present race
      metadata cacheOrigins thread index current active top topPresent
  have called := GenericAsMutCallFrontend.call_uncached options limits remaining budget dispatchFuel span debugOff source cmp
    caller _ machine _ _ sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16
    destValid old destLive uncached callerClocks ghost backend race entered
  exact ⟨done,called,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4⟩


/-- Current completed mutable authority derives both actual FnEntry callbacks
internally, then immediately executes the real caller and helper body. The
actual constructor output and its resources remain available for helper release. -/
theorem caller_from_authority
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : CandidateStableCallOwnership.Completes entry.allocation.extra completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (parent : UniIndex) (parentNode : Miri.TreeBorrows.TreeNode)
    (parentPresent : entry.allocation.extra.nodes.get parent = some parentNode)
    (parentTagEq : parentNode.tag = parentTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size < 65536)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowForestFnEntry.operation entry.allocation.extra tracker.global {} id parentTag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1 ∧
      output.frame.protectedTags = #[(id,output.tag)] ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = entry.allocation.extra.locations.size ∧
      output.child.tree.nodes.size ≤ entry.allocation.extra.nodes.size+1 ∧
      output.child.tree = CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = entry.allocation.extra.roots ∧
        CandidateStableCallOwnership.Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
        GeneralRangeMapOrigins.OwnedOn
          (S05CompletedAncestryReadMutable.Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
            output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree ∧
        (∀ index node, entry.allocation.extra.nodes.get index = some node →
          ∃ next, output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧
            next.parent = node.parent ∧ next.isExposed = node.isExposed) ∧
        (∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧ node.isExposed = false) ∧
        (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len) →
          GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)) ∧

    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator (Storage.withCurrent #[] caller machine) =
      .ok () (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    entry.allocation.extra runtime.formed.toGraphState parent parentNode parentPresent
  have treeBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacity]
    exact bounds
  have nonzeroLen : len ≠ 0 := by intro equal;subst len;simp at positive
  obtain ⟨output,actual,tag,global,frameProtected,readDone,childDone,afterRuntime,afterCapacity,growth,
    child,lookup,roots,afterComplete,afterOwned,_,_,activity,afterOrder,oldNodes,childNode⟩ :=
    S05ConcreteFnEntryRaw.invoke entry.allocation.extra tracker.global {} id completion runtime complete order
      position root parent rootNode parentNode slot rootAt parentPresent path fresh nodeRoom short offset len nonzeroLen treeBounds owned
  rw [parentTagEq] at actual
  let literal := CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have normalized : GeneralBorrowForestFnEntry.operation entry.allocation.extra tracker.global {} id parentTag offset len
      .VisitChildrenOfAccessed = .ok literal := by
    simpa only [CandidateCurrentFnEntryRaw.operation] using
      CurrentCallTypedFnEntry.literal_operation entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have outputEq : output = literal := Except.ok.inj (actual.symm.trans normalized)
  have readCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,
      GlobalState.addProtector,FrameState.addProtector] using readDone
  have childCompleted : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,
      GlobalState.addProtector,FrameState.addProtector,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using childDone
  have treeEq : output.child.tree = CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len := by
    rw [outputEq]
    rfl
  obtain ⟨_,readRuntime,_,_,readNodes,_,readTags,readCapacity⟩ := S05ConcreteFnEntryRaw.prepare_read
    entry.allocation.extra tracker.global {} id completion runtime complete order position root parent rootNode parentNode
    slot rootAt parentPresent path fresh offset len treeBounds owned short .VisitChildrenOfAccessed
  rw [parentTagEq] at readRuntime readNodes readTags readCapacity
  let accessed := literal.access.tree
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed literal.global at readRuntime
  change accessed.nodes = entry.allocation.extra.nodes at readNodes
  change accessed.tagMapping = entry.allocation.extra.tagMapping at readTags
  change accessed.locations.size = entry.allocation.extra.locations.size at readCapacity
  obtain ⟨_,_,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    entry.allocation.extra tracker.global {} id fresh runtime
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tagMapping tracker.global.nextPointerTag := by
    rw [readTags]
    exact originalFresh
  have afterRoom : accessed.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have parentAfter : accessed.nodeAt parent = some parentNode := by
    change accessed.nodes.get parent = some parentNode
    rw [readNodes]
    exact parentPresent
  have parentTagged : accessed.indexOfTag parentTag = some parent := by
    unfold BorrowTree.indexOfTag
    rw [readTags]
    have tagged := (complete.2.2.2.2.1 parent parentNode parentPresent).1
    simpa only [parentTagEq] using tagged
  have afterBounds : offset.toNat+len.toNat ≤ accessed.locations.size.bytes.toNat := by rw [readCapacity];exact treeBounds
  obtain ⟨hiddenChild,hiddenLookup,⟨node,nodeAt,nodeTag,hidden⟩,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct
    accessed literal.global readRuntime parentTag tracker.global.nextPointerTag parent parentNode parentTagged parentAfter afterFresh afterRoom
    offset len nonzeroLen afterBounds
  have hiddenLookup' : literal.child.tree.indexOfTag tracker.global.nextPointerTag = some hiddenChild := by
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshMetadataChildMutableSlot.result,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using hiddenLookup
  have actualLookup : literal.child.tree.indexOfTag tracker.global.nextPointerTag = some child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using lookup
  have sameChild : hiddenChild = child := Option.some.inj (hiddenLookup'.symm.trans actualLookup)
  subst hiddenChild
  have childNodeHidden : ∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧ node.isExposed = false := by
    refine ⟨node,?_,nodeTag.trans tag.symm,hidden⟩
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshMetadataChildMutableSlot.result,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using nodeAt
  have targetActivity : ∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len) →
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len) := by
    intro target active
    have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed target .Write offset (offset+len) :=
      GeneralBorrowFreshActiveWithinAccess.normal entry.allocation.extra parentTag (Size.ofBytes offset) (Size.ofBytes len)
        .Read literal.global.protectedTags .VisitChildrenOfAccessed target offset (offset+len)
        runtime.formed.well treeBounds (Nat.le_refl _) (Nat.le_refl _) active
    have preserved := GeneralBorrowRawTargetActivity.protected_child accessed literal.global readRuntime
      parentTag tracker.global.nextPointerTag parent parentNode parentTagged parentAfter afterFresh afterRoom offset len nonzeroLen afterBounds
      target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) readActivity
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      accessed,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using preserved
  have body := caller_before_return options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh
    readCompleted childCompleted capacity destValid old destLive uncached callerClocks ghost shallow cachedAddress present race metadata cacheOrigins
    thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 backend
  refine ⟨output,actual,tag,global,?_,readDone,childDone,afterRuntime,afterCapacity,growth,treeEq,
    child,lookup,roots,afterComplete,afterOwned,activity,afterOrder,oldNodes,childNodeHidden,targetActivity,body⟩
  exact frameProtected


/-- The actual root call step includes source before-terminator accounting,
then the authority-derived helper entry and its real body trace. -/
theorem step_from_authority
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : CandidateStableCallOwnership.Completes entry.allocation.extra completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (parent : UniIndex) (parentNode : Miri.TreeBorrows.TreeNode)
    (parentPresent : entry.allocation.extra.nodes.get parent = some parentNode)
    (parentTagEq : parentNode.tag = parentTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size < 65536)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowForestFnEntry.operation entry.allocation.extra tracker.global {} id parentTag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1 ∧
      output.frame.protectedTags = #[(id,output.tag)] ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = entry.allocation.extra.locations.size ∧
      output.child.tree.nodes.size ≤ entry.allocation.extra.nodes.size+1 ∧
      output.child.tree = CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = entry.allocation.extra.roots ∧
        CandidateStableCallOwnership.Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
        GeneralRangeMapOrigins.OwnedOn
          (S05CompletedAncestryReadMutable.Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
            output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree ∧
        (∀ index node, entry.allocation.extra.nodes.get index = some node →
          ∃ next, output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧
            next.parent = node.parent ∧ next.isExposed = node.isExposed) ∧
        (∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧ node.isExposed = false) ∧
        (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len) →
          GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write offset (offset+len)) ∧

    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine)
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] caller machine) =
      ((Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine),.ok true) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine ∧
      GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine ∧
      done.extra.borrowTracker = some output.frame ∧ done.extra.dataRace = none ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧
      done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout ∧
      done.returnContinuation = .goto (some 7) .Continue ∧ done.vaList = #[] ∧
      done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] caller machine
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent #[] caller next
  have nextGhost : next.user.payload.ghost = false := (AsMutPtrReturn.accounted_ghost options remaining span machine).trans ghost
  have nextShallow : next.user.payload.validation = .Shallow := (AsMutPtrReturn.accounted_validation options remaining span machine).trans shallow
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddress : next.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have nextMetadata : (EvalProjectionMachine.arrays.get nextState).metadata = PreparedReflection.actual.runtime := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have nextOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get nextState) := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cacheOrigins
  obtain ⟨output,actual,tag,global,frameProtected,readDone,childDone,afterRuntime,afterCapacity,growth,treeEq,
    child,lookup,roots,afterComplete,afterOwned,activity,afterOrder,oldNodes,childNode,targetActivity,bodyResult⟩ :=
    caller_from_authority options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds caller next tracker enabled defaultMode fresh
      completion runtime complete order parent parentNode parentPresent parentTagEq nodeRoom short owned capacity
      destValid old destLive uncached callerClocks nextGhost nextShallow nextAddress present race nextMetadata nextOrigins
      thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 nextBackend
  obtain ⟨done,called,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4⟩ := bodyResult
  let root := AsMutUncachedCall.cachedCaller caller destValid
  let beforePush := Storage.withCurrent #[] root next
  let destination := (LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates beforePush destination current).machine
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry (Argument.finalTree entry.allocation.extra tracker parentTag offset len)}
  let frame := Entry.initialized options beforePush destination value adjusted id tracker.global.nextPointerTag
  have frameExtra : done.extra = frame.extra := extra
  obtain ⟨_,_,postRace,postAddress,postGhost,postShallow,postUser,postFixed⟩ :=
    AsMutPushPreserves.preserves options.userRelevantCrates beforePush destination current
  change post.user.payload.payload.user = next.user.payload.payload.user at postUser
  have helperGhost : resultMachine.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    exact postGhost.trans nextGhost
  have helperShallow : resultMachine.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    exact postShallow.trans nextShallow
  have helperRace : resultMachine.dataRace = none := by
    change post.dataRace = none
    exact postRace.trans race
  have helperBackend : resultMachine.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postUser]
    exact nextBackend
  have nextFlags := RootZeroCompleteState.tick_flags options remaining span machine
  have nextUnchecked : (cfg.terminators.getControl next.user).checkedArithmetic = false := nextFlags.1.trans unchecked
  have nextNoGc : (cfg.terminators.getControl next.user).gcInterval = 0 := nextFlags.2.trans noGc
  have helperUnchecked : (cfg.terminators.getControl resultMachine.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextUnchecked ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextUnchecked ⊢
    rw [postUser]
    exact nextUnchecked
  have helperNoGc : (cfg.terminators.getControl resultMachine.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextNoGc ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextNoGc ⊢
    rw [postUser]
    exact nextNoGc
  have helperFixed : resultMachine.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    exact postFixed.trans fixed
  let supply := AsMutPush.fresh next
  let rank := (AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2).extra.userRelevance
  let nextThread := if rank >= current.extra.userRelevance then {thread with topUserRelevantFrame := some 1} else thread
  have helperActive : resultMachine.threads.activeThread? = some nextThread := by
    change (GenericPushRelevance.afterPush supply.1 1 rank current.extra.userRelevance).threads.activeThread? = some nextThread
    exact AsMutPushPreserves.active_after_push supply.1 thread active 1 rank current.extra.userRelevance
  have indexBound : index < 2 := by
    have known := (Array.getElem?_eq_some_iff.mp topPresent).1
    simpa only [AsMutPush.pushed,Storage.withCurrent,Array.size_push,Array.size_empty] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < 2 := by
    have equal : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [equal] using indexBound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < 2 := by
    unfold nextThread at same
    split at same
    · have equal : (1 : Nat) = i := by simpa only [Option.some.injEq] using same
      omega
    · exact oldBound i same
  have helperRuntime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine :=
    ⟨helperGhost,helperShallow,helperRace,rfl,rfl,rfl,helperBackend,helperUnchecked,helperNoGc,helperFixed,⟨nextThread,helperActive⟩⟩
  have helperCache : GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine :=
    ⟨fun _ => ⟨nextThread,helperActive,cacheBound⟩⟩
  let literal := CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have normalized : GeneralBorrowForestFnEntry.operation entry.allocation.extra tracker.global {} id parentTag offset len
      .VisitChildrenOfAccessed = .ok literal := by
    simpa only [CandidateCurrentFnEntryRaw.operation] using
      CurrentCallTypedFnEntry.literal_operation entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have outputEq : output = literal := Except.ok.inj (actual.symm.trans normalized)
  have helperBorrow : done.extra.borrowTracker = some output.frame := by
    rw [frameExtra,outputEq]
    rfl
  have frameRace : frame.extra.dataRace = none := by
    change machine.dataRace.map _ = none
    rw [race]
    rfl
  have helperClocks : done.extra.dataRace = none := by rw [frameExtra];exact frameRace
  have helperBody : done.body = HelperCompilerFacts.asMutPtrBody.body := body
  have helperDestination : done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout := by
    rw [returnPlace]
    rfl
  have helperContinuation : done.returnContinuation = .goto (some 7) .Continue := by rw [continuation];rfl
  have helperVarargs : done.vaList = #[] := by rw [varargs];rfl
  have slots := GeneralBorrowRawAsMutShape.locals options beforePush destination value adjusted id tracker.global.nextPointerTag
  have helperOne : done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [sourceSlot]
    change frame.locals[1]? = _
    rw [show frame.locals = _ from slots]
    rfl
  have accounting := SourceControl.before_terminator cfg limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () initial = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[6]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  refine ⟨output,actual,tag,global,frameProtected,readDone,childDone,afterRuntime,afterCapacity,growth,treeEq,
    child,lookup,roots,afterComplete,afterOwned,activity,afterOrder,oldNodes,childNode,targetActivity,done,?_,
    trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4,helperRuntime,helperCache,helperBorrow,helperClocks,helperBody,helperDestination,helperContinuation,helperVarargs,helperOne⟩
  apply GenericCallStages.source_step cfg limits () initial nextState _ caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue
    AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) sourceLocation blockAt noStatement AsMutCallTerminator.source_call accounting' called
  simp [Storage.withCurrent,nextState]

end
end DuplicatePrefix.CurrentCallAsMutArgumentCopy.Body
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallAsMutArgumentCopy." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current AsMut argument dependency {dependency}"
