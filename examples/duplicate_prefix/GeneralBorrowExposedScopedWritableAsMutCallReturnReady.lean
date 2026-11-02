import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutCallReturn
import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutRawReady
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutCallReturnReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedWritableAsMutCallInput GeneralBorrowExposedScopedWritableAsMutCallReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem executes (s : Input) :
    let cfg:=ActualReferenceContext.config s.options (s.remaining+1) s.span
    let ended:=(held s).global.endCall (({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag)
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index s.data.input
    ∃ root post,
      SuccessfulTrace.Trace cfg s.limits (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] root post) ∧
      root={AsMutPtrReturn.writeFrame (caller s) 15 (.scalar (Scalar.fromPointer cfg.access.runtime.base (pointer s)))
        (by simpa [caller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using s.valid15) with location:=.mir ⟨7,0⟩} ∧
      post.memory=RetagEntry.updatedMemory s.machine.memory s.id s.entry (released s) ∧
      post.borrowTracker=some {held s with global:=ended} ∧
      GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine post ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context (released s) anchor s.selected s.head s.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location =>
          Nonempty (GeneralBorrowExposedScopedWritableReadData.Data (released s) location ended.protectedTags anchor s.selected s.head s.tail
            (fun position=>s.data.resources.component.support position ∨ position=anchor.toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data (released s) location ended.protectedTags anchor s.selected s.head s.tail .Write) ∧
          Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data (released s) location ended.protectedTags anchor s.selected s.head s.tail))
          s.offset (s.offset+s.len) (released s).locations ∧
        (released s).locations.WellFormed ∧ (released s).locations.size=s.entry.allocation.extra.locations.size := by
  obtain ⟨root,post,trace,frameEq,memoryEq,trackedEq,releaseDone,runtime⟩:=GeneralBorrowExposedScopedWritableAsMutCallReturn.executes s
  have ready:=GeneralBorrowExposedScopedWritableAsMutRawReady.ready s.entry.allocation.extra s.tracker s.id s.parentTag s.offset s.len
    s.selected s.head s.tail s.data s.atBase s.full s.rangePositive s.clean
  obtain ⟨context,owned,well,size⟩:=ready.2
  refine ⟨root,post,trace,frameEq,memoryEq,trackedEq,runtime,context,?_,well,size⟩
  intro position valid positive lower upper
  obtain ⟨⟨data⟩,write⟩:=owned position valid positive lower upper
  refine ⟨⟨data⟩,write,⟨?_⟩⟩
  exact GeneralBorrowExposedScopedWritableReadData.strong _ _ _ _ _ _ _ _ context data
end
end DuplicatePrefix.GeneralBorrowExposedScopedWritableAsMutCallReturnReady
