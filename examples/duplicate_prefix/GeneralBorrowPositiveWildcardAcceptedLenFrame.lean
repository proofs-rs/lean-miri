import duplicate_prefix.GeneralBorrowPositiveWildcardNonzeroMachinePrefixMetadata
import duplicate_prefix.GeneralBorrowScopedRejectedFrameReady
import duplicate_prefix.GeneralBorrowExposedScopedAcceptedControl
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedLenFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open LenUncachedFrontend PtrMetadataExecution ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
abbrev frame (i : GeneralBorrowExposedScopedLenCallInput.Input) := GeneralBorrowScopedRejectedFrameReady.after i.caller i.valid i.len
/-- Actual len-return local facts for the accepted scalar prefix, derived
from the original-call Origin and the physical helper's exact root frame. -/
theorem facts (s : GeneralBorrowPositiveWildcardNonzeroInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input)
    (origin : GeneralBorrowPositiveWildcardNonzeroMachinePrefixMetadata.Origin s updated i) :
    GeneralBorrowExposedScopedAcceptedControl.FrameFacts (frame i) i.len s.count := by
  let value := (RetagReferencePlace.sliceValue (config i.options i.remaining i.span).access.runtime.base
    (Pointer.new (.concrete i.id i.exprTag) (Size.ofBytes (i.base+i.offset))) i.len SharedReferenceMetadata.sharedLayout).imm
  have slot11 : i.caller.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ := by
    rw [Array.getElem?_eq_getElem i.valid]
    exact congrArg some (congr (congrArg LocalState.mk i.live) i.uncached)
  have slot12 : i.caller.locals[12]?=some ⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩ := by
    rw [Array.getElem?_eq_getElem i.sourceValid]
    exact congrArg some (congr (congrArg LocalState.mk i.sourceLive) i.sourceCached)
  have raw : GeneralBorrowForestSharedPreLenFrame.Facts i.caller i.caller s.count value :=
    ⟨i.sourceBody,i.identity,i.callee,origin.size,i.located,rfl,rfl,rfl,rfl,origin.allImmediate,
      origin.slot0,origin.slot7,origin.slot8,origin.slot9,origin.slot10,slot11,slot12,origin.slot13⟩
  have next := GeneralBorrowScopedRejectedFrameReady.build i.caller i.caller s.count i.len value raw i.valid
  refine ⟨next.body,next.identity,next.callee,next.size,next.location,next.all,(congrArg (·.dataRace) next.extra).trans i.noClocks,
    next.slot0,next.slot7,next.slot8,next.slot9,next.slot10,next.slot11,⟨value,?_⟩,next.slot13,?_,?_⟩
  · rw [next.slot12]
    rfl
  · have known:=origin.unused 15 (by decide) (by decide)
    simpa [frame,GeneralBorrowScopedRejectedFrameReady.after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set] using known
  · have known:=origin.unused 16 (by decide) (by decide)
    simpa [frame,GeneralBorrowScopedRejectedFrameReady.after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set] using known

theorem keep (i : GeneralBorrowExposedScopedLenCallInput.Input) (index : Nat) (different : index≠11) :
    (frame i).locals[index]?=i.caller.locals[index]? := by
  simp [frame,GeneralBorrowScopedRejectedFrameReady.after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedLenFrame
