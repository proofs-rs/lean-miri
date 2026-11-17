import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenUncachedFrontend
namespace DuplicatePrefix.GeneralBorrowScopedRejectedFrameReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open LenUncachedFrontend PtrMetadataExecution
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def after (caller : CompilerFrameContext.ActualFrame) (valid : 11<caller.locals.size) (len : UInt64) :=
  {writeFrame (cachedCaller caller valid) 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
    (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location:=.mir ⟨3,0⟩}

structure Facts (before result : CompilerFrameContext.ActualFrame) (count len : UInt64) (value : Immediate Provenance) : Prop where
  body : result.body=RootBody.reflected.body.body
  identity : result.bodyIdentity=RootBody.reflected.body.identity
  callee : result.functionInstance=RootBody.reflected.functionInstance
  size : result.locals.size=25
  location : result.location=.mir ⟨3,0⟩
  extra : result.extra=before.extra
  continuation : result.returnContinuation=before.returnContinuation
  returnPlace : result.returnPlace=before.returnPlace
  varargs : result.vaList=before.vaList
  all : CopyHelperCleanup.AllImmediate result
  slot0 : result.locals[0]?=some ⟨.live (.immediate .uninit),none⟩
  slot7 : result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩
  slot8 : result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩
  slot9 : result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot10 : result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩
  slot11 : result.locals[11]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩
  slot12 : result.locals[12]?=some ⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩
  slot13 : result.locals[13]?=some ⟨.live (.immediate .uninit),none⟩

theorem build (before caller : CompilerFrameContext.ActualFrame) (count len : UInt64) (value : Immediate Provenance)
    (raw : GeneralBorrowForestSharedPreLenFrame.Facts before caller count value) (valid : 11<caller.locals.size) :
    Facts caller (after caller valid len) count len value := by
  have keep (index : Nat) (different : index≠11) : (after caller valid len).locals[index]?=caller.locals[index]? := by
    simp [after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  refine ⟨raw.body,raw.identity,raw.callee,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout] using raw.size
  · simpa [CopyHelperCleanup.AllImmediate,after,cachedCaller,writeFrame,ActualLocalCopy.written] using
      CopyHelperCleanup.all_immediate_written caller 11 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 len))) valid raw.all
  · rw [keep 0 (by decide)];exact raw.slot0
  · rw [keep 7 (by decide)];exact raw.slot7
  · rw [keep 8 (by decide)];exact raw.slot8
  · rw [keep 9 (by decide)];exact raw.slot9
  · rw [keep 10 (by decide)];exact raw.slot10
  · simp [after,cachedCaller,writeFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set,valid]
  · rw [keep 12 (by decide)];exact raw.slot12
  · rw [keep 13 (by decide)];exact raw.slot13
end
end DuplicatePrefix.GeneralBorrowScopedRejectedFrameReady
