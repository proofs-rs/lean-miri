import duplicate_prefix.GeneralBorrowForestFunctionEntryToShared
import duplicate_prefix.GeneralBorrowForestEntrySharedExpression
namespace DuplicatePrefix.GeneralBorrowForestSharedPreLenFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowForestFunctionEntryToShared
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
def after (before : CompilerFrameContext.ActualFrame) (valid : 12 < before.locals.size) (value : Immediate Provenance) :=
  CopyHelperSteps.advance (ActualLocalCopy.written before 12 SharedReferenceMetadata.sharedLayout valid value) ⟨2,11⟩
set_option autoImplicit false in
structure Facts (before result : CompilerFrameContext.ActualFrame) (count : UInt64) (value : Immediate Provenance) : Prop where
  body : result.body = RootBody.reflected.body.body
  identity : result.bodyIdentity = RootBody.reflected.body.identity
  callee : result.functionInstance = RootBody.reflected.functionInstance
  size : result.locals.size = 25
  location : result.location = .mir ⟨2,12⟩
  extra : result.extra = before.extra
  continuation : result.returnContinuation = before.returnContinuation
  returnPlace : result.returnPlace = before.returnPlace
  varargs : result.vaList = before.vaList
  all : CopyHelperCleanup.AllImmediate result
  slot0 : result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  slot7 : result.locals[7]? = some ⟨.live (.immediate .uninit),none⟩
  slot8 : result.locals[8]? = some ⟨.live (.immediate .uninit),none⟩
  slot9 : result.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot10 : result.locals[10]? = some ⟨.live (.immediate .uninit),none⟩
  slot11 : result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩
  slot12 : result.locals[12]? = some ⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩
  slot13 : result.locals[13]? = some ⟨.live (.immediate .uninit),none⟩

theorem build (before : CompilerFrameContext.ActualFrame) (original value : Immediate Provenance)
    (count : UInt64) (borrowFrame : FrameState) (ready : Ready before original count borrowFrame)
    (valid : 12 < before.locals.size) : Facts before (after before valid value) count value := by
  have keep (i : Nat) (different : i≠12) : (after before valid value).locals[i]? = before.locals[i]? := by
    simp [after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  refine ⟨ready.body,ready.identity,ready.callee,?_,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using ready.size
  · exact CopyHelperCleanup.all_immediate_written before 12 SharedReferenceMetadata.sharedLayout value valid ready.immediate
  · rw [keep 0 (by decide)];exact ready.slot0
  · rw [keep 7 (by decide)];exact ready.slot7
  · rw [keep 8 (by decide)];exact ready.slot8
  · rw [keep 9 (by decide)];exact ready.slot9
  · rw [keep 10 (by decide)];exact ready.slot10
  · rw [keep 11 (by decide)];exact ready.lenSlot
  · simp [after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,valid]
  · rw [keep 13 (by decide)];exact ready.slot13
end
end DuplicatePrefix.GeneralBorrowForestSharedPreLenFrame
