import duplicate_prefix.GeneralBorrowObserverSharedLedger
namespace DuplicatePrefix.GeneralBorrowSharedFnEntryGlobalReturn
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual fresh Strong registration and singleton helper endCall leave the
whole pre-helper protector table unchanged. Raw runtime high-water data derive
fresh-tag absence; no operation outcome or final query premise is supplied. -/
theorem global (tree : BorrowTree) (before : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree before)
    (frame : FrameState) (allocation : AllocId) (room : before.nextPointerTag.value < 18446744073709551615) :
    (GeneralBorrowFnEntryRegistration.registered before frame allocation room).1.endCall
      (({} : FrameState).addProtector allocation before.nextPointerTag) = GeneralBorrowFnEntryRegistration.advanced before room := by
  have complete := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unprotected⟩ := GenericFunctionTagFormation.fresh_above tree _ _ before.nextPointerTag complete (Nat.le_refl _)
  simp only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
    GlobalState.addProtector,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rw [GeneralBorrowObserverSharedLedger.remove_insert,
    GeneralBorrowObserverReadRestore.remove_absent _ _ unprotected]

/-- Every pre-helper protector query (including the return-slot tags) is exact
on the real post-helper endCall global, without per-query side conditions. -/
theorem queries (tree : BorrowTree) (before : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree before)
    (frame : FrameState) (allocation : AllocId) (room : before.nextPointerTag.value < 18446744073709551615) :
    let after := (GeneralBorrowFnEntryRegistration.registered before frame allocation room).1.endCall
      (({} : FrameState).addProtector allocation before.nextPointerTag)
    after.protectedTags = before.protectedTags ∧
      (∀ query, after.protectedTags.get query = before.protectedTags.get query) ∧
      (∀ query, after.protectedTags.contains query = before.protectedTags.contains query) := by
  have exactGlobal := global tree before runtime frame allocation room
  dsimp only
  rw [exactGlobal]
  exact ⟨rfl,fun _=>rfl,fun _=>rfl⟩
end DuplicatePrefix.GeneralBorrowSharedFnEntryGlobalReturn
