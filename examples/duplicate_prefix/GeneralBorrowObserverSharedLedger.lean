import duplicate_prefix.GeneralBorrowObserverReadRestore
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
namespace DuplicatePrefix.GeneralBorrowObserverSharedLedger
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowObserverReadRow (virtual)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real insert/remove of one protector retains precisely the original entries
other than that tag, including the physical table order. -/
theorem remove_insert (tags : ProtectedTags) (tag : BorTag) (kind : ProtectorKind) :
    (tags.insert tag kind).remove tag = tags.remove tag := by
  cases tags
  simp [ProtectedTags.insert,ProtectedTags.remove,Array.filter_push,Array.filter_filter,Bool.and_self]

/-- The original table is exactly the virtual ledger of the fresh protected
shared helper and its unprotected source temporary. Both absence conditions
are call-entry facts about this actual fresh registration. -/
theorem registered_virtual (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615) (temporaryTag : BorTag)
    (freshUnprotected : global.protectedTags.contains global.nextPointerTag = false)
    (temporaryUnprotected : global.protectedTags.contains temporaryTag = false) :
    virtual (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1
      allocation global.nextPointerTag temporaryTag = global.protectedTags := by
  simp only [virtual,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
    GlobalState.addProtector,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rw [remove_insert,GeneralBorrowObserverReadRestore.remove_absent _ _ freshUnprotected,
    GeneralBorrowObserverReadRestore.remove_absent _ _ temporaryUnprotected]

/-- Raw runtime high-water data derives freshness for the newly allocated tag;
no future global/operation outcome or unprotection assumption is supplied. -/
theorem registered_virtual_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (frame : FrameState) (allocation : AllocId) (room : global.nextPointerTag.value < 18446744073709551615)
    (temporaryTag : BorTag) (temporaryUnprotected : global.protectedTags.contains temporaryTag = false) :
    virtual (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1
      allocation global.nextPointerTag temporaryTag = global.protectedTags := by
  have complete := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unprotected⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag complete (Nat.le_refl _)
  exact registered_virtual global frame allocation room temporaryTag unprotected temporaryUnprotected
end DuplicatePrefix.GeneralBorrowObserverSharedLedger
