import duplicate_prefix.GeneralBorrowFnEntryRegistration
import duplicate_prefix.TypedRetagEmpty
namespace DuplicatePrefix.GeneralBorrowFnEntryRegistrationRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open GeneralBorrowFnEntryRegistration (advanced registered)

/-- Actual global tag allocation and Strong registration preserve complete
runtime facts independently of source normal permissions or owner windows. -/
theorem prepare (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    :
    global.newPointerTag = .ok (advanced global room,global.nextPointerTag) ∧
    (registered global frame allocation room).1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
    (registered global frame allocation room).2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (registered global frame allocation room).1 ∧
    GeneralBorrowProtector.Fresh tree global.nextPointerTag ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  have complete := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,nodeFresh,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag complete (Nat.le_refl _)
  have same : ∀ index node, tree.nodeAt index = some node →
      ((registered global frame allocation room).1.protectedTags).contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags true
  have equal : advanced global room = allocated := congrArg Prod.fst (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have formed : GeneralBorrowStructuralHistorySifaState.Formed tree (registered global frame allocation room).1.protectedTags := by
    refine ⟨runtime.formed.toState,?_⟩
    intro position valid
    refine ⟨?_,(runtime.formed.profile position valid).vacant⟩
    intro index node present
    rw [same index node present]
    exact (runtime.formed.profile position valid).present index node present
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree (registered global frame allocation room).1 := by
    refine ⟨formed,?_,runtime.possible,?_⟩
    · intro position valid
      exact GeneralBorrowProtectorCacheMap.frame tree _ _ _ (runtime.coherent position valid)
        (by intro index node present exposed;exact same index node present)
    · simpa only [registered,GlobalState.addProtector,advanced,GeneralBorrowFreshSharedSequence.registered,ite_true] using below
  exact ⟨TypedRetagEmpty.allocate_tag global room,ProtectedTags.get_insert_same _ _ _,rfl,current,nodeFresh,fresh⟩
end DuplicatePrefix.GeneralBorrowFnEntryRegistrationRuntime
