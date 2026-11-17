import duplicate_prefix.GeneralBorrowFnEntryRegistration
namespace DuplicatePrefix.GeneralBorrowDefaultTagAllocation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration (advanced)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Literal fresh tag allocation without protector registration. Membership at
all old nodes, initial Positive and runtime are retained; fresh/unheld follow
from the initial high-water bound. -/
theorem prepare (tree : BorrowTree) (global : GlobalState)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some anchor) (some selected) maximum offset len) :
    global.newPointerTag = .ok (advanced global room,global.nextPointerTag) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (advanced global room) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree (advanced global room).protectedTags
      (some anchor) (some selected) maximum offset len) ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag ∧
    global.protectedTags.contains global.nextPointerTag = false := by
  have complete := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,nodeFresh,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag complete (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced global room = allocated := congrArg Prod.fst (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree (advanced global room) :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced] using below⟩
  refine ⟨TypedRetagEmpty.allocate_tag global room,afterRuntime,⟨positive⟩,fresh,?_⟩
  exact unheld
end DuplicatePrefix.GeneralBorrowDefaultTagAllocation
