import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.PositiveLenPost
import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S03SeparateReturnRegistration
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Registering the current fresh tag in another allocation leaves protector
lookups at every existing return-tree node unchanged. Freshness is derived
from the runtime high-water invariant, for concrete and wildcard sources. -/
theorem register (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum offset len) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (TypedRetagGeneric.protectedGlobal global room) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree
      (TypedRetagGeneric.protectedGlobal global room).protectedTags source selected maximum offset len) ∧
    ∀ index node, tree.nodeAt index = some node →
      (TypedRetagGeneric.protectedGlobal global room).protectedTags.get node.tag = global.protectedTags.get node.tag := by
  obtain ⟨_,_,_,current,kept,_⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare tree global {} allocation room runtime
    source selected maximum offset len positive
  obtain ⟨_,_,_,_,fresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  refine ⟨current,kept,?_⟩
  intro index node present
  have different := fresh (index,node)
    (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present))
  exact ProtectorInsertion.get_other global.protectedTags global.nextPointerTag node.tag .StrongProtector different

/-- The actual positive-count body allocates an unprotected Shared tag, then
registers and removes the len frame's fresh protector. An unrelated return
tree keeps its complete runtime and concrete/wildcard owner capability. -/
theorem len (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (first : tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker tracker first).global.nextPointerTag.value < 18446744073709551615)
    (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset count : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags source selected maximum offset count) :
    let final := PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker tracker first) second allocation
    DuplicatePrefixBorrowContract.RuntimeFacts tree final.global ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree final.global.protectedTags source selected maximum offset count) := by
  let expr := ReferenceBorrowDriver.allocatedTracker tracker first
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag first
  have raised : DuplicatePrefixBorrowContract.RuntimeFacts tree expr.global := by
    refine ⟨runtime.formed,runtime.coherent,runtime.possible,?_⟩
    apply GeneralBorrowForestTagHighWaterHistory.weaken tree tracker.global.protectedTags
      tracker.global.nextPointerTag expr.global.nextPointerTag runtime.below
    change tracker.global.nextPointerTag.value.toNat ≤ (TypedRetagEmpty.successorTag tracker.global.nextPointerTag first).value.toNat
    omega
  obtain ⟨_,_,_,registered,⟨kept⟩,_⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare tree expr.global {} allocation
    second raised source selected maximum offset count positive
  obtain ⟨_,_,_,_,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree expr.global {} allocation second raised
  let frame := ({} : FrameState).addProtector allocation expr.global.nextPointerTag
  have hidden : S04ReturnReleaseParent.HiddenFrame tree frame := by
    intro row member index node present same
    have rowEq : row = (allocation,expr.global.nextPointerTag) := by
      simpa only [frame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] using member
    subst row
    exact False.elim ((nodeFresh (index,node)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present))) same)
  exact S04ReturnReleaseParent.end_call tree
    (GeneralBorrowFnEntryRegistration.registered expr.global {} allocation second).1 frame registered hidden
    source selected maximum offset count kept

end DuplicatePrefix.S03SeparateReturnRegistration
