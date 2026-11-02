import duplicate_prefix.S02WildcardSameDestinationRootPositive
import duplicate_prefix.S02WildcardSameDestinationRead
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources
namespace DuplicatePrefix.S02WildcardSameDestinationRootOperation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Real wildcard FnEntry registration, ranged Read and fresh-root construction
preserve a disjoint old return owner and all old node/tag metadata. -/
theorem operation_destination (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64) (positive : Positive tree global.protectedTags none none none offset len)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (destination : Positive tree global.protectedTags source selected maximum lower width) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset len = .ok output ∧
      Nonempty (Positive output.child.tree output.global.protectedTags source selected maximum lower width) ∧
      output.child.tree.locations.size = tree.locations.size ∧
      (∀ query node,tree.nodeAt query = some node → output.child.tree.nodeAt query = some node) ∧
      (∀ tag query,tree.indexOfTag tag = some query → output.child.tree.indexOfTag tag = some query) := by
  obtain ⟨allocated,_held,_frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime none none none offset len positive
  obtain ⟨_allocated,_held2,_frameEq2,_runtime,⟨registeredDestination⟩,_fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime source selected maximum lower width destination
  let registration := registered global frame allocation tagRoom
  let read := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterDestination⟩⟩ := S02WildcardSameDestinationRead.positive tree registration.1 registeredRuntime offset len registeredPositive distinct short
    source selected maximum lower width outside registeredDestination
  have afterPositive : Positive read.tree registration.1.protectedTags none none none offset len := by
    refine ⟨positive.positive,?_,?_,?_,contract.rows⟩
    · rw [contract.capacity];exact positive.bounds
    · intro anchor impossible;cases impossible
    · intro _;rw [contract.roots];exact positive.wildcardRoot rfl
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact nodeRoom
  obtain ⟨childDone,childPositive,capacity,oldNodes,oldTags⟩ := S02WildcardSameDestinationRootPositive.construct read.tree registration.1 afterRuntime global.nextPointerTag
    freshAfter room offset len afterPositive source selected maximum lower width outside afterDestination
  let child := read.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,read,child⟩
  refine ⟨output,?_,childPositive,capacity.trans contract.capacity,?_,?_⟩
  · simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · intro query node present
    apply oldNodes query node
    change read.tree.nodes.get query = some node
    rw [contract.nodes]
    exact present
  · intro tag query tagged
    apply oldTags tag query
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact tagged
end DuplicatePrefix.S02WildcardSameDestinationRootOperation
