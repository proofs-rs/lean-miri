import duplicate_prefix.S03EmptyTagState
import duplicate_prefix.S04ZeroFnEntryObserver
import duplicate_prefix.S04ZeroWildcardFnEntryObserver
import duplicate_prefix.S04ZeroConcreteRuntime

namespace DuplicatePrefix.S03EmptyFnEntryFacts
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration S03EmptyTagState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- Literal zero protected construction produces a hidden, inactive leaf in
both actual allocator branches; inactivity is obtained from runtime Clean. -/
noncomputable def concrete_data (tree : BorrowTree) (parentTag tag : BorTag)
    (input : ConcreteEmptyPoolEntry.Input tree parentTag tag) : Data input.after tag input.index := by
  let facts := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .None input.index (GeneralBorrowFreshChild.child tag input.parent) input.stage_new
  let node := Classical.choose facts
  obtain ⟨present,same,parent,children,permission,hidden⟩ := Classical.choose_spec facts
  refine ⟨node,?_,present,same,children,hidden,?_⟩
  · unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index input.free
  · exact clean input.after input.index (input.future_clean input.index input.clean)

noncomputable def wildcard_data (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (vacantClean : GeneralBorrowGcVacantClean.VacantClean tree) : Data (slot.after tag) tag slot.index := by
  refine ⟨WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None,?_,?_,rfl,rfl,rfl,?_⟩
  · exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh slot.index slot.free
  · exact GeneralBorrowFreshLocation.get_same tree.nodes slot.index _
  · exact clean (slot.after tag) slot.index (vacantClean slot.index slot.vacant)

/-- The same real allocation/Strong registration/zero FnEntry constructor
that preserves the return observer also produces its actual zero-tag data. -/
theorem concrete_registered (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (short : tree.nodes.size < 65536) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag) (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) ∧
      ∃ index, Nonempty (Data result.tree global.nextPointerTag index) ∧
        ∀ anchor, source = some anchor → index ≠ anchor := by
  obtain ⟨allocated,held,owned,done,kept⟩ := S04ZeroFnEntryObserver.register_construct tree global frame allocation runtime
    parentTag parent parentNode tagged present short tagRoom offset source selected maximum ownerOffset ownerLen positive
  obtain ⟨_,_,_,nextRuntime,_,fresh⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime
    source selected maximum ownerOffset ownerLen positive
  have accounting := nextRuntime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by unfold GeneralBorrowFreshStagePool.Accounting at accounting;omega
  let input := ConcreteEmptyPoolEntry.factory tree parentTag global.nextPointerTag parent parentNode
    (Classical.choice nextRuntime.formed.depth) tagged present fresh nextRuntime.formed.allocator.pool accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean nextRuntime)
  refine ⟨allocated,held,owned,done,kept,input.index,?_,?_⟩
  · rw [input.child offset]
    exact ⟨concrete_data tree parentTag global.nextPointerTag input⟩
  · intro anchor sourceEq same
    obtain ⟨node,present⟩ := positive.sourcePresent anchor sourceEq
    rw [←same,show tree.nodeAt input.index = none from input.vacant] at present
    cases present

/-- Concrete zero FnEntry forms runtime, the return observer and zero-tag
metadata on the same actual constructor result, with no offset bound. -/
theorem concrete_complete (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (short : tree.nodes.size < 65536) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag) (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree registration.1 ∧
      ∃ index, Nonempty (Data result.tree global.nextPointerTag index) ∧
        ∀ anchor, source = some anchor → index ≠ anchor := by
  obtain ⟨allocated,held,owned,done,kept,index,data,different⟩ := concrete_registered tree global frame allocation runtime
    parentTag parent parentNode tagged present short tagRoom offset source selected maximum ownerOffset ownerLen positive
  obtain ⟨_,_,_,registeredRuntime,_,fresh⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime
    source selected maximum ownerOffset ownerLen positive
  have bound : global.nextPointerTag.value.toNat < (registered global frame allocation tagRoom).1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have isHeld : (registered global frame allocation tagRoom).1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have full := S04ZeroConcreteRuntime.construct tree (registered global frame allocation tagRoom).1 registeredRuntime
    parentTag parent parentNode tagged present global.nextPointerTag fresh (by omega) bound isHeld offset
  exact ⟨allocated,held,owned,done,kept,full.2.1,index,data,different⟩

/-- Wildcard zero FnEntry produces the same hidden inactive data on its actual
new root, together with full runtime and the preserved return observer. -/
theorem wildcard_registered (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (short : tree.nodes.size < 65536) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag) (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree registration.1 ∧
      ∃ index, Nonempty (Data result.tree global.nextPointerTag index) ∧
        ∀ anchor, source = some anchor → index ≠ anchor := by
  obtain ⟨allocated,held,owned,done,kept,afterRuntime,_,_⟩ := S04ZeroWildcardFnEntryObserver.complete tree global frame allocation runtime
    short tagRoom offset source selected maximum ownerOffset ownerLen positive
  obtain ⟨_,_,_,nextRuntime,_,fresh⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime
    source selected maximum ownerOffset ownerLen positive
  have accounting := nextRuntime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by unfold GeneralBorrowFreshStagePool.Accounting at accounting;omega
  let slot := WildcardHitPoolRoot.factory tree nextRuntime.formed.allocator.pool accounting fits
  refine ⟨allocated,held,owned,done,kept,afterRuntime,slot.index,?_,?_⟩
  · rw [slot.child global.nextPointerTag fresh offset]
    exact ⟨wildcard_data tree slot global.nextPointerTag fresh (DuplicatePrefixBorrowContract.vacant_clean nextRuntime)⟩
  · intro anchor sourceEq same
    obtain ⟨node,present⟩ := positive.sourcePresent anchor sourceEq
    rw [←same,show tree.nodeAt slot.index = none from slot.vacant] at present
    cases present

end DuplicatePrefix.S03EmptyFnEntryFacts
