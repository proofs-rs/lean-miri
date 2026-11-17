import duplicate_prefix.S03EmptySharedRuntime
import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration
import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens

namespace DuplicatePrefix.S03EmptyLenBorrow
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- The exact borrowing part of the real zero-length len call: allocate,
Strong-register, construct the empty shared argument, release it, and endCall.
The parent's existing return window and original empty-tag state survive. -/
theorem with_input (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen)
    (observer : UniIndex)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write ownerOffset (ownerOffset+ownerLen))
    (zero : UniIndex) (quiet : S04ReturnReleaseInactive.Quiescent tree zero) :
    let entryGlobal := (registered global {} allocation tagRoom).1
      let afterGlobal := entryGlobal.endCall (({} : FrameState).addProtector allocation global.nextPointerTag)
      global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen true = ⟨input.after,.ok ()⟩ ∧
      input.after.releaseProtector global.nextPointerTag entryGlobal.protectedTags = ⟨input.after,.Released⟩ ∧
      DuplicatePrefixBorrowContract.RuntimeFacts input.after afterGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after afterGlobal.protectedTags source selected maximum ownerOffset ownerLen) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin input.after observer .Write ownerOffset (ownerOffset+ownerLen) ∧
      S04ReturnReleaseInactive.Quiescent input.after zero := by
  obtain ⟨allocated,held,owned,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global {} allocation tagRoom runtime
      source selected maximum ownerOffset ownerLen positive
  let entryGlobal := (registered global {} allocation tagRoom).1
  have tagBound : global.nextPointerTag.value.toNat < entryGlobal.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have afterRuntime := S03EmptySharedRuntime.construct tree entryGlobal registeredRuntime parentTag global.nextPointerTag input room tagBound
  obtain ⟨childEq,⟨childPositive⟩,childActive,childQuiet⟩ := S03EmptySharedFrame.construct tree entryGlobal registeredRuntime
    parentTag global.nextPointerTag input offset true source selected maximum ownerOffset ownerLen registeredPositive observer active zero quiet
  have stagePresent : input.stage.nodeAt input.index =
      some (GeneralBorrowFreshAnchor.sharedNode global.nextPointerTag input.parent) := by
    exact S04ZeroReadSharedAttach.fresh_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode global.nextPointerTag input.parent) input.vacant input.present
  obtain ⟨node,lookup,sameTag,parents,children,permission,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read input.index
    (GeneralBorrowFreshAnchor.sharedNode global.nextPointerTag input.parent) stagePresent
  have newPresent : input.after.nodeAt input.index = some node := lookup
  have newTag : node.tag = global.nextPointerTag := sameTag
  have newHidden : node.isExposed = false := hidden
  let afterGlobal := entryGlobal.endCall (({} : FrameState).addProtector allocation global.nextPointerTag)
  obtain ⟨finalRuntime,unheld,other⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call input.after entryGlobal afterRuntime
    allocation global.nextPointerTag input.index node newPresent newTag newHidden
  have sameExposed : ∀ index value, input.after.nodeAt index = some value → value.isExposed = true →
      afterGlobal.protectedTags.contains value.tag = entryGlobal.protectedTags.contains value.tag := by
    intro index value found exposed
    have different : value.tag ≠ global.nextPointerTag := by
      intro eq
      have first := afterRuntime.formed.allocator.nodeTags index value found
      have second := afterRuntime.formed.allocator.nodeTags input.index node newPresent
      have sameTags : value.tag = node.tag := eq.trans newTag.symm
      rw [sameTags] at first
      have indices := Option.some.inj (first.symm.trans second)
      subst index
      have nodes := Option.some.inj (found.symm.trans newPresent)
      subst value
      rw [newHidden] at exposed
      contradiction
    unfold ProtectedTags.contains
    rw [other value.tag different]
  have finalPositive := GeneralBorrowHiddenProtectorRowWeakens.positive input.after entryGlobal.protectedTags afterGlobal.protectedTags
    (GeneralBorrowRelease.end_call_weakens entryGlobal _) sameExposed source selected maximum ownerOffset ownerLen childPositive
  exact ⟨allocated,childEq,input.release entryGlobal.protectedTags,finalRuntime,finalPositive,childActive,childQuiet⟩

end DuplicatePrefix.S03EmptyLenBorrow
