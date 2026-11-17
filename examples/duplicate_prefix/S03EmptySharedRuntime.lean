import duplicate_prefix.S03EmptySharedFrame
import duplicate_prefix.GeneralBorrowConstructorPossible
import duplicate_prefix.GeneralBorrowZeroSharedExposureCache
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
import duplicate_prefix.GeneralBorrowFnEntryRegistration

namespace DuplicatePrefix.S03EmptySharedRuntime
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- The two real empty Shared constructors in the positive-count branch retain
complete runtime facts. Their empty inside maps impose no offset bound. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.after global := by
  have bounded : GeneralBorrowStructuralHistoryMixedConcrete.Bounded
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) (Size.ofBytes 0) tree.locations.size := by
    intro segment member
    simp [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes] at member
  have structural := GeneralBorrowStructuralHistoryMixedConcrete.preserves tree runtime.formed.toState
    parentTag input.parent input.parentNode input.tagged input.present tag input.fresh room
    .Frozen .Read false rfl rfl rfl (Size.ofBytes 0)
    (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) bounded
  rw [input.child 0 false] at structural
  have profile : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.after location global.protectedTags) input.after.locations := by
    apply GeneralBorrowSifaProfileTransport.sifa input.stage global.protectedTags input.parent .Read
    intro position valid
    have consistent := GeneralBorrowSifaPermissionConsistency.frozen false (global.protectedTags.contains tag)
    have attached := GeneralBorrowConstructorSifaProfile.attach tree (input.stage.locations.entries[position].data)
      global.protectedTags input.index input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode tag input.parent)
      input.vacant input.present (runtime.formed.profile position valid) consistent
    exact ⟨attached.present,attached.vacant⟩

  have possible : Every (GeneralBorrowSnapshotReadRuntime.GlobalPossible input.after) input.after.locations := by
    apply GeneralBorrowConstructorPossible.sifa input.stage input.parent .Read
    intro position valid
    exact GeneralBorrowConstructorPossible.attach tree _ global.protectedTags input.index input.parent input.parentNode tag
      input.vacant input.present (runtime.formed.profile position valid) (runtime.possible position valid)
  have coherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent input.after location global.protectedTags) input.after.locations := by
    have actual : ∀ offset : UInt64,
        Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent
          (tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
            (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen false).tree location global.protectedTags)
          (tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
            (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen false).tree.locations := by
      intro offset
      cases chosen : input.slot with
      | append noFree aligned fits =>
        exact (GeneralBorrowZeroSharedExposureCache.append tree input.depth parentTag tag input.parent input.parentNode
          input.tagged input.present input.fresh noFree aligned fits offset false global.protectedTags runtime.coherent).2
      | reuse index available valid vacant slack =>
        exact (GeneralBorrowZeroSharedExposureCache.reuse tree input.depth parentTag tag input.parent index input.parentNode
          input.tagged input.present input.fresh available valid vacant slack offset false global.protectedTags runtime.coherent).2
    have atZero := actual 0
    rw [input.child 0 false] at atZero
    exact atZero
  refine ⟨⟨structural.1,profile⟩,coherent,possible,?_⟩
  refine ⟨?_,runtime.below.protectors⟩
  intro row member
  change row ∈ input.after.tagMapping.mapping at member
  rw [input.mapping_after] at member
  rcases Array.mem_push.mp member with old | added
  · exact runtime.below.mapping row old
  · cases added
    exact tagBound

/-- Actual unprotected Shared-expression tag allocation followed by its empty
constructor preserves the caller facts needed by the subsequent len call. -/
theorem allocate_construct (tree : BorrowTree) (global : GlobalState)
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
    let advanced := GeneralBorrowFnEntryRegistration.advanced global tagRoom
    global.newPointerTag = .ok (advanced,global.nextPointerTag) ∧
    tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen false = ⟨input.after,.ok ()⟩ ∧
    DuplicatePrefixBorrowContract.RuntimeFacts input.after advanced ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after advanced.protectedTags source selected maximum ownerOffset ownerLen) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin input.after observer .Write ownerOffset (ownerOffset+ownerLen) ∧
    S04ReturnReleaseInactive.Quiescent input.after zero := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global tagRoom
  have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have raised : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,
      GeneralBorrowForestTagHighWaterHistory.weaken tree global.protectedTags global.nextPointerTag advanced.nextPointerTag
        runtime.below (Nat.le_of_lt tagBound)⟩
  have afterRuntime := construct tree advanced raised parentTag global.nextPointerTag input room tagBound
  obtain ⟨child,kept,activity,quiescent⟩ := S03EmptySharedFrame.construct tree global runtime parentTag global.nextPointerTag input
    offset false source selected maximum ownerOffset ownerLen positive observer active zero quiet
  exact ⟨TypedRetagEmpty.allocate_tag global tagRoom,child,afterRuntime,kept,activity,quiescent⟩

end DuplicatePrefix.S03EmptySharedRuntime
