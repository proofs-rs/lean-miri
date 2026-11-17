import duplicate_prefix.GeneralBorrowProtectedCallbacksConstructor
import duplicate_prefix.GeneralBorrowProtectedCapabilityConstructor

namespace DuplicatePrefix.GeneralBorrowProtectedCallbacksCapabilities
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual protected mutable constructor creates child Read+Write Normal
and preserves both other-root callback kinds on the same owner window, with
arbitrary coherent append/reuse pools. Ancestor SIFA is actually None. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodes.get parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (heldTag : global.protectedTags.contains newTag = true)
    (selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some parent) (some selected) maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child,actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      OwnedOn (fun location => GeneralBorrowProtectedCapabilityRange.Child actual.tree global.protectedTags parent child location ∧
        Callbacks actual.tree global.protectedTags selected maximum location) offset (offset+len) actual.tree.locations := by
  have callbacks := GeneralBorrowProtectedCallbacksConstructor.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound heldTag selected maximum offset len positive
  have normal : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags parent))
      offset (offset+len) tree.locations := by
    intro position valid positiveWindow start stop
    obtain ⟨row⟩ := positive.rows position valid positiveWindow start stop
    exact row.normal parent rfl
  have nonzero : len ≠ 0 := by intro zero;have p := positive.positive;rw [zero] at p;contradiction
  have capabilities := GeneralBorrowProtectedCapabilityConstructor.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound heldTag offset len nonzero positive.bounds normal
  refine ⟨callbacks.1,callbacks.2.1,callbacks.2.2.1,callbacks.2.2.2.1,?_⟩
  obtain ⟨child,lookup,roots,allCallbacks⟩ := callbacks.2.2.2.2
  obtain ⟨otherChild,otherLookup,both⟩ := capabilities.2.2.2.2
  have equal : otherChild = child := Option.some.inj (otherLookup.symm.trans lookup)
  subst otherChild
  refine ⟨child,lookup,roots,?_⟩
  intro position valid positiveWindow start stop
  exact ⟨both position valid positiveWindow start stop,allCallbacks position valid positiveWindow start stop⟩

end DuplicatePrefix.GeneralBorrowProtectedCallbacksCapabilities
