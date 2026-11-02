import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultCallbacks
import duplicate_prefix.GeneralBorrowFreshRootScopedProtectedCallbacks
import duplicate_prefix.GeneralBorrowDefaultChildPositive
import duplicate_prefix.GeneralBorrowProtectedChildPositive
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedChildPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
theorem default (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat) (unprotected : global.protectedTags.contains newTag = false)
    (selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags child selected maximum offset len) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨basePositive⟩⟩ :=
    GeneralBorrowDefaultChildPositive.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unprotected
      selected (some maximum) offset len positive.base
  obtain ⟨callbackDone,callbackRuntime,callbackCapacity,callbackGrowth,callbackChild,callbackLookup,callbackRoots,callbackRows⟩ :=
    GeneralBorrowFreshRootScopedDefaultCallbacks.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unprotected
      selected maximum offset len positive
  have same : callbackChild = child := Option.some.inj (callbackLookup.symm.trans lookup)
  subst callbackChild
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨⟨basePositive,?_⟩⟩⟩
  intro position valid nonzero start stop
  obtain ⟨baseRow⟩ := basePositive.rows position valid nonzero start stop
  obtain ⟨exposed,callbacks⟩ := callbackRows position valid nonzero start stop
  exact ⟨⟨baseRow,exposed,callbacks⟩⟩

theorem protected_mutable (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat) (heldTag : global.protectedTags.contains newTag = true)
    (selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags child selected maximum offset len) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨basePositive⟩⟩ :=
    GeneralBorrowProtectedChildPositive.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound heldTag
      selected (some maximum) offset len positive.base
  obtain ⟨callbackDone,callbackRuntime,callbackCapacity,callbackGrowth,callbackChild,callbackLookup,callbackRoots,callbackRows⟩ :=
    GeneralBorrowFreshRootScopedProtectedCallbacks.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound heldTag
      selected maximum offset len positive
  have same : callbackChild = child := Option.some.inj (callbackLookup.symm.trans lookup)
  subst callbackChild
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨⟨basePositive,?_⟩⟩⟩
  intro position valid nonzero start stop
  obtain ⟨baseRow⟩ := basePositive.rows position valid nonzero start stop
  obtain ⟨exposed,callbacks⟩ := callbackRows position valid nonzero start stop
  exact ⟨⟨baseRow,exposed,callbacks⟩⟩

end DuplicatePrefix.GeneralBorrowFreshRootScopedChildPositive
