import duplicate_prefix.GeneralBorrowFreshRootScopedReadRow
import duplicate_prefix.GeneralBorrowFreshRootScopedSourceSharedConstructor
import duplicate_prefix.GeneralBorrowSharedReadPositive
import duplicate_prefix.GeneralBorrowSharedParentPositive
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
theorem shared_read (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains newTag = held)
    (selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedReadRow.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child,actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive actual.tree global.protectedTags parent selected maximum offset len) ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive actual.tree global.protectedTags child selected maximum offset len) := by
  have nonzero : len ≠ 0 := by intro zero;have p := positive.base.positive;rw [zero] at p;contradiction
  have sources : OwnedOn (fun location => Nonempty (GeneralBorrowFreshRootScopedSource.Source tree location global.protectedTags parent selected maximum))
      offset (offset+len) tree.locations := by
    intro position valid nonempty start stop
    obtain ⟨row⟩ := positive.rows position valid nonempty start stop
    exact ⟨GeneralBorrowFreshRootScopedReadRow.source tree _ global.protectedTags parent selected maximum row⟩
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨parentBase⟩,⟨childBase⟩⟩ :=
    GeneralBorrowSharedReadPositive.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound held aligned
      selected (some maximum) offset len positive.base
  obtain ⟨callbackDone,callbackRuntime,callbackCapacity,callbackGrowth,callbackChild,callbackLookup,callbackRoots,callbackRows⟩ :=
    GeneralBorrowFreshRootScopedSourceSharedConstructor.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room
      tagBound held aligned selected maximum offset len nonzero positive.base.bounds sources
  have same : callbackChild = child := Option.some.inj (callbackLookup.symm.trans lookup)
  subst callbackChild
  let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
  have parentRows : GeneralBorrowFreshRootScopedReadRow.Positive actual.tree global.protectedTags parent selected maximum offset len := by
    refine ⟨parentBase,?_⟩
    intro position valid nonempty start stop
    obtain ⟨base⟩ := parentBase.rows position valid nonempty start stop
    obtain ⟨exposed,callbacks⟩ := callbackRows position valid nonempty start stop
    exact ⟨⟨base,exposed,callbacks⟩⟩
  have childRows : GeneralBorrowFreshRootScopedReadRow.Positive actual.tree global.protectedTags child selected maximum offset len := by
    refine ⟨childBase,?_⟩
    intro position valid nonempty start stop
    obtain ⟨base⟩ := childBase.rows position valid nonempty start stop
    obtain ⟨exposed,callbacks⟩ := callbackRows position valid nonempty start stop
    exact ⟨⟨base,exposed,callbacks⟩⟩
  exact ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨parentRows⟩,⟨childRows⟩⟩

theorem shared_parent (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat) (unprotected : global.protectedTags.contains newTag = false)
    (selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags parent selected maximum offset len) := by
  obtain ⟨initialRead⟩ := GeneralBorrowFreshRootScopedReadRow.of_positive tree global.protectedTags parent selected maximum offset len positive
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨parentRead⟩,childRead⟩ :=
    shared_read tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound false unprotected selected maximum offset len initialRead
  obtain ⟨baseDone,baseRuntime,baseCapacity,baseGrowth,baseChild,baseLookup,baseRoots,⟨parentBase⟩⟩ :=
    GeneralBorrowSharedParentPositive.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unprotected
      selected (some maximum) offset len positive.base
  have same : baseChild = child := Option.some.inj (baseLookup.symm.trans lookup)
  subst baseChild
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨⟨parentBase,?_⟩⟩⟩
  intro position valid nonempty start stop
  obtain ⟨base⟩ := parentBase.rows position valid nonempty start stop
  obtain ⟨row⟩ := parentRead.rows position valid nonempty start stop
  exact ⟨⟨base,row.exposed,row.callbacks⟩⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedPositive
