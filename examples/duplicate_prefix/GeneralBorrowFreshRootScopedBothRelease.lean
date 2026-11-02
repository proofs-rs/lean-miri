import duplicate_prefix.GeneralBorrowBothReleaseCore
import duplicate_prefix.GeneralBorrowFreshRootScopedRange
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedBothRelease
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Full actual unexposed mutable-helper release, with arbitrary roots, initial
outside-source activity, allocator pools and exposed caches. The fresh child's
own activity window bounds the real scan's accessed rows. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags anchor selected maximum offset len)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode) (hidden : anchorNode.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags anchor selected maximum offset len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree anchor .Write offset (offset+len) ∧
    actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.base.bounds tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have nonempty : offset.toNat < (offset+len).toNat := by rw [sum];have p:=positive.base.positive;omega
  have runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  obtain ⟨done,frame,rows,allRuntime,activity,well,capacity⟩ := GeneralBorrowBothReleaseCore.release tree global.protectedTags
    tag anchor offset (offset+len) nonempty anchorNode present hidden tagged
    (fun current location => GeneralBorrowFreshRootScopedRange.Row current global.protectedTags anchor selected maximum location)
    (fun map location row => GeneralBorrowFreshRootScopedRange.row_locations tree map location global.protectedTags anchor selected maximum row)
    (fun location row currentRuntime kind range =>
      let done := GeneralBorrowFreshRootScopedRange.location_kind tree global.protectedTags before.formed.toGraphState anchor selected anchorNode present
        maximum kind location row distinct currentRuntime short .SkipChildrenOfAccessed range
      ⟨done.1,done.2.1,done.2.2.1⟩)
    active before.formed.well runtime positive.rows
  let actual := tree.releaseProtector tag global.protectedTags
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree actual.tree.locations before.formed.toGraphState
  rw [←frame] at graph
  have finalRuntime : DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global := by
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,?_⟩
    · intro position valid;exact (allRuntime position valid).profile
    · intro position valid;exact (allRuntime position valid).coherent
    · intro position valid;exact (allRuntime position valid).possible
    · have tags := congrArg BorrowTree.tagMapping frame
      refine ⟨?_,before.below.protectors⟩
      rw [tags]
      exact before.below.mapping
  have baseRows : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowConcreteRowReadRange.Row actual.tree global.protectedTags anchor selected (some maximum)) offset (offset+len) actual.tree.locations := by
    intro position valid nonempty start stop
    obtain ⟨row⟩ := rows position valid nonempty start stop
    exact ⟨row.base⟩
  refine ⟨done,finalRuntime,⟨⟨⟨positive.base.positive,?_,?_,(by intro impossible;cases impossible),baseRows⟩,rows⟩⟩,activity,frame,capacity⟩
  · rw [capacity];exact positive.base.bounds
  · intro source same
    have equal : source = anchor := Option.some.inj same.symm
    subst source
    refine ⟨anchorNode,?_⟩
    have nodes := congrArg BorrowTree.nodes frame
    change actual.tree.nodes.get anchor = some anchorNode
    rw [nodes]
    exact present
end DuplicatePrefix.GeneralBorrowFreshRootScopedBothRelease
