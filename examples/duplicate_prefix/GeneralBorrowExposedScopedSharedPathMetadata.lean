import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafNext
import duplicate_prefix.GeneralBorrowExposedScopedSharedUniqueWriteRestore
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedPathMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def child (input : Input) (protections : ProtectedTags) (mode : ChildrenVisitMode) : BorrowTree :=
  ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode).tree.newChild
    (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree

/-- Exact source Read→shared child forms production full ancestor paths,
including the increased traversal fuel, from initial leaf/component metadata. -/
theorem attach (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources input protections selected head tail writable)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) (mode : ChildrenVisitMode)
    (oldLocation newLocation : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection input.tree oldLocation tags).topology
      (source_normal_projection (child input protections mode) newLocation tags).topology input.parent.toNat (index input).toNat := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedSharedLeafRun.prepare input protections selected head tail writable raw atBase full mode
  have frame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
  have endIndex:=at_end prepared
  have projectedSize : (source_normal_projection prepared.tree oldLocation tags).topology.nodes.size=(index prepared).toNat := by
    rw [endIndex]
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have extension:=(append prepared).extension oldLocation newLocation tags
  have forest : GeneralBorrowForest.Forest (source_normal_projection prepared.tree oldLocation tags).topology := by
    have same : (source_normal_projection prepared.tree oldLocation tags).topology=(source_normal_projection prepared.tree default protections).topology := by
      unfold_general_projection
      rfl
    rw [same]
    exact preparedRaw.forest
  have data:=GeneralBorrowFreshSharedPaths.of_append _ _ prepared.parent.toNat extension forest
  rw [projectedSize] at data
  have childEq : result prepared=child input protections mode := by
    simp only [result,child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  rw [childEq,parentEq,indexEq,treeEq,frame] at data
  exact data
/-- Two real scoped shared stages form exactly the expression/helper prefix
required by target restoration; no full-prefix shape is supplied by callers. -/
theorem two_step (first second : Input) (firstTags secondTags : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex) (writable : Nat → Bool)
    (firstRaw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources first firstTags selected head tail writable)
    (secondRaw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources second secondTags selected head tail
      (GeneralBorrowFreshMixedChild.extend writable (index first).toNat))
    (firstAtBase : first.offset=0) (firstFull : first.len=first.tree.locations.size.bytes)
    (secondAtBase : second.offset=0) (secondFull : second.len=second.tree.locations.size.bytes)
    (firstMode secondMode : ChildrenVisitMode)
    (treeEq : second.tree=child first firstTags firstMode) (parentEq : second.parent=index first)
    (tags : ProtectedTags) (location : LocationTree) :
    (source_normal_projection (child second secondTags secondMode) location tags).topology.ancestorPath (index second).toNat=
      (index second).toNat::(index first).toNat::(source_normal_projection (child second secondTags secondMode) location tags).topology.ancestorPath first.parent.toNat ∧
    (index first).toNat∉(source_normal_projection (child second secondTags secondMode) location tags).topology.ancestorPath first.parent.toNat ∧
    (index second).toNat∉(source_normal_projection (child second secondTags secondMode) location tags).topology.ancestorPath first.parent.toNat := by
  have one:=attach first firstTags selected head tail writable firstRaw firstAtBase firstFull firstMode location location tags
  have two:=attach second secondTags selected head tail _ secondRaw secondAtBase secondFull secondMode location location tags
  rw [treeEq,parentEq] at two
  exact GeneralBorrowFreshSharedPaths.two_step _ _ _ first.parent.toNat (index first).toNat (index second).toNat one two

end DuplicatePrefix.GeneralBorrowExposedScopedSharedPathMetadata
