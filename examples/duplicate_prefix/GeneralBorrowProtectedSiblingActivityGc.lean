import duplicate_prefix.GeneralBorrowProtectedSiblingActivityMerge
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.GeneralBorrowGcFullClean
import duplicate_prefix.GeneralBorrowGcLiveRetained
import duplicate_prefix.GeneralBorrowGcFrameProvenanceStack
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingActivityGc
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem modify_all (tree : BorrowTree) (update : ByteRange → LocationTree → LocationTree)
    (query : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (frame : ∀ range location state,(update range location).perms.get query = some state → location.perms.get query = some state)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin {tree with locations := tree.locations.modifyAll update} query ownerKind lower upper := by
  intro point location atPoint state stored accessed kind associated
  obtain ⟨position,valid,startPoint,pointStop,equal⟩ := atPoint
  have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  change (tree.locations.modifyAll update).entries[position].data = location at equal
  simp only [DedupRangeMap.modifyAll,Array.getElem_map] at equal startPoint pointStop
  rw [←equal] at stored
  have oldStored := frame tree.locations.entries[position].range tree.locations.entries[position].data state stored
  exact active point tree.locations.entries[position].data ⟨position,previous,startPoint,pointStop,rfl⟩ state oldStored accessed kind associated

theorem remove (tree : BorrowTree) (index query : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin (source_remove_useless_node tree index).1 query ownerKind lower upper := by
  cases present : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [present,Id.run,bind,pure] using active
  | some node =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,bind,pure]
    apply modify_all tree _ query ownerKind lower upper _ active
    intro range location state stored
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at stored
      cases stored
    · rw [GeneralBorrowSparseRemoval.remove_get_other _ index query same] at stored
      exact stored

theorem trim (tree : BorrowTree) (query : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} query ownerKind lower upper := by
  apply modify_all tree _ query ownerKind lower upper _ active
  intro range location state stored
  rw [GeneralBorrowGcRangeClean.trim_location_get] at stored
  exact stored

theorem merge (tree : BorrowTree) (query : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin {tree with locations := tree.locations.mergeAdjacentThorough.state} query ownerKind lower upper :=
  refines tree.locations tree.locations.mergeAdjacentThorough.state (GeneralBorrowProtectedSiblingActivityMerge.refines tree.locations) query ownerKind lower upper active

/-- Real GC preserves strict activity bounds through node removals, parent and
child rewrites, location trimming and thorough merging, even on error prefixes.
This is data preservation, not a claim that erroneous collection succeeds. -/
theorem collect (tree : BorrowTree) (live : Array BorTag) (query : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree query ownerKind lower upper) :
    ActiveWithin (tree.removeUnreachableTags live).tree query ownerKind lower upper := by
  apply GeneralBorrowGcRootInvariant.preserves (fun tree => ActiveWithin tree query ownerKind lower upper) tree live active
  · intro current root good
    exact GeneralBorrowGcWhileInvariant.preserves (fun tree => ActiveWithin tree query ownerKind lower upper)
      (fun current index good => remove current index query ownerKind lower upper good)
      (fun current index oldNode newNode present tagged good => good) current root live good
  · intro current good
    exact merge _ query ownerKind lower upper (trim current query ownerKind lower upper good)

/-- Actual eligibility guards retain the same live-tagged child index and tag
while its strict activity window survives the entire real collector. -/
theorem retained (tree : BorrowTree) (live : Array BorTag) (query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get query = some node) (held : live.contains node.tag = true)
    (ownerKind : AccessKind) (lower upper : UInt64) (active : ActiveWithin tree query ownerKind lower upper) :
    ∃ next,(tree.removeUnreachableTags live).tree.nodes.get query = some next ∧ next.tag = node.tag ∧
      ActiveWithin (tree.removeUnreachableTags live).tree query ownerKind lower upper := by
  obtain ⟨next,found,tagged⟩ := GeneralBorrowGcLiveRetained.collect tree live query node present held
  exact ⟨next,found,tagged,collect tree live query ownerKind lower upper active⟩

/-- The real active-stack root visitor supplies liveness from a frame-owned
protector; no successful root collection or post-GC retained-node premise is
provided. The actual tree collector then retains that same child and activity. -/
theorem stack_protector (tree : BorrowTree) (query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get query = some node) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree query ownerKind lower upper)
    (roots : ProvenanceGC.Roots) (stack : ThreadStacks.ActualStack) (raw : GeneralBorrowGcFrameProvenanceStack.StackForm stack)
    (frameIndex : Nat) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrow : FrameState) (id : AllocId)
    (framePresent : stack.frames[frameIndex]? = some frame) (borrowPresent : frame.extra.borrowTracker = some borrow)
    (stored : (id,node.tag) ∈ borrow.protectedTags) :
    ∃ collected,roots.stack stack = .ok collected ∧ collected.allocations.contains id = true ∧
      ∃ next,(tree.removeUnreachableTags collected.tags).tree.nodes.get query = some next ∧ next.tag = node.tag ∧
        ActiveWithin (tree.removeUnreachableTags collected.tags).tree query ownerKind lower upper := by
  obtain ⟨collected,actual,extension,held,allocation⟩ := GeneralBorrowGcFrameProvenanceStack.protector roots stack raw frameIndex frame borrow id node.tag framePresent borrowPresent stored
  exact ⟨collected,actual,allocation,retained tree collected.tags query node present held ownerKind lower upper active⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingActivityGc
