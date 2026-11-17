import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadData
import duplicate_prefix.GeneralBorrowSparseLeafCallback
import duplicate_prefix.GeneralBorrowFreshActiveOnClean
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadVacant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowSparseLeafCallback
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab in
elab "inactive_writable_vacant_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.endsWith ".GeneralBorrowExposedScopedAncestorAccess.iterator" then some name else none
  match names with
  | [name]=>return mkConst name
  | _=>throwError "expected fixed scoped Read source iterator"

/-- Actual concrete hidden-component Read followed by every ordered old-root
callback retains effective writable leaves. Physical other-root Reads really
materialize/access reservations; virtual calls really materialize lazy states.
The full cache is framed rather than treating those callbacks as no-ops. -/
theorem frame (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop) (writable : Nat→Bool)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable)
    (query : UniIndex) (vacant : tree.nodes.get query=none) (clean : location.perms.get query=none) :
    let result:=source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range
    source_access_status result=none ∧
    (source_access_location result).exposedCache=location.exposedCache ∧
    Writable tree protections area.support (source_access_location result) ∧
    (source_access_location result).perms.get query=location.perms.get query := by
  let normalLocation:=(tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location
  have normal:=GeneralBorrowExposedScopedInactiveExposureNormal.access tree location protections anchor .Read .VisitChildrenOfAccessed data.base.base.forest
    data.base.base.component data.base.base.owned context.depth context.children context.anchorNode context.anchorPresent data.base.base.ancestors data.base.base.coherent
  have normalWritable : Writable tree protections area.support normalLocation := by
    intro query node member present
    have same:=normal.2.2.2.2 query node present (data.base.base.separate query member)
    change GeneralBorrowExposedConditionalWritePermissions.Compatible ((tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location.perms.get query |>.getD node.defaultLocationState) .LocalAccess (protections.contains node.tag)
    rw [same]
    exact data.writableLeaves query node member present
  have normalFrame : normalLocation.perms.get query=location.perms.get query := by
    rw [clean]
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query .Read .VisitChildrenOfAccessed
      context.depth context.children context.anchorNode context.anchorPresent vacant clean
  have all : ∀roots : List UniIndex,(∀root∈roots,root∈tail)→∀before,
      GeneralBorrowExposureCardinality.LocationCoherent tree before protections→Writable tree protections area.support before→
      ∃after,GeneralBorrowExposedKnownRootSchedule.run tree roots selected before context.selectedNode.tag protections=⟨after,.Completed⟩ ∧
        GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧ after.exposedCache=before.exposedCache ∧
        Writable tree protections area.support after ∧ after.perms.get query=before.perms.get query := by
    intro roots
    induction roots with
    | nil=>intro subset before coherent ready;exact ⟨before,rfl,coherent,rfl,ready,rfl⟩
    | cons root rest ih=>
      intro subset before coherent ready
      by_cases same : root=selected
      · simpa only [GeneralBorrowExposedKnownRootSchedule.run,same,ite_true] using ih (fun query member=>subset query (by simp [member])) before coherent ready
      · let rootData:=data.base.base.virtual root (subset root (by simp)) same
        have included:=rootData.included root rootData.rooted
        obtain ⟨node,present,leaf,exposed⟩:=data.leaves root included
        obtain ⟨middle,called,middleCoherent,cache,middleWritable,others⟩:=GeneralBorrowSparseLeafCallback.step tree before protections area.support
          root node (some context.selectedNode.tag) .Read true present leaf exposed included coherent data.short ready
          (by intro tag equal;cases equal;exact context.tags root node included present)
        obtain ⟨after,actual,finalCoherent,finalCache,finalWritable,finalFrame⟩:=ih (fun query member=>subset query (by simp [member])) middle middleCoherent middleWritable
        have different : query≠root := by intro equal;subst query;rw [show tree.nodeAt root=none from vacant] at present;cases present
        refine ⟨after,?_,finalCoherent,finalCache.trans cache,finalWritable,finalFrame.trans (others query different)⟩
        simpa only [GeneralBorrowExposedKnownRootSchedule.run,same,ite_false,called,beq_self_eq_true,ite_true] using actual
  let first : BorrowTree.WildcardLocationAccessResult:=if selected=head then ⟨normalLocation,.Completed⟩ else
    tree.performWildcardAccessAt normalLocation head (some context.selectedNode.tag) .Read protections false
  have firstGood : first.status=.Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree first.location protections ∧
      first.location.exposedCache=normalLocation.exposedCache ∧ Writable tree protections area.support first.location ∧ first.location.perms.get query=normalLocation.perms.get query := by
    by_cases same : selected=head
    · simp only [first,same,ite_true]
      exact ⟨True.intro,normal.2.2.2.1,True.intro,normalWritable,True.intro⟩
    · let rootData:=data.base.base.primary (Ne.symm same)
      have included:=rootData.base.included head rootData.base.rooted
      obtain ⟨node,present,leaf,exposed⟩:=data.leaves head included
      obtain ⟨after,called,coherent,cache,ready,others⟩:=GeneralBorrowSparseLeafCallback.step tree normalLocation protections area.support head node
        (some context.selectedNode.tag) .Read false present leaf exposed included normal.2.2.2.1 data.short normalWritable
        (by intro tag equal;cases equal;exact context.tags head node included present)
      simp only [first,same,ite_false,called]
      have different : query≠head := by intro equal;subst query;rw [show tree.nodeAt head=none from vacant] at present;cases present
      exact ⟨True.intro,coherent,cache,ready,others query different⟩
  obtain ⟨after,completed,coherent,cache,ready,queryFrame⟩:=all tail (fun _ member=>member) first.location firstGood.2.1 firstGood.2.2.2.1
  have firstEq : first=⟨first.location,.Completed⟩:=by
    have reconstruct : first=⟨first.location,first.status⟩:=by cases first;rfl
    rw [firstGood.1] at reconstruct
    exact reconstruct
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).access.root=selected.toNat:=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans data.base.base.rootPath
  obtain ⟨actual,status⟩:=inactive_writable_vacant_iterator tree location first.location after anchor selected head context.selectedNode tail protections range
    context.roots context.selectedPresent normal.1 normal.2.1 rootEq firstEq completed
  dsimp only
  rw [actual]
  exact ⟨status,cache.trans (firstGood.2.2.1.trans normal.2.2.1),ready,queryFrame.trans (firstGood.2.2.2.2.trans normalFrame)⟩

end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadVacant
