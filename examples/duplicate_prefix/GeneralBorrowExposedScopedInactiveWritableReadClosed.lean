import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadData
import duplicate_prefix.GeneralBorrowSparseLeafCallback
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadClosed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowSparseLeafCallback
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab in
elab "inactive_writable_read_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.endsWith ".GeneralBorrowExposedScopedAncestorAccess.iterator" then some name else none
  match names with
  | [name]=>return mkConst name
  | _=>throwError "expected fixed scoped Read source iterator"

/-- Actual concrete exposed inactive-component Read followed by every ordered old-root
callback retains effective writable leaves. Physical other-root Reads really
materialize/access reservations; virtual calls really materialize lazy states.
The full cache is framed rather than treating those callbacks as no-ops. -/
theorem frame (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop) (writable : Nat→Bool)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable) :
    let result:=source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range
    source_access_status result=none ∧
    (source_access_location result).exposedCache=location.exposedCache ∧
    Writable tree protections area.support (source_access_location result) := by
  let normalLocation:=(tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location
  have normal:=GeneralBorrowExposedScopedInactiveExposureNormal.access tree location protections anchor .Read .VisitChildrenOfAccessed data.base.base.forest
    data.base.base.component data.base.base.owned context.depth context.children context.anchorNode context.anchorPresent data.base.base.ancestors data.base.base.coherent
  have normalWritable : Writable tree protections area.support normalLocation := by
    intro query node member present
    have same:=normal.2.2.2.2 query node present (data.base.base.separate query member)
    change GeneralBorrowExposedConditionalWritePermissions.Compatible ((tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location.perms.get query |>.getD node.defaultLocationState) .LocalAccess (protections.contains node.tag)
    rw [same]
    exact data.writableLeaves query node member present
  have all : ∀roots : List UniIndex,(∀root∈roots,root∈tail)→∀before,
      GeneralBorrowExposureCardinality.LocationCoherent tree before protections→Writable tree protections area.support before→
      ∃after,GeneralBorrowExposedKnownRootSchedule.run tree roots selected before context.selectedNode.tag protections=⟨after,.Completed⟩ ∧
        GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧ after.exposedCache=before.exposedCache ∧
        Writable tree protections area.support after := by
    intro roots
    induction roots with
    | nil=>intro subset before coherent ready;exact ⟨before,rfl,coherent,rfl,ready⟩
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
        obtain ⟨after,actual,finalCoherent,finalCache,finalWritable⟩:=ih (fun query member=>subset query (by simp [member])) middle middleCoherent middleWritable
        refine ⟨after,?_,finalCoherent,finalCache.trans cache,finalWritable⟩
        simpa only [GeneralBorrowExposedKnownRootSchedule.run,same,ite_false,called,beq_self_eq_true,ite_true] using actual
  let first : BorrowTree.WildcardLocationAccessResult:=if selected=head then ⟨normalLocation,.Completed⟩ else
    tree.performWildcardAccessAt normalLocation head (some context.selectedNode.tag) .Read protections false
  have firstGood : first.status=.Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree first.location protections ∧
      first.location.exposedCache=normalLocation.exposedCache ∧ Writable tree protections area.support first.location := by
    by_cases same : selected=head
    · simp only [first,same,ite_true]
      exact ⟨True.intro,normal.2.2.2.1,True.intro,normalWritable⟩
    · let rootData:=data.base.base.primary (Ne.symm same)
      have included:=rootData.base.included head rootData.base.rooted
      obtain ⟨node,present,leaf,exposed⟩:=data.leaves head included
      obtain ⟨after,called,coherent,cache,ready,others⟩:=GeneralBorrowSparseLeafCallback.step tree normalLocation protections area.support head node
        (some context.selectedNode.tag) .Read false present leaf exposed included normal.2.2.2.1 data.short normalWritable
        (by intro tag equal;cases equal;exact context.tags head node included present)
      simp only [first,same,ite_false,called]
      exact ⟨True.intro,coherent,cache,ready⟩
  obtain ⟨after,completed,coherent,cache,ready⟩:=all tail (fun _ member=>member) first.location firstGood.2.1 firstGood.2.2.2
  have firstEq : first=⟨first.location,.Completed⟩:=by
    have reconstruct : first=⟨first.location,first.status⟩:=by cases first;rfl
    rw [firstGood.1] at reconstruct
    exact reconstruct
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).access.root=selected.toNat:=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans data.base.base.rootPath
  obtain ⟨actual,status⟩:=inactive_writable_read_iterator tree location first.location after anchor selected head context.selectedNode tail protections range
    context.roots context.selectedPresent normal.1 normal.2.1 rootEq firstEq completed
  dsimp only
  rw [actual]
  exact ⟨status,cache.trans (firstGood.2.2.1.trans normal.2.2.1),ready⟩

/-- Full strengthened inactive raw Read data is reconstructed from the actual source
operation. No successful old-root callback, final scalar profile or exactUnique
substitute is an input. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop) (writable : Nat→Bool) (fits : tree.nodes.data.size≤4294967296)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range)=none ∧
    Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree
      (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range))
      protections anchor selected head tail support writable) := by
  have complete:=GeneralBorrowExposedScopedInactiveMixedClosedData.access tree location protections anchor selected head tail range context support writable fits data.base
  have kept:=frame tree location protections anchor selected head tail range context support writable data
  obtain ⟨base⟩:=complete.2
  exact ⟨complete.1,⟨base,data.short,data.leaves,kept.2.2⟩⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadClosed
