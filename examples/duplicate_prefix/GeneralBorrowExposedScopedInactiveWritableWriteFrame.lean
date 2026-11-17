import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAccessData
import duplicate_prefix.GeneralBorrowExposedKnownRootWriteSchedule
import duplicate_prefix.GeneralBorrowSparseLeafCallback
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableWriteFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowSparseLeafCallback
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
open Lean Elab in
elab "inactive_write_scanAt" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.scanAt" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected source-bound selected-root callback"
open Lean Elab in
elab "inactive_write_indexed" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.indexed" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected source-bound selected-root index adapter"

private theorem iterator (tree : BorrowTree) (before middle after : LocationTree) (anchor selected head : UniIndex)
    (selectedNode : TreeNode) (tail : List UniIndex) (protections : ProtectedTags)  (range : ByteRange)
    (roots : tree.roots = (head::tail).toArray) (present : tree.nodes.get selected = some selectedNode)
    (normalStatus : (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).access.status = .Completed)
    (normalOutcome : (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).outcome = .ok ())
    (rootEq : (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).access.root = selected.toNat)
    (first : (if selected = head then ⟨(tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).location,.Completed⟩
      else tree.performWildcardAccessAt (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).location head
        (some selectedNode.tag) .Write protections false) = (⟨middle,.Completed⟩ : BorrowTree.WildcardLocationAccessResult))
    (completed : GeneralBorrowExposedKnownRootWriteSchedule.run tree tail selected middle selectedNode.tag protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before (some anchor) .Write protections .VisitChildrenOfAccessed range) = after ∧
    source_access_status (source_tree_access_at tree before (some anchor) .Write protections .VisitChildrenOfAccessed range) = none := by
  simp_tree_helpers
  simp only [normalStatus,normalOutcome,rootEq,index_self,present,roots]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  by_cases same : selected = head
  · subst selected
    have equal : (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).location = middle := by
      simpa only [ite_true] using congrArg BorrowTree.WildcardLocationAccessResult.location first
    simp [present,List.size_toArray,List.range'_succ,bind,pure,equal]
    change (forIn (List.range' 1 tail.length) (middle,none,false)
      (inactive_write_scanAt tree head head tail selectedNode.tag .Write protections range)).1 = after ∧
      (forIn (List.range' 1 tail.length) (middle,none,false)
      (inactive_write_scanAt tree head head tail selectedNode.tag .Write protections range)).2.1 = none
    rw [inactive_write_indexed,GeneralBorrowExposedKnownRootWriteSchedule.successful tree tail head middle after selectedNode.tag protections range completed]
    exact ⟨rfl,rfl⟩
  · have called : tree.performWildcardAccessAt (tree.performNormalAccessAt before anchor .Write protections .VisitChildrenOfAccessed).location head
        (some selectedNode.tag) .Write protections false = ⟨middle,.Completed⟩ := by simpa only [same,ite_false] using first
    simp [present,List.size_toArray,List.range'_succ,bind,pure,same,called]
    change (forIn (List.range' 1 tail.length) (middle,none,false)
      (inactive_write_scanAt tree head selected tail selectedNode.tag .Write protections range)).1 = after ∧
      (forIn (List.range' 1 tail.length) (middle,none,false)
      (inactive_write_scanAt tree head selected tail selectedNode.tag .Write protections range)).2.1 = none
    rw [inactive_write_indexed,GeneralBorrowExposedKnownRootWriteSchedule.successful tree tail selected middle after selectedNode.tag protections range completed]
    exact ⟨rfl,rfl⟩

/-- Actual concrete exposed inactive-component Read followed by every ordered old-root
callback retains effective writable leaves. Physical other-root Reads really
materialize/access reservations; virtual calls really materialize lazy states.
The full cache is framed rather than treating those callbacks as no-ops. -/
theorem frame (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop)
    (data : GeneralBorrowExposedScopedInactiveWritableAccessData.Data tree location protections anchor selected head tail support) :
    let result:=source_tree_access_at tree location (some anchor) .Write protections .VisitChildrenOfAccessed range
    source_access_status result=none ∧
    (source_access_location result).exposedCache=location.exposedCache ∧
    Writable tree protections area.support (source_access_location result) ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    (∀query,¬area.support query→(source_access_location result).perms.get query=
      (tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).location.perms.get query) := by
  let normalLocation:=(tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).location
  have normal:=GeneralBorrowExposedScopedInactiveExposureNormal.access tree location protections anchor .Write .VisitChildrenOfAccessed data.base.base.forest
    data.base.base.component (GeneralBorrowExposedScopedInactiveWritableAccessData.owned data .Write) context.depth context.children context.anchorNode context.anchorPresent data.base.base.ancestors data.base.base.coherent
  have normalWritable : Writable tree protections area.support normalLocation := by
    intro query node member present
    have same:=normal.2.2.2.2 query node present (data.base.base.separate query member)
    change GeneralBorrowExposedConditionalWritePermissions.Compatible ((tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).location.perms.get query |>.getD node.defaultLocationState) .LocalAccess (protections.contains node.tag)
    rw [same]
    exact data.writableLeaves query node member present
  have all : ∀roots : List UniIndex,(∀root∈roots,root∈tail)→∀before,
      GeneralBorrowExposureCardinality.LocationCoherent tree before protections→Writable tree protections area.support before→
      ∃after,GeneralBorrowExposedKnownRootWriteSchedule.run tree roots selected before context.selectedNode.tag protections=⟨after,.Completed⟩ ∧
        GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧ after.exposedCache=before.exposedCache ∧
        Writable tree protections area.support after ∧
        (∀query,¬area.support query→after.perms.get query=before.perms.get query) := by
    intro roots
    induction roots with
    | nil=>intro subset before coherent ready;exact ⟨before,rfl,coherent,rfl,ready,fun _ _=>rfl⟩
    | cons root rest ih=>
      intro subset before coherent ready
      by_cases same : root=selected
      · simpa only [GeneralBorrowExposedKnownRootWriteSchedule.run,same,ite_true] using ih (fun query member=>subset query (by simp [member])) before coherent ready
      · let rootData:=data.base.base.virtual root (subset root (by simp)) same
        have included:=rootData.included root rootData.rooted
        obtain ⟨node,present,leaf,exposed⟩:=data.leaves root included
        obtain ⟨middle,called,middleCoherent,cache,middleWritable,others⟩:=GeneralBorrowSparseLeafCallback.step tree before protections area.support
          root node (some context.selectedNode.tag) .Write true present leaf exposed included coherent data.short ready
          (by intro tag equal;cases equal;exact context.tags root node included present)
        obtain ⟨after,actual,finalCoherent,finalCache,finalWritable,finalFrame⟩:=ih (fun query member=>subset query (by simp [member])) middle middleCoherent middleWritable
        refine ⟨after,?_,finalCoherent,finalCache.trans cache,finalWritable,?_⟩
        ·
          simpa only [GeneralBorrowExposedKnownRootWriteSchedule.run,same,ite_false,called,beq_self_eq_true,ite_true] using actual
        · intro query outside
          exact (finalFrame query outside).trans (others query (by intro equal;subst query;exact outside included))
  let first : BorrowTree.WildcardLocationAccessResult:=if selected=head then ⟨normalLocation,.Completed⟩ else
    tree.performWildcardAccessAt normalLocation head (some context.selectedNode.tag) .Write protections false
  have firstGood : first.status=.Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree first.location protections ∧
      first.location.exposedCache=normalLocation.exposedCache ∧ Writable tree protections area.support first.location ∧ (∀query,¬area.support query→first.location.perms.get query=normalLocation.perms.get query) := by
    by_cases same : selected=head
    · simp only [first,same,ite_true]
      exact ⟨True.intro,normal.2.2.2.1,True.intro,normalWritable,fun _ _=>True.intro⟩
    · let rootData:=data.base.base.primary (Ne.symm same)
      have included:=rootData.base.included head rootData.base.rooted
      obtain ⟨node,present,leaf,exposed⟩:=data.leaves head included
      obtain ⟨after,called,coherent,cache,ready,others⟩:=GeneralBorrowSparseLeafCallback.step tree normalLocation protections area.support head node
        (some context.selectedNode.tag) .Write false present leaf exposed included normal.2.2.2.1 data.short normalWritable
        (by intro tag equal;cases equal;exact context.tags head node included present)
      simp only [first,same,ite_false,called]
      exact ⟨True.intro,coherent,cache,ready,fun query outside=>others query (by intro equal;subst query;exact outside included)⟩
  obtain ⟨after,completed,coherent,cache,ready,finalFrame⟩:=all tail (fun _ member=>member) first.location firstGood.2.1 firstGood.2.2.2.1
  have firstEq : first=⟨first.location,.Completed⟩:=by
    have reconstruct : first=⟨first.location,first.status⟩:=by cases first;rfl
    rw [firstGood.1] at reconstruct
    exact reconstruct
  have rootEq : (tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).access.root=selected.toNat:=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree location protections)).trans data.base.base.rootPath
  obtain ⟨actual,status⟩:=iterator tree location first.location after anchor selected head context.selectedNode tail protections range
    context.roots context.selectedPresent normal.1 normal.2.1 rootEq firstEq completed
  dsimp only
  rw [actual]
  exact ⟨status,cache.trans (firstGood.2.2.1.trans normal.2.2.1),ready,coherent,
    fun query outside=>(finalFrame query outside).trans (firstGood.2.2.2.2 query outside)⟩

end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableWriteFrame
