import duplicate_prefix.GeneralBorrowStructuralHistoryWildcardAllocator
import duplicate_prefix.GeneralBorrowFreshRangeFrame
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryWildcard
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem positive_exact (tree : BorrowTree) (initialState : State tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (inserted : tree.tagMapping.insert tag=.Inserted mapping index)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial=true) (nonunique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (insideInitial : inside.permission.isInitial=true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held=.Access inside.idempotentForeignAccess)
    (offset len : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held =
      ⟨GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len,.ok ()⟩ := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree initialState.allocator.accounting available
    have fits : tree.tagMapping.mapping.size≤4294967295 := by change tree.nodes.data.size+1≤_ at room;omega
    have allocation := GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits
    have agree := UniKeyMapInsertResult.Inserted.inj (allocation.symm.trans inserted)
    have operation := GeneralBorrowPositiveWildcardConstructor.append tree tag fresh available fits outside sifa inside held
      initial nonunique foreign insideInitial insideForeign offset len nonzero initialState.well bounds
    dsimp only at operation
    rw [agree.1,agree.2] at operation
    exact operation
  | some slot =>
    have allocation := GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh slot available
    have agree := UniKeyMapInsertResult.Inserted.inj (allocation.symm.trans inserted)
    have operation := GeneralBorrowPositiveWildcardConstructor.reuse tree tag slot fresh available outside sifa inside held
      initial nonunique foreign insideInitial insideForeign offset len nonzero initialState.well bounds
    dsimp only at operation
    rw [agree.1,agree.2] at operation
    exact operation

private theorem build (tree : BorrowTree) (initialState : State tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial=true) (nonunique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa)
    (insideInitial : inside.permission.isInitial=true)
    (insideForeign : inside.permission.strongestIdempotentForeignAccess held=.Access inside.idempotentForeignAccess)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let operation := tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new (Size.ofBytes len) inside) outside held
    operation.outcome=.ok () ∧ State operation.tree ∧ operation.tree.locations.size=tree.locations.size ∧
      operation.tree.nodes.size≤tree.nodes.size+1 := by
  obtain ⟨mapping,index,inserted,stageGraph,growth⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select tree initialState.toGraphState tag fresh room outside sifa
  by_cases empty : len=0
  · subst len
    have actual := WildcardHitZeroConstructor.exact tree tag index mapping inserted outside sifa held initial nonunique foreign inside offset
    dsimp only
    simp only [show Size.ofBytes 0=Size.ZERO from rfl]
    rw [actual]
    exact ⟨rfl,⟨stageGraph,initialState.well⟩,rfl,growth⟩
  · have actual := positive_exact tree initialState tag fresh room mapping index inserted outside sifa inside held
      initial nonunique foreign insideInitial insideForeign offset len empty bounds
    dsimp only
    rw [actual]
    have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => {location with perms:=location.perms.insert index inside}) initialState.well bounds
    exact ⟨rfl,⟨GeneralBorrowStructuralHistoryState.graph_locations _ _ stageGraph,geometry.1⟩,
      congrArg Size.ofBytes geometry.2,growth⟩

/-- Actual wildcard Default reservation at any root list and coherent sparse
allocator, including zero lengths and reuse of the real back free slot. Graph,
partition and allocator State are derived from raw State/freshness/room/bounds;
no permission ownership, operation success or intermediate State is assumed. -/
theorem construct (tree : BorrowTree) (initial : State tree) (newTag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let operation := tree.newChild (Size.ofBytes offset) .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    operation.outcome=.ok () ∧ State operation.tree ∧ operation.tree.locations.size=tree.locations.size ∧
      operation.tree.nodes.size≤tree.nodes.size+1 :=
  build tree initial newTag fresh room (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true
    rfl rfl rfl rfl rfl offset len bounds

/-- Shared Frozen wildcard root construction, protected or unprotected, with
arbitrary zero/positive length and the same intrinsic structural guarantee. -/
theorem shared (tree : BorrowTree) (initial : State tree) (newTag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (held : Bool) (offset len : UInt64) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let operation := tree.newChild (Size.ofBytes offset) .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    operation.outcome=.ok () ∧ State operation.tree ∧ operation.tree.locations.size=tree.locations.size ∧
      operation.tree.nodes.size≤tree.nodes.size+1 := by
  have foreign : Permission.Frozen.strongestIdempotentForeignAccess held=.Access .Read := by cases held <;> rfl
  exact build tree initial newTag fresh room .Frozen .Read GeneralBorrowFreshAnchor.sharedState held
    rfl rfl foreign rfl foreign offset len bounds
end DuplicatePrefix.GeneralBorrowStructuralHistoryWildcard
