import duplicate_prefix.GeneralBorrowWildcardConstructorSlot
namespace DuplicatePrefix.GeneralBorrowWildcardConstructorExact
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- Exact actual positive wildcard constructor calculation for the slot selected
from raw state. This internal composition law is not a final invocation contract. -/
theorem exact (tree : BorrowTree) (initialState : State tree) (tag : BorTag)
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

end DuplicatePrefix.GeneralBorrowWildcardConstructorExact
