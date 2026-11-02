import duplicate_prefix.GeneralBorrowWildcardConstructorState
namespace DuplicatePrefix.GeneralBorrowWildcardConstructorSlot
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

/-- A coherent arbitrary pool determines the real wildcard constructor slot,
including its fresh row and size bounds. No free-pool emptiness or successful
insert outcome is a caller premise. -/
theorem select (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) :
    ∃ mapping index, tree.tagMapping.insert tag = .Inserted mapping index ∧
      mapping.mapping = tree.tagMapping.mapping.push (tag,index) ∧ tree.nodes.get index = none ∧
      GeneralBorrowStructuralHistoryState.GraphState (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) ∧
      tree.nodes.size ≤ (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).size ∧
      (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).size ≤ tree.nodes.size+1 := by
  obtain ⟨mapping,index,inserted,graph,growth⟩ := GeneralBorrowStructuralHistoryWildcardAllocator.select tree runtime.formed.toGraphState tag fresh room outside sifa
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree runtime.formed.toState tag fresh room mapping index inserted
  refine ⟨mapping,index,inserted,?_,vacant,graph,?_,growth⟩
  · cases available : tree.tagMapping.deassigned.back? with
    | none =>
      have aligned := GeneralBorrowFreshStagePool.empty_aligned tree runtime.formed.allocator.accounting available
      have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by change tree.nodes.data.size+1 ≤ _ at room;omega
      have actual := GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits
      have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
      rw [←equal.1,←equal.2]
    | some chosen =>
      have actual := GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh chosen available
      have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
      rw [←equal.1,←equal.2]
  · cases available : tree.tagMapping.deassigned.back? with
    | none =>
      have aligned := GeneralBorrowFreshStagePool.empty_aligned tree runtime.formed.allocator.accounting available
      have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by change tree.nodes.data.size+1 ≤ _ at room;omega
      have actual := GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits
      have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
      rw [←equal.2]
      have atEnd : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
        simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
        exact aligned
      rw [GeneralBorrowFreshNode.append_size tree.nodes _ _ atEnd]
      omega
    | some chosen =>
      have actual := GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh chosen available
      have equal := UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)
      rw [←equal.2]
      have bounded := runtime.formed.allocator.pool.bounded chosen (Array.mem_of_back? available)
      rw [GeneralBorrowFreshReuseNode.bounded_size tree.nodes chosen _ bounded]
      exact Nat.le_refl _
end DuplicatePrefix.GeneralBorrowWildcardConstructorSlot
