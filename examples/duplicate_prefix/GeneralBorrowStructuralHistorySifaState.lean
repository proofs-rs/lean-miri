import duplicate_prefix.GeneralBorrowStructuralHistoryConcreteAllocator
import duplicate_prefix.GeneralBorrowAllocationSifaConsistency
import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowGcSifaConsistency
namespace DuplicatePrefix.GeneralBorrowStructuralHistorySifaState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowLocationSifaConsistency GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Physical scalar skip-cache bounds and vacancy cleanliness, in addition to
intrinsic structure. This invariant asserts no permission ownership by itself. -/
structure Formed (tree : BorrowTree) (protections : ProtectedTags) : Prop extends State tree where
  profile : Every (fun location => Profile tree location protections) tree.locations

theorem initial (tag : BorTag) (size : Size) (protections : ProtectedTags) : Formed (BorrowTree.new tag size) protections :=
  ⟨GeneralBorrowStructuralHistorySeed.initial tag size,GeneralBorrowAllocationSifaConsistency.allocation size.bytes tag protections⟩

/-- Every genuinely vacant allocator slot is physically Clean everywhere. -/
theorem vacant_clean (tree : BorrowTree) (protections : ProtectedTags) (formed : Formed tree protections) :
    GeneralBorrowGcVacantClean.VacantClean tree := by
  intro index vacant position valid
  exact (formed.profile position valid).vacant index vacant

theorem gc (tree : BorrowTree) (protections : ProtectedTags) (formed : Formed tree protections) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome=.ok () ∧ Formed (tree.removeUnreachableTags live).tree protections := by
  have structural := GeneralBorrowStructuralHistoryState.gc tree formed.toState live
  exact ⟨structural.1,⟨structural.2.1,GeneralBorrowGcSifaConsistency.collect tree protections live formed.profile⟩⟩

/-- Raw initial allocator data determines that the exact successful tag insertion
uses an actually vacant slot; operation success is the conclusion of insert's
raw Fresh policy, not a constructor outcome assumption. -/
theorem vacant_of_insert (tree : BorrowTree) (state : State tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (inserted : tree.tagMapping.insert tag=.Inserted mapping index) :
    tree.nodes.get index=none := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree state.allocator.accounting available
    have fits : tree.tagMapping.mapping.size≤4294967295 := by change tree.nodes.data.size+1≤_ at room;omega
    have actual := GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits
    have same := (UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)).2
    rw [←same]
    have atEnd : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩:UniIndex).toNat=tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size<2^32)]
      exact aligned
    simp [UniValMap.get,atEnd]
  | some slot =>
    have actual := GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh slot available
    have same := (UniKeyMapInsertResult.Inserted.inj (actual.symm.trans inserted)).2
    rw [←same]
    exact state.allocator.pool.vacant slot (Array.mem_of_back? available)
end DuplicatePrefix.GeneralBorrowStructuralHistorySifaState
