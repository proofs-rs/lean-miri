import duplicate_prefix.GeneralBorrowStructuralHistoryWildcardGraph
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryWildcardAllocator
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowGcAllocator GeneralBorrowFreshStagePool
open GeneralBorrowFreshAllocatorInvariant GeneralBorrowStructuralHistoryWildcardGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem installed_tags (tree : BorrowTree) (initial : GraphState tree) (tag : BorTag) (index : UniIndex)
    (free : Array UniIndex) (outside : Permission) (sifa : IdempotentForeignAccess)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) :
    NodeTags (WildcardHitZeroConstructor.installed tree ⟨tree.tagMapping.mapping.push (tag,index),free⟩ index tag outside sifa) := by
  have pushed := GeneralBorrowSharedAllocatorInvariant.push_tags tree tag index free fresh initial.allocator.nodeTags
  have lookup := GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh index free
  exact GeneralBorrowSharedAllocatorInvariant.insert_tags {tree with tagMapping:=⟨tree.tagMapping.mapping.push (tag,index),free⟩}
    index (WildcardHitZeroConstructor.rootNode tag outside sifa) lookup pushed

private theorem installed_graph (tree : BorrowTree) (initial : GraphState tree) (mapping : UniKeyMap BorTag)
    (index : UniIndex) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (vacant : tree.nodes.get index=none)
    (allocator : Invariant (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa))
    (fits : (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).nodes.size≤4294967296) :
    GraphState (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
  let after := WildcardHitZeroConstructor.installed tree mapping index tag outside sifa
  have extended := extension tree initial mapping index tag outside sifa vacant
  refine ⟨?_,⟨GeneralBorrowGcDfsGraphRestoration.depth _ after extended⟩,?_,
    covered tree initial mapping index tag outside sifa,root_nodes tree initial mapping index tag outside sifa vacant,allocator,fits⟩
  · intro location protections
    exact ⟨GeneralBorrowGcDfsProjectedForest.of_graph after _ extended fits location protections⟩
  · intro parent node present child member
    obtain ⟨childNode,childPresent,_⟩ := extended.children parent node present child member
    exact ⟨childNode,childPresent⟩

/-- Raw intrinsic allocator State chooses the real newChild back free slot or
append index. Both branches form a new isolated root and all graph/allocator
invariants, with no parent or permissions required. -/
theorem select (tree : BorrowTree) (initial : GraphState tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) :
    ∃ mapping index, tree.tagMapping.insert tag=.Inserted mapping index ∧
      GraphState (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) ∧
      (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).nodes.size≤tree.nodes.size+1 := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    have aligned := empty_aligned tree initial.allocator.accounting available
    have fits : tree.tagMapping.mapping.size≤4294967295 := by change tree.nodes.data.size+1≤_ at room;omega
    have atEnd : index.toNat=tree.nodes.data.size := by
      change (UInt32.ofNat tree.tagMapping.mapping.size).toNat=_
      rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
      exact aligned
    have vacant : tree.nodes.get index=none := by simp [UniValMap.get,atEnd]
    have capacity := GeneralBorrowFreshNode.append_size tree.nodes index (WildcardHitZeroConstructor.rootNode tag outside sifa) atEnd
    have clear := Array.back?_eq_none_iff.mp available
    have pool : Pool (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)) tree.tagMapping.deassigned := by
      rw [clear]
      exact ⟨by simp,by simp,by simp⟩
    have accounting : Accounting (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
      simp only [Accounting,WildcardHitZeroConstructor.installed,mapping,Array.size_push]
      rw [capacity,clear,Array.size_empty,Nat.add_zero,aligned]
      rfl
    have allocator : Invariant (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) :=
      ⟨pool,accounting,fresh_push_unique tree.tagMapping tag index tree.tagMapping.deassigned initial.allocator.unique fresh,
        installed_tags tree initial tag index tree.tagMapping.deassigned outside sifa fresh⟩
    refine ⟨mapping,index,GeneralBorrowTagMap.insert_append _ tag fresh available fits,
      installed_graph tree initial mapping index tag outside sifa vacant allocator (by change (tree.nodes.insert index _).size≤_;rw[capacity];omega),?_⟩
    exact Nat.le_of_eq capacity
  | some index =>
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩
    have member := Array.mem_of_back? available
    have bounded := initial.allocator.pool.bounded index member
    have vacant := initial.allocator.pool.vacant index member
    have capacity := GeneralBorrowFreshReuseNode.bounded_size tree.nodes index (WildcardHitZeroConstructor.rootNode tag outside sifa) bounded
    have pool := consume tree.nodes tree.tagMapping.deassigned initial.allocator.pool index available (WildcardHitZeroConstructor.rootNode tag outside sifa)
    have nonempty : 0<tree.tagMapping.deassigned.size := by
      obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp available
      rw[eq,Array.size_push];omega
    have accounting : Accounting (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
      simp only [Accounting,WildcardHitZeroConstructor.installed,mapping,Array.size_push]
      rw [capacity,Array.size_pop]
      have old := initial.allocator.accounting
      unfold Accounting at old
      omega
    have allocator : Invariant (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) :=
      ⟨pool,accounting,fresh_push_unique tree.tagMapping tag index tree.tagMapping.deassigned.pop initial.allocator.unique fresh,
        installed_tags tree initial tag index tree.tagMapping.deassigned.pop outside sifa fresh⟩
    refine ⟨mapping,index,GeneralBorrowTagMap.insert_free _ tag fresh index available,
      installed_graph tree initial mapping index tag outside sifa vacant allocator (by change (tree.nodes.insert index _).size≤_;rw[capacity];omega),?_⟩
    change (tree.nodes.insert index _).size≤_
    rw[capacity];omega
end DuplicatePrefix.GeneralBorrowStructuralHistoryWildcardAllocator
