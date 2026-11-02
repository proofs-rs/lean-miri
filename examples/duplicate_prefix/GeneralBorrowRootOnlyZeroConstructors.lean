import duplicate_prefix.GeneralBorrowRootOnlyPositiveConstructors
import duplicate_prefix.GeneralBorrowZeroSharedState
import duplicate_prefix.GeneralBorrowZeroDefaultState
namespace DuplicatePrefix.GeneralBorrowRootOnlyZeroConstructors
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralBorrowRootOnlyConstructorFrames DuplicatePrefix.GeneralBorrowRootOnlySharedFrames DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralBorrowSifa
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
/-- The actual zero-length Shared constructor preserves root-only exposure,
Unique storage and exact caches; allocator append/reuse is derived internally. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree root ∧
    Every (LocationInvariant cache root) (GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree.locations := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  let P := fun tree : BorrowTree => RootOnly tree root ∧ Every (LocationInvariant cache root) tree.locations
  have frame : ∀ (index : UniIndex) (mapping : UniKeyMap BorTag),
      tree.tagMapping.insert tag = .Inserted mapping index →
      (tree.nodes.insert index (GeneralBorrowFreshAnchor.sharedNode tag root)).get root = some s.node →
      P (GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree := by
    intro index mapping inserted parentAfter
    let stage := {(GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)) with tagMapping := mapping}
    have stageOnly : RootOnly stage root := by
      simpa only [stage,RootOnly] using attach tree root index s.node (GeneralBorrowFreshAnchor.sharedNode tag root) only rfl
    have stageInitial : Every (LocationInvariant cache root) stage.locations := by
      simpa only [stage,GeneralBorrowFreshGraph.attached] using initial
    have result : P (sourceUpdateSifa stage root .Read).1 := sifa stage root root .Read cache stageOnly stageInitial
    have actual := GeneralBorrowZeroSharedConstructor.exact tree s.node.tag tag root index s.node mapping
      inserted tagged parentAfter offset false
    have trees : (GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree = (sourceUpdateSifa stage root .Read).1 :=
      by simpa only [GeneralBorrowZeroSharedState.operation,stage] using congrArg BorrowTree.ChildInsertResult.tree actual
    exact (congrArg P trees).mpr result
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
      rw [aligned];change tree.nodes.data.size+5 ≤ _ at room;change tree.nodes.data.size ≤ _;omega
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    have different := GeneralBorrowFreshNode.parent_not_fresh tree.nodes index root s.node atEnd s.star.present
    exact frame index _ (GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits)
      ((GeneralBorrowFreshLocation.get_other tree.nodes index root (GeneralBorrowFreshAnchor.sharedNode tag root) different).trans s.star.present)
  | some index =>
    have vacant := s.allocator.pool.vacant index (Array.mem_of_back? available)
    have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node vacant s.star.present
    exact frame index _ (GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh index available)
      ((GeneralBorrowFreshLocation.get_other tree.nodes index root (GeneralBorrowFreshAnchor.sharedNode tag root) different).trans s.star.present)

/-- The actual zero-length Default constructor preserves root-only exposure,
Unique storage and exact caches; allocator append/reuse is derived internally. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64)
    (cache : ExposedCache) (only : RootOnly tree root)
    (initial : Every (LocationInvariant cache root) tree.locations) :
    RootOnly (GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree root ∧
    Every (LocationInvariant cache root) (GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree.locations := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  let P := fun tree : BorrowTree => RootOnly tree root ∧ Every (LocationInvariant cache root) tree.locations
  have frame : ∀ (index : UniIndex) (mapping : UniKeyMap BorTag),
      tree.tagMapping.insert tag = .Inserted mapping index →
      (tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag root)).get root = some s.node →
      P (GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree := by
    intro index mapping inserted parentAfter
    let stage := {(GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)) with tagMapping := mapping}
    have stageOnly : RootOnly stage root := by
      simpa only [stage,RootOnly] using attach tree root index s.node (GeneralBorrowFreshDefaultChild.child tag root) only rfl
    have stageInitial : Every (LocationInvariant cache root) stage.locations := by
      simpa only [stage,GeneralBorrowFreshGraph.attached] using initial
    have result : P (sourceUpdateSifa stage root .Read).1 := sifa stage root root .Read cache stageOnly stageInitial
    have actual := GeneralBorrowZeroDefaultConstructor.exact tree s.node.tag tag root index s.node mapping
      inserted tagged parentAfter offset
    have trees : (GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree = (sourceUpdateSifa stage root .Read).1 :=
      by simpa only [GeneralBorrowZeroDefaultState.operation,stage] using congrArg BorrowTree.ChildInsertResult.tree actual
    exact (congrArg P trees).mpr result
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
      rw [aligned];change tree.nodes.data.size+5 ≤ _ at room;change tree.nodes.data.size ≤ _;omega
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    have different := GeneralBorrowFreshNode.parent_not_fresh tree.nodes index root s.node atEnd s.star.present
    exact frame index _ (GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh available fits)
      ((GeneralBorrowFreshLocation.get_other tree.nodes index root (GeneralBorrowFreshDefaultChild.child tag root) different).trans s.star.present)
  | some index =>
    have vacant := s.allocator.pool.vacant index (Array.mem_of_back? available)
    have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root s.node vacant s.star.present
    exact frame index _ (GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh index available)
      ((GeneralBorrowFreshLocation.get_other tree.nodes index root (GeneralBorrowFreshDefaultChild.child tag root) different).trans s.star.present)

end DuplicatePrefix.GeneralBorrowRootOnlyZeroConstructors
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyZeroConstructors." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only zero constructor dependency {dependency}"
