import duplicate_prefix.GeneralBorrowRootOnlyZeroConstructors
namespace DuplicatePrefix.GeneralBorrowRootOnlyConstructorFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Actual ancestor-SIFA updates preserve the exact exposure flag at every slot. -/
theorem sifa_flag (tree : BorrowTree) (root start : UniIndex) (strongest : IdempotentForeignAccess) :
    ((sourceUpdateSifa tree start strongest).1.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed :=
  GeneralBorrowFreshMetadataChildSifa.lookup_exposure tree _
    (GeneralBorrowFreshMetadataChildSifa.sifa_exposure tree start strongest) root

/-- Attaching a child retains the original root exposure flag exactly. -/
theorem attached_flag (tree : BorrowTree) (root child : UniIndex) (node newNode : TreeNode) :
    ((GeneralBorrowFreshGraph.attached tree child root node newNode).nodes.get root).map TreeNode.isExposed =
      some node.isExposed := by
  simp only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,
    GeneralBorrowFreshLocation.get_same,Option.map_some]
/-- Exact original-root flag after the real Shared append constructor. -/
theorem shared_append (input : GeneralBorrowFreshMetadataChildShared.Input) :
    ((GeneralBorrowFreshMetadataChildShared.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildShared.stage input)
    (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildShared.index input) input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildShared.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

/-- Exact original-root flag after the real Shared Reuse constructor. -/
theorem shared_reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) :
    ((GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
    (GeneralBorrowFreshMetadataChildSharedReuse.result input) (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildSharedReuse.index input) input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

/-- Exact original-root flag after the real Default append constructor. -/
theorem default_append (input : GeneralBorrowFreshMetadataChildDefault.Input) :
    ((GeneralBorrowFreshMetadataChildDefault.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildDefault.stage input)
    (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildDefault.index input) input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildDefault.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

/-- Exact original-root flag after the real Default Reuse constructor. -/
theorem default_reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) :
    ((GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodes.get input.parent).map TreeNode.isExposed =
      (input.tree.nodes.get input.parent).map TreeNode.isExposed := by
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
    (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (GeneralBorrowFreshMetadataChildDefaultReuse.exposure input) input.parent
  have root := attached_flag input.tree input.parent (GeneralBorrowFreshMetadataChildDefaultReuse.index input) input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
  have stage : ((GeneralBorrowFreshMetadataChildDefaultReuse.stage input).nodes.get input.parent).map TreeNode.isExposed = some input.parentNode.isExposed := by
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged] using root
  rw [flags,stage,show input.tree.nodes.get input.parent = some input.parentNode from input.parentPresent]
  rfl

/-- Actual Shared allocator selection preserves the original root flag. -/
theorem shared (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    ((GeneralBorrowPartitionShared.operation tree s.node.tag tag offset len).tree.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagPresent := s.allocator.nodeTags root s.node s.star.present
  have well := s.well
  have bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact requested
  have slack : depth.depth root < tree.nodes.size := by
    have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
    have available : 0 < tree.nodes.data.size := by omega
    simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using available
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    let input : GeneralBorrowFreshMetadataChildShared.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      isProtected := false,offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact shared_append input
  | some index =>
    have member := Array.mem_of_back? available
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      isProtected := false,offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact shared_reuse input

/-- Actual Default allocator selection preserves the original root flag. -/
theorem reserve (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (requested : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    ((GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).tree.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have tagPresent := s.allocator.nodeTags root s.node s.star.present
  have well := s.well
  have bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact requested
  have slack : depth.depth root < tree.nodes.size := by
    have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root s.node s.star.present
    have available : 0 < tree.nodes.data.size := by omega
    simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using available
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree s.allocator.accounting available
    let input : GeneralBorrowFreshMetadataChildDefault.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      noFree := available,aligned := aligned,fits := by rw [aligned];change tree.nodes.size ≤ _;omega
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_append input
  | some index =>
    have member := Array.mem_of_back? available
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input := {
      tree := tree,depth := depth
      children := GeneralBorrowStarCertificates.children tree root s.node s.star
      covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
      parentTag := s.node.tag,newTag := tag,parent := root,parentNode := s.node
      parentTagPresent := tagPresent,parentPresent := s.star.present,fresh := fresh
      index := index,available := available,valid := s.allocator.pool.bounded index member
      vacant := s.allocator.pool.vacant index member,parentSlack := slack
      offset := offset,len := len,nonzero := nonzero,well := well,bounds := bounds }
    exact default_reuse input

/-- Actual empty Shared construction retains the original root flag. -/
theorem zero_shared (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64) :
    ((GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  let P := fun after : BorrowTree => (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed
  have frame : ∀ (index : UniIndex) (mapping : UniKeyMap BorTag),
      tree.tagMapping.insert tag = .Inserted mapping index →
      (tree.nodes.insert index (GeneralBorrowFreshAnchor.sharedNode tag root)).get root = some s.node →
      P (GeneralBorrowZeroSharedState.operation tree s.node.tag tag offset).tree := by
    intro index mapping inserted parentAfter
    let stage := {(GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshAnchor.sharedNode tag root)) with tagMapping := mapping}
    have result : P (sourceUpdateSifa stage root .Read).1 := by
      have flags := sifa_flag stage root root .Read
      have old := attached_flag tree root index s.node (GeneralBorrowFreshAnchor.sharedNode tag root)
      have staged : (stage.nodes.get root).map TreeNode.isExposed = some s.node.isExposed := by
        simpa only [stage] using old
      change ((sourceUpdateSifa stage root .Read).1.nodes.get root).map TreeNode.isExposed = _
      rw [flags,staged,show tree.nodes.get root = some s.node from s.star.present]
      rfl
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

/-- Actual empty Default construction retains the original root flag. -/
theorem zero_reserve (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64) :
    ((GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree.nodes.get root).map TreeNode.isExposed =
      (tree.nodes.get root).map TreeNode.isExposed := by
  have tagged := s.allocator.nodeTags root s.node s.star.present
  let P := fun after : BorrowTree => (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed
  have frame : ∀ (index : UniIndex) (mapping : UniKeyMap BorTag),
      tree.tagMapping.insert tag = .Inserted mapping index →
      (tree.nodes.insert index (GeneralBorrowFreshDefaultChild.child tag root)).get root = some s.node →
      P (GeneralBorrowZeroDefaultState.operation tree s.node.tag tag offset).tree := by
    intro index mapping inserted parentAfter
    let stage := {(GeneralBorrowFreshGraph.attached tree index root s.node (GeneralBorrowFreshDefaultChild.child tag root)) with tagMapping := mapping}
    have result : P (sourceUpdateSifa stage root .Read).1 := by
      have flags := sifa_flag stage root root .Read
      have old := attached_flag tree root index s.node (GeneralBorrowFreshDefaultChild.child tag root)
      have staged : (stage.nodes.get root).map TreeNode.isExposed = some s.node.isExposed := by
        simpa only [stage] using old
      change ((sourceUpdateSifa stage root .Read).1.nodes.get root).map TreeNode.isExposed = _
      rw [flags,staged,show tree.nodes.get root = some s.node from s.star.present]
      rfl
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

end DuplicatePrefix.GeneralBorrowRootOnlyConstructorFlags
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyConstructorFlags." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only constructor flag dependency {dependency}"
