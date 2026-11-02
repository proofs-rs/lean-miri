import duplicate_prefix.GeneralBorrowFullSharedResources

namespace DuplicatePrefix.GeneralBorrowGeneratedStarShape
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowFreshMetadata
open DuplicatePrefix.GeneralBorrowFullSharedRead
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Exact sparse star topology: one parentless root and all other present nodes
are distinct root children with no descendants. Permissions are independent. -/
structure Star (tree : BorrowTree) (root : UniIndex) (rootNode : TreeNode) : Prop where
  present : tree.nodeAt root = some rootNode
  parentless : rootNode.parent = none
  leaves : ∀ query node, tree.nodeAt query = some node → query ≠ root →
    node.parent = some root ∧ node.children = #[]
  distinct : rootNode.children.toList.Nodup
  children : ∀ query, query ∈ rootNode.children.toList ↔
    query ≠ root ∧ ∃ node, tree.nodeAt query = some node

theorem locations (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (good : Star tree root node) (map : DedupRangeMap LocationTree) :
    Star {tree with locations := map} root node :=
  ⟨good.present,good.parentless,good.leaves,good.distinct,good.children⟩

theorem of_nodes (before after : BorrowTree) (root : UniIndex) (node : TreeNode)
    (same : after.nodes = before.nodes) (good : Star before root node) : Star after root node := by
  refine ⟨?_,good.parentless,?_,good.distinct,?_⟩
  · change after.nodes.get root = some node
    rw [same];exact good.present
  · intro query value present different
    change after.nodes.get query = some value at present
    rw [same] at present
    exact good.leaves query value present different
  · intro query
    change query ∈ node.children.toList ↔ query ≠ root ∧ ∃ value, after.nodes.get query = some value
    rw [same];exact good.children query

/-- Transport exact star topology through the metadata view preserved by SIFA. -/
theorem shaped (before after : BorrowTree) (root : UniIndex) (node : TreeNode)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (good : Star before root node) : ∃ next, Star after root next := by
  obtain ⟨next,present,tag,parent,children,permission⟩ := node_fields before after same root node good.present
  refine ⟨next,present,parent.trans good.parentless,?_,?_,?_⟩
  · intro query value found different
    obtain ⟨old,oldPresent,_,oldParent,oldChildren,_⟩ := node_fields after before same.symm query value found
    have facts := good.leaves query old oldPresent different
    exact ⟨oldParent.symm.trans facts.1,oldChildren.symm.trans facts.2⟩
  · rw [children];exact good.distinct
  · intro query
    rw [children,good.children]
    constructor
    · rintro ⟨different,old,found⟩
      obtain ⟨value,present,_⟩ := node_exists before after same query old found
      exact ⟨different,value,present⟩
    · rintro ⟨different,value,found⟩
      obtain ⟨old,present,_⟩ := node_exists after before same.symm query value found
      exact ⟨different,old,present⟩

/-- Actual append-stage node mutations extend a star by one fresh leaf. -/
theorem attached_star (tree : BorrowTree) (root : UniIndex) (rootNode : TreeNode)
    (index : UniIndex) (leaf : TreeNode) (good : Star tree root rootNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parent : leaf.parent = some root)
    (empty : leaf.children = #[]) :
    Star (attached tree index root rootNode leaf) root (updatedParent rootNode index) := by
  have notNew : root ≠ index := parent_not_fresh tree.nodes index root rootNode atEnd good.present
  refine ⟨parent_lookup tree index root rootNode leaf atEnd good.present,good.parentless,?_,?_,?_⟩
  · intro query node present different
    by_cases fresh : query = index
    · subst query
      rw [new_lookup tree index root rootNode leaf atEnd good.present] at present
      cases present
      exact ⟨parent,empty⟩
    · rw [other_lookup tree index root query rootNode leaf atEnd good.present different fresh] at present
      exact good.leaves query node present different
  · simp only [updatedParent,Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨good.distinct,by simp,?_⟩
    intro query member other singleton equal
    have same : other = index := by simpa only [List.mem_singleton] using singleton
    obtain ⟨node,present⟩ := (good.children query).mp member |>.2
    have valid := lookup_valid tree.nodes query node present
    rw [equal,same,atEnd] at valid
    omega
  · intro query
    simp only [updatedParent,Array.toList_push,List.mem_append,List.mem_singleton]
    constructor
    · intro member
      rcases member with old | fresh
      · obtain ⟨different,node,present⟩ := (good.children query).mp old
        exact ⟨different,old_present tree index root query rootNode leaf node atEnd good.present present⟩
      · subst query
        exact ⟨Ne.symm notNew,leaf,new_lookup tree index root rootNode leaf atEnd good.present⟩
    · rintro ⟨different,node,present⟩
      by_cases fresh : query = index
      · exact Or.inr fresh
      · rw [other_lookup tree index root query rootNode leaf atEnd good.present different fresh] at present
        exact Or.inl ((good.children query).mpr ⟨different,node,present⟩)

attribute [local irreducible] GeneralBorrowFreshMetadataChildShared.result GeneralBorrowFreshMetadataChildShared.stage

/-- A real shared append retains exact star topology after the actual SIFA. -/
theorem append_star (input : Input) (good : Star input.tree input.parent input.parentNode) :
    ∃ node, Star (result input) input.parent node := by
  have known := attached_star input.tree input.parent input.parentNode (index input)
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) good (at_end input) rfl rfl
  have nodesEq : (stage input).nodes =
      (attached input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)).nodes := by
    unfold stage GeneralBorrowFreshMetadataChildAttach.staged
    rfl
  have staged := of_nodes _ (stage input) input.parent (updatedParent input.parentNode (index input)) nodesEq known
  exact shaped (stage input) (result input) input.parent (updatedParent input.parentNode (index input)) (shape input) staged

/-- Distinct present child indices fit in the actual sparse node capacity. -/
theorem children_bound (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (good : Star tree root node) : node.children.size ≤ tree.nodes.size := by
  have mapped : (node.children.toList.map UniIndex.toNat).Nodup :=
    good.distinct.map UniIndex.toNat (fun left right different same => different (index_injective left right same))
  have subset : node.children.toList.map UniIndex.toNat ⊆ List.range tree.nodes.size := by
    intro position member
    obtain ⟨query,queryMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨value,present⟩ := (good.children query).mp queryMember |>.2
    exact List.mem_range.mpr (lookup_valid tree.nodes query value present)
  simpa only [List.length_map,Array.length_toList,List.length_range] using mapped.length_le_of_subset subset

/-- Actual allocation has precisely the root and no leaf. -/
theorem seed_star (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    Star seed.tree seed.parent seed.parentNode := by
  let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
  have only : ∀ query node, seed.tree.nodeAt query = some node → query = seed.parent := by
    intro query node present
    have valid := lookup_valid seed.tree.nodes query node present
    change query.toNat < (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.data.size at valid
    rw [GeneralBorrowFullSharedSeed.tree_eq] at valid
    change query.toNat < 1 at valid
    apply index_injective query seed.parent
    change query.toNat = 0
    omega
  refine ⟨seed.parentPresent,rfl,?_,by exact List.nodup_nil,?_⟩
  · intro query node present different
    exact False.elim (different (only query node present))
  · intro query
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨different,node,present⟩
      exact False.elim (different (only query node present))

/-- Any history successor Input with the actual child tree and retained slice
length inherits the full generator State and exact star. Its offset is forced
to zero by the retained capacity and its own explicit range bounds. -/
theorem successor (input : Input) (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode) (next : Input)
    (tree : next.tree = (child input {}).tree) (parent : next.parent = input.parent)
    (length : next.len = input.len) :
    ∃ postLocation, State next postLocation ∧ Star next.tree next.parent next.parentNode := by
  obtain ⟨forest⟩ := good.forest
  let prepared := afterReadInput input location {} good.offset
  have readFacts := GeneralBorrowFullSharedRead.read_closed input location good.offset
    good.locations good.roots good.parentless forest good.profile
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput]
  have childTree : (child input {}).tree = result prepared := by rw [actualChild];unfold result;rfl
  have preparedStar : Star prepared.tree prepared.parent prepared.parentNode :=
    ⟨star.present,star.parentless,star.leaves,star.distinct,star.children⟩
  obtain ⟨rootNode,postStar⟩ := append_star prepared preparedStar
  have nextPresent : (result prepared).nodeAt input.parent = some next.parentNode := by
    rw [←childTree,←tree,←parent]
    exact next.parentPresent
  have sameNode : next.parentNode = rootNode := Option.some.inj (nextPresent.symm.trans postStar.present)
  have nextStar : Star next.tree next.parent next.parentNode := by
    rw [tree,childTree,parent,sameNode]
    exact postStar
  have metadata := GeneralBorrowFreshMetadataChildShared.append prepared
  obtain ⟨postLocation,locations,profile,cache⟩ := GeneralBorrowFullSharedAppend.append prepared
    (readLocation input location {}) good.offset rfl good.parentless readFacts.2.2.1
  have capacity : next.tree.locations.size.bytes = input.len := by
    rw [tree,childTree,locations]
    simp [RangeMapNonempty.homogeneous,DedupRangeMap.size,prepared,afterReadInput,Size.ofBytes]
  have offset : next.offset = 0 := by
    apply UInt64.toNat_inj.mp
    have bounds := next.bounds
    rw [capacity,length] at bounds
    change next.offset.toNat = 0
    omega
  have postForest := GeneralBorrowFreshTopology.extended_forest _ _ prepared.parent.toNat
    (metadata.extension (readLocation input location {}) postLocation {}) forest
  refine ⟨postLocation,⟨offset,?_,?_,nextStar.parentless,?_,?_⟩,nextStar⟩
  · rw [length,tree,childTree];exact locations
  · rw [tree,childTree,metadata.roots,parent];exact good.roots
  · rw [tree,childTree];exact ⟨postForest⟩
  · rw [tree,childTree,parent];exact profile

/-- Every actual completed Run beginning in a generator star retains its
State and star; intermediate successful operations are read from the Run,
not assumed by the allocation-to-history theorem. -/
theorem run_star {input final : Input} {tags : List BorTag}
    (history : GeneralBorrowFullSharedRepeat.Run input tags final)
    (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode) :
    ∃ finalLocation, State final finalLocation ∧ Star final.tree final.parent final.parentNode := by
  induction history generalizing location with
  | nil => exact ⟨location,good,star⟩
  | cons readDone childDone tree parent newTag length tail ih =>
    obtain ⟨postLocation,nextGood,nextStar⟩ := successor _ location good star _ tree parent length
    exact ih postLocation nextGood nextStar

end DuplicatePrefix.GeneralBorrowGeneratedStarShape
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGeneratedStarShape.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated star-shape dependency {dependency}"
