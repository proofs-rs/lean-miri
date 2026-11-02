import duplicate_prefix.GeneralBorrowSharedStepClosure
namespace DuplicatePrefix.GeneralBorrowTwoRootStepClosure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowExposeReadParentRead DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem parent_path (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (parentless : input.parentNode.parent = none) :
    (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat = [input.parent.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection input.tree location protections).topology input.parent.toNat).parent = none := by
    change ((source_normal_projection input.tree location protections).topology.nodes[input.parent.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node input.tree location protections input.parent.toNat input.parent input.parentNode rfl input.parentPresent]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection input.tree location protections).topology
    (source_normal_projection input.tree location protections).topology.nodes.size input.parent.toNat = _
  cases (source_normal_projection input.tree location protections).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- A complete actual two-root Read and shared constructor retains the foreign
leaf witness and selected parent's stored Unique permission in the SAME result
as the new/old Ready family. Initial data, not operation success, drive the join. -/
theorem read_append_closed (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (offset : input.offset = 0) (length : input.len = 1)
    (foreignRoot : UniIndex) (foreignNode : TreeNode)
    (initial : input.tree.locations = homogeneous 1 location)
    (roots : input.tree.roots = #[foreignRoot,input.parent]) (different : input.parent ≠ foreignRoot)
    (parentless : input.parentNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection input.tree location protections) input.parent.toNat .Read)
    (foreign : GeneralBorrowWildcardLeaf.Data input.tree location foreignRoot foreignNode input.parentNode.tag)
    (rootState : LocationState) (rootStored : location.perms.get input.parent = some rootState)
    (rootUnique : rootState.permission = .Unique)
    (frozenOthers : ∀ event ∈ ((source_normal_projection input.tree location protections).performAccess
        input.parent.toNat .Read .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → input.tree.nodeAt index = some node → index ≠ input.parent → node.isExposed = true →
      ∃ state, location.perms.get index = some state ∧ state.permission = .Frozen)
    (outside : ∀ event ∈ ((source_normal_projection input.tree location protections).topology.traverse input.parent.toNat
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection input.tree location protections) .Read)).2,
      event.node ≠ foreignRoot.toNat) :
    (GeneralBorrowExposeReadParentRead.read input protections).status = .Completed ∧ (child input protections).outcome = .ok () ∧
    ∃ postLocation postRoot requestNode postForeign,
      (child input protections).tree.locations = homogeneous 1 postLocation ∧
      Ready (child input protections).tree postLocation input.parent postRoot
        ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      (∀ (request : Request) (rootNode : TreeNode),
        Ready input.tree location input.parent rootNode request →
        ∃ nextNode, Ready (child input protections).tree postLocation input.parent postRoot
          ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag) ∧
      GeneralBorrowWildcardLeaf.Data (child input protections).tree postLocation foreignRoot postForeign postRoot.tag ∧
      (∃ state, postLocation.perms.get input.parent = some state ∧ state.permission = .Unique) ∧
      (child input protections).tree.roots = input.tree.roots ∧ postRoot.tag = input.parentNode.tag := by
  let prepared := afterReadInput input location protections offset length
  have readFacts := GeneralBorrowTwoRootUniqueParentRead.read_exact input location protections foreignRoot foreignNode
    initial roots different parentless forest owned foreign rootState rootStored rootUnique frozenOthers outside
  have childEq : child input protections = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag
      (DedupRangeMap.new (Size.ofBytes prepared.len) GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    simp only [child,readFacts.2,prepared,afterReadInput,offset,length]
  have treeEq : (child input protections).tree = result prepared := by rw [childEq];rfl
  have rootLocal : ∀ event ∈ ((source_normal_projection input.tree location protections).topology.traverse input.parent.toNat
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection input.tree location protections) .Read)).2,
      event.node = input.parent.toNat → event.relatedness = .LocalAccess := by
    intro event member same
    have classified := (GeneralBorrowTraversal.traversal_data (source_normal_projection input.tree location protections).topology
      forest input.parent.toNat owned.anchorValid .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection input.tree location protections) .Read)).2 event member
    simpa only [same,parent_path input location protections parentless,List.mem_cons,List.not_mem_nil,or_false,ite_true] using classified.2
  have readUnique := GeneralBorrowReadUnique.normal_unique input.tree location protections input.parent input.parent
    input.parentNode .VisitChildrenOfAccessed input.parentPresent ⟨rootState,rootStored,rootUnique⟩ rootLocal
  have foreignStored := GeneralBorrowTwoRootNormalAccess.normal_unvisited input.tree location protections input.parent
    foreignRoot foreignNode .Read .VisitChildrenOfAccessed foreign.present outside
  have readCache := GeneralBorrowReadNoopCache.selected_unique input.tree location input.parent protections
    .VisitChildrenOfAccessed rootState forest owned rootStored rootUnique frozenOthers
  have foreignAfter : GeneralBorrowWildcardLeaf.Data prepared.tree (readLocation input location protections)
      foreignRoot foreignNode prepared.parentNode.tag :=
    ⟨foreign.present,foreign.leaf,foreign.exposed,foreignStored.trans foreign.writable,
      by rw [show (readLocation input location protections).exposedCache = location.exposedCache from readCache];exact foreign.cache,
      foreign.boundedTag⟩
  obtain ⟨postLocation,postRoot,newNode,postForeign,locations,newReady,cache,preserved,foreignFinal,uniqueFinal,rootsFinal,tagFinal⟩ :=
    GeneralBorrowSharedStepClosure.append_closed prepared (readLocation input location protections) offset length rfl parentless
      foreignRoot foreignNode different foreignAfter readUnique
  refine ⟨readFacts.1,?_,postLocation,postRoot,newNode,postForeign,?_,?_,cache.trans readCache,?_,?_,uniqueFinal,?_,tagFinal⟩
  · rw [childEq];exact (GeneralBorrowFreshMetadataChildShared.append prepared).success
  · rw [treeEq];exact locations
  · rw [treeEq];exact newReady
  · intro request rootNode ready
    rw [treeEq]
    exact preserved request rootNode (read_ready input location protections offset length request rootNode ready)
  · rw [treeEq];exact foreignFinal
  · rw [treeEq];exact rootsFinal
end DuplicatePrefix.GeneralBorrowTwoRootStepClosure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTwoRootStepClosure." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two-root generator closure dependency {dependency}"
