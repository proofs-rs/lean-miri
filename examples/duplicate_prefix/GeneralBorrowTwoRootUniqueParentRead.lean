import duplicate_prefix.GeneralBorrowExposeReadParentRead
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowReadNoopCache
namespace DuplicatePrefix.GeneralBorrowTwoRootUniqueParentRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowExposeReadParentRead
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem parent_path (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (parentless : input.parentNode.parent = none) :
    ((source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat).getLast! = input.parent.toNat := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection input.tree location protections).topology input.parent.toNat).parent = none := by
    change ((source_normal_projection input.tree location protections).topology.nodes[input.parent.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node input.tree location protections input.parent.toNat input.parent input.parentNode rfl input.parentPresent]
    simp only [parentless,Option.map_none]
  change (sourceAncestorPath (source_normal_projection input.tree location protections).topology
    (source_normal_projection input.tree location protections).topology.nodes.size input.parent.toNat).getLast! = input.parent.toNat
  cases (source_normal_projection input.tree location protections).topology.nodes.size with
  | zero => rfl
  | succ fuel =>
    rw [GeneralBorrowPresence.ancestor_succ,parent]
    rfl

/-- The actual one-byte parent Read traverses the normal parent component and
then the exposed foreign leaf at root position zero. Both successes are derived. -/
theorem read_exact (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (foreignRoot : UniIndex) (foreignNode : TreeNode)
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
    (GeneralBorrowExposeReadParentRead.read input protections).status = .Completed ∧
    (GeneralBorrowExposeReadParentRead.read input protections).tree = {input.tree with locations := homogeneous 1 (readLocation input location protections)} := by
  have normalGood := GeneralBorrowNormalLocation.normal_succeeds input.tree location protections input.parent .Read
    .VisitChildrenOfAccessed forest owned input.depth input.children input.parentNode input.parentPresent
  have rootEq : (input.tree.performNormalAccessAt location input.parent .Read protections .VisitChildrenOfAccessed).access.root = input.parent.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection input.tree location protections)).trans
      (parent_path input location protections parentless)
  have foreignStored := GeneralBorrowTwoRootNormalAccess.normal_unvisited input.tree location protections input.parent
    foreignRoot foreignNode .Read .VisitChildrenOfAccessed foreign.present outside
  have cache := GeneralBorrowReadNoopCache.selected_unique input.tree location input.parent protections
    .VisitChildrenOfAccessed rootState forest owned rootStored rootUnique frozenOthers
  have afterData : GeneralBorrowWildcardLeaf.Data input.tree
      (readLocation input location protections) foreignRoot foreignNode input.parentNode.tag :=
    ⟨foreign.present,foreign.leaf,foreign.exposed,foreignStored.trans foreign.writable,
      by rw [show (readLocation input location protections).exposedCache = location.exposedCache from cache];exact foreign.cache,
      foreign.boundedTag⟩
  have normalPresent : input.tree.nodes.get input.parent = some input.parentNode := input.parentPresent
  have wildcard := GeneralBorrowWildcardLeaf.access input.tree _ foreignRoot foreignNode input.parentNode.tag .Read protections afterData
  dsimp only [readLocation] at wildcard
  have access : source_access_location (source_tree_access_at input.tree location (some input.parent) .Read protections .VisitChildrenOfAccessed ⟨0,1⟩) =
      readLocation input location protections ∧
      source_access_status (source_tree_access_at input.tree location (some input.parent) .Read protections .VisitChildrenOfAccessed ⟨0,1⟩) = none := by
    simp_tree_helpers
    simp only [normalGood.1,normalGood.2,rootEq,index_self]
    simp only [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      show #[foreignRoot,input.parent].size = 2 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
      show List.range' 0 2 = [0,1] from rfl]
    simp [List.forIn_cons,List.forIn_nil,wildcard,bind,pure,normalPresent,different,readLocation]
  have tagged : input.tree.indexOfTag input.parentTag = some input.parent := input.parentTagPresent
  unfold GeneralBorrowExposeReadParentRead.read BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,initial]
  have zero : Size.ofBytes 0 = Size.ZERO := rfl
  rw [zero,iter_mut_homogeneous_full (1 : UInt64) location (by decide)]
  simp only [Array.size_singleton,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous (1 : UInt64) location) 0 (by change 0<1;decide)]
  simp only [access.1,access.2]
  constructor
  · trivial
  · rfl

/-- A full actual two-root parent Read with an optionally exposed Unique parent and shared append forms the new Ready
leaf and retains every prior Ready sibling and the exact exposure cache.
The exposed foreign Unique leaf/cache conditions concern the initial state;
no operation success or constructor post-state is supplied as an assumption. -/
theorem read_append_ready (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
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
    ∃ postLocation postRoot requestNode,
      (child input protections).tree.locations = homogeneous 1 postLocation ∧
      Ready (child input protections).tree postLocation input.parent postRoot
        ⟨input.newTag,index input,requestNode⟩ ∧
      postLocation.exposedCache = location.exposedCache ∧
      ∀ (request : Request) (rootNode : TreeNode),
        Ready input.tree location input.parent rootNode request →
        ∃ nextNode, Ready (child input protections).tree postLocation input.parent postRoot
          ⟨request.tag,request.leaf,nextNode⟩ ∧ nextNode.tag = request.node.tag := by
  let prepared := afterReadInput input location protections offset length
  have readFacts := read_exact input location protections foreignRoot foreignNode initial roots different parentless forest owned foreign rootState rootStored rootUnique frozenOthers outside
  have childEq : child input protections = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag
      (DedupRangeMap.new (Size.ofBytes prepared.len) GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    simp only [child,readFacts.2,prepared,afterReadInput,offset,length]
  have treeEq : (child input protections).tree = result prepared := by rw [childEq];rfl
  have built := GeneralBorrowExposeReadFormation.append_ready_preserves prepared
    (readLocation input location protections) offset length rfl parentless
  obtain ⟨postLocation,postRoot,newNode,locations,newReady,cacheEq,preserved⟩ := built
  have readCache := GeneralBorrowReadNoopCache.selected_unique input.tree location input.parent protections
    .VisitChildrenOfAccessed rootState forest owned rootStored rootUnique frozenOthers
  refine ⟨readFacts.1,?_,postLocation,postRoot,newNode,?_,?_,cacheEq.trans readCache,?_⟩
  · rw [childEq]
    exact (GeneralBorrowFreshMetadataChildShared.append prepared).success
  · rw [treeEq];exact locations
  · rw [treeEq];exact newReady
  · intro request rootNode ready
    rw [treeEq]
    exact preserved request rootNode (read_ready input location protections offset length request rootNode ready)
end DuplicatePrefix.GeneralBorrowTwoRootUniqueParentRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTwoRootUniqueParentRead." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two-root parent Read dependency {dependency}"
