import duplicate_prefix.GeneralBorrowExposureFoldShape
import duplicate_prefix.GeneralBorrowGeneratedExposureReady
import duplicate_prefix.GeneralBorrowExposedStarWrite
import duplicate_prefix.GeneralBorrowExposedPartitionState
namespace DuplicatePrefix.GeneralBorrowExposedStarFormation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Source-derived exposure endpoint, with cache, permission and recurring
ownership facts kept explicit rather than forgotten behind shape equality. -/
structure Output (input : Input) where
  requests : List Request
  tree : BorrowTree
  location : LocationTree
  node : TreeNode
  leaves : requests.map Request.leaf = input.parentNode.children.toList
  leavesDone : (run {} requests input.tree).outcome = .ok ()
  rootEq : (run {} requests input.tree).tree.exposeTag {} input.parentTag = ⟨tree,.ok ()⟩
  locations : tree.locations = RangeMapNonempty.homogeneous input.len location
  star : Star tree input.parent node
  profile : GeneralBorrowSharedGeneratorProfile.Profile tree location input.parent
  exposed : ∀ index node,tree.nodeAt index = some node → node.isExposed = true
  counts : GeneralBorrowWriteCardinality.Counts location.exposedCache input.parent node.children.toList
  state : GeneralBorrowPartitionState.State tree input.parent input.len

/-- All endpoint facts follow from actual leaf/root exposure operations. Initial
cache/flag data are intermediate premises, discharged by allocation histories. -/
theorem form (input : Input) (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode)
    (allocator : GeneralBorrowGcAllocator.Invariant input.tree) (room : input.tree.nodes.size+4 ≤ 4294967295)
    (unexposed : GeneralBorrowSharedUnexposed.Unexposed input.tree) (emptyCache : location.exposedCache = {})
    (short : input.parentNode.children.size+1 < 65536) : Nonempty (Output input) := by
  obtain ⟨requests,leaves,ready⟩ := GeneralBorrowGeneratedExposureReady.requests input.tree location input.parent input.parentNode
    star good.profile allocator.nodeTags unexposed
  have distinct : (requests.map Request.leaf).Nodup := by rw [leaves];exact star.distinct
  have known : ∀ request ∈ requests,∃ node,input.tree.nodeAt request.leaf = some node :=
    fun request member => ⟨request.node,(ready request member).present⟩
  let after := pureRun input.len input.parent requests input.tree location
  have actual := run_eq requests input.tree location input.len input.parent input.parentNode {} good.locations ready distinct
  have leafShape := GeneralBorrowExposureFoldShape.pure_shape requests input.tree location input.len input.parent good.locations
    (fun request member => ⟨request.node,(ready request member).present,rfl⟩)
  have leafProfile := GeneralBorrowExposureFoldFlags.profile requests input.tree location input.len input.parent good.profile known
  have frame := GeneralBorrowExposedLeavesRoot.root_frame requests input.tree location input.len input.parent
    (fun request member => (ready request member).different)
  have rootPresent : after.1.nodeAt input.parent = some input.parentNode := frame.1.trans input.parentPresent
  have tagged : after.1.indexOfTag input.parentTag = some input.parent := by
    change after.1.tagMapping.get input.parentTag = some input.parent
    rw [frame.2];exact input.parentTagPresent
  have rootStored : ∃ state,after.2.perms.get input.parent = some state ∧ state.permission = .Unique :=
    ⟨GeneralBorrowWildcardLeaf.unique,leafProfile.rootStored,rfl⟩
  have actualRoot := GeneralBorrowUniqueRootExposure.expose after.1 input.parentTag input.parent input.parentNode after.2 input.len {}
    tagged rootPresent good.parentless (unexposed _ _ input.parentPresent) rootStored
    (GeneralBorrowStarExposureCounts.pure_locations requests input.tree location input.len input.parent good.locations)
  let postLocation := {after.2 with exposedCache := GeneralBorrowUniqueRootExposure.bump after.2.exposedCache input.parent}
  let postTree := {(marked after.1 input.parent input.parentNode) with locations := RangeMapNonempty.homogeneous input.len postLocation}
  have sourceRoot : after.1.exposeTag {} input.parentTag = ⟨postTree,.ok ()⟩ := actualRoot
  have depth := GeneralBorrowFreshMetadata.parent_depth input.tree after.1 leafShape input.depth
  have rootFacts := GeneralBorrowRootExposureFrame.expose after.1 input.parentTag input.parent input.parentNode tagged rootPresent depth
    (unexposed _ _ input.parentPresent) {}
  rw [sourceRoot] at rootFacts
  have postShape : GeneralBorrowView.treeShape postTree = GeneralBorrowView.treeShape input.tree := rootFacts.2.1.trans leafShape
  obtain ⟨node,postStar⟩ := GeneralBorrowGeneratedStarShape.shaped input.tree postTree input.parent input.parentNode postShape star
  have nodeChildren : node.children = input.parentNode.children := by
    obtain ⟨node2,present,tag,parent,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields input.tree postTree postShape input.parent input.parentNode input.parentPresent
    have same : node = node2 := Option.some.inj (postStar.present.symm.trans present)
    rw [same];exact children
  have markedProfile := GeneralBorrowExposureFoldFlags.mark_profile after.1 after.2 input.parent input.parentNode leafProfile
  have postProfile : GeneralBorrowSharedGeneratorProfile.Profile postTree postLocation input.parent :=
    ⟨markedProfile.rootStored,markedProfile.shared,markedProfile.vacant⟩
  have exposed : ∀ index node,postTree.nodeAt index = some node → node.isExposed = true :=
    GeneralBorrowExposureFoldFlags.mark_all after.1 input.parent input.parentNode
      (GeneralBorrowExposureFoldFlags.all_nonroot requests input.tree location input.len input.parent input.parentNode star leaves known)
  have counted := GeneralBorrowStarExposureCounts.pure_counts requests input.tree location input.len input.parent []
    (by rw [emptyCache];exact GeneralBorrowStarExposureCounts.empty input.parent)
    (fun request member => (ready request member).different)
    (by have length := congrArg List.length leaves;simp only [List.length_map,Array.length_toList] at length;simp only [List.length_nil,Nat.zero_add];omega)
  simp only [List.append_nil] at counted
  have postCount := GeneralBorrowWriteCardinality.root_exposed after.2.exposedCache input.parent _ counted
    (by have length := congrArg List.length leaves;simp only [List.length_map,Array.length_toList] at length;simp only [List.length_reverse,List.length_map];omega)
  have reindexed : GeneralBorrowWriteCardinality.Counts postLocation.exposedCache input.parent node.children.toList := by
    apply GeneralBorrowWriteCacheCardinality.counts_perm _ _ _ _ postCount
    rw [nodeChildren,←leaves]
    exact List.reverse_perm _
  let initialState := GeneralBorrowPartitionState.of_reusable input.tree input.parent input.len
    (GeneralBorrowReusableStar.of_generated input location good star allocator room)
  obtain ⟨state,taggedState⟩ := Classical.choice (GeneralBorrowExposedPartitionState.of_shape input.tree postTree input.parent input.len initialState postShape)
  exact ⟨⟨requests,postTree,postLocation,node,leaves,by rw [actual],
    by rw [actual];exact sourceRoot,rfl,postStar,postProfile,exposed,reindexed,state⟩⟩
end DuplicatePrefix.GeneralBorrowExposedStarFormation
