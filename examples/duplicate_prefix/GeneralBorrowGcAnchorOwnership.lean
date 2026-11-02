import duplicate_prefix.GeneralBorrowGcSurvivingRootPaths
import duplicate_prefix.GeneralBorrowGcLiveRetained
import duplicate_prefix.GeneralBorrowGcOwnedPolicy
import duplicate_prefix.GeneralBorrowGcForestRootOwnership
import duplicate_prefix.GeneralBorrowExposureAncestorDistinct
namespace DuplicatePrefix.GeneralBorrowGcAnchorOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.GeneralBorrowExposureAncestorFold DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Projection ancestor paths are the real source parent walk, with its exact
fuel convention, at every present node in a parent-closed finite graph. -/
theorem path (tree : BorrowTree) (depth : ParentDepth tree.nodes) (location : LocationTree)
    (fuel : Nat) (anchor : UniIndex) (node : TreeNode) (present : tree.nodes.get anchor = some node) :
    sourceAncestorPath (source_normal_projection tree location {}).topology fuel anchor.toNat =
      (walk tree.nodes (fuel+1) anchor).map UniIndex.toNat := by
  induction fuel generalizing anchor node with
  | zero => cases edge : node.parent <;> simp [GeneralBorrowPresence.ancestor_zero,walk,present,edge]
  | succ fuel ih =>
    have projected : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology anchor.toNat).parent = node.parent.map UniIndex.toNat := by
      change ((source_normal_projection tree location {}).topology.nodes[anchor.toNat]?.getD ⟨none,[]⟩).parent = _
      rw [projection_topology_node tree location {} anchor.toNat anchor node rfl present]
    rw [GeneralBorrowPresence.ancestor_succ,projected]
    cases parent : node.parent with
    | none =>
      simp only [parent,Option.map_none]
      rw [walk,present]
      simp only [parent,List.map_cons,List.map_nil]
    | some before =>
      obtain ⟨earlier,found,_⟩ := depth.parent anchor node present before parent
      simp only [parent,Option.map_some]
      rw [walk,present]
      simp only [parent,List.map_cons]
      exact congrArg (List.cons anchor.toNat) (ih before earlier found)

private theorem topology_size (tree : BorrowTree) (location : LocationTree) :
    (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]

/-- Exact surviving source ancestry determines concrete-anchor relatedness,
independently of interval payloads or exposure cache contents. -/
theorem related (before after : BorrowTree) (beforeDepth : ParentDepth before.nodes)
    (afterDepth : ParentDepth after.nodes) (paths : GeneralBorrowGcSurvivingPaths.Relation before.nodes after.nodes)
    (metadata : GeneralBorrowGcNodeMetadata.Metadata before after)
    (anchor query : UniIndex) (node value : TreeNode)
    (present : after.nodes.get anchor = some node) (found : after.nodes.get query = some value)
    (location : LocationTree) :
    relation (source_normal_projection after location {}) anchor.toNat query.toNat =
    relation (source_normal_projection before (⟨⟨#[]⟩,{}⟩ : LocationTree) {}) anchor.toNat query.toNat := by
  obtain ⟨old,oldPresent,_⟩ := metadata anchor node present
  have beforePath := path before beforeDepth (⟨⟨#[]⟩,{}⟩ : LocationTree) before.nodes.size anchor old oldPresent
  have afterPath := path after afterDepth location after.nodes.size anchor node present
  have membership : query.toNat ∈ (walk after.nodes (after.nodes.size+1) anchor).map UniIndex.toNat ↔
      query.toNat ∈ (walk before.nodes (before.nodes.size+1) anchor).map UniIndex.toNat := by
    have injective := GeneralBorrowNodeUpdate.index_injective
    simpa only [List.mem_map,show (∃ a,a ∈ walk after.nodes (after.nodes.size+1) anchor ∧ a.toNat = query.toNat) ↔ query ∈ walk after.nodes (after.nodes.size+1) anchor from
      ⟨fun ⟨a,member,equal⟩ => (injective a query equal) ▸ member,fun member => ⟨query,member,rfl⟩⟩,
      show (∃ a,a ∈ walk before.nodes (before.nodes.size+1) anchor ∧ a.toNat = query.toNat) ↔ query ∈ walk before.nodes (before.nodes.size+1) anchor from
      ⟨fun ⟨a,member,equal⟩ => (injective a query equal) ▸ member,fun member => ⟨query,member,rfl⟩⟩] using paths anchor node present query value found
  unfold relation
  change (if query.toNat ∈ sourceAncestorPath _ _ _ then _ else _) = (if query.toNat ∈ sourceAncestorPath _ _ _ then _ else _)
  rw [topology_size,topology_size,afterPath,beforePath]
  simp only [membership]

/-- Effective range policy and exact surviving ancestry reconstruct arbitrary
Read/Write anchor ownership on the actual final byte partition. -/
theorem ownership (before after : BorrowTree) (beforeDepth : ParentDepth before.nodes)
    (afterDepth : ParentDepth after.nodes) (paths : GeneralBorrowGcSurvivingPaths.Relation before.nodes after.nodes)
    (metadata : GeneralBorrowGcNodeMetadata.Metadata before after)
    (forest : ∀ location : LocationTree, GeneralBorrowForest.Forest (source_normal_projection after location {}).topology)
    (fits : after.nodes.size ≤ 4294967296) (anchor : UniIndex) (node : TreeNode)
    (present : after.nodes.get anchor = some node) (kind : AccessKind) (lower upper : UInt64)
    (policy : GeneralBorrowGcLocalEffectivePolicy.Policy (GeneralBorrowGcOwnedPolicy.Allowed before anchor kind) lower upper after) :
    OwnedOn (GeneralBorrowRange.LocationOwned after {} anchor kind) lower upper after.locations := by
  intro position bounded positive beforeUpper afterLower
  let location := after.locations.entries[position].data
  refine ⟨⟨forest location⟩,?_,?_,?_,?_⟩
  · rw [topology_size];exact GeneralBorrowNodeUpdate.lookup_valid after.nodes anchor node present
  · exact (projection_sizes after location {}).1.trans (topology_size after location).symm
  · exact (projection_sizes after location {}).2.trans (topology_size after location).symm
  · intro index valid
    have bound : index < after.nodes.data.size := by
      change index < after.nodes.size
      rw [←topology_size after location];exact valid
    obtain ⟨query,converted,equal⟩ := index_nat index (by change after.nodes.data.size ≤ 4294967296 at fits;omega)
    have unheld : (source_normal_projection after location {}).protectedNodes.contains index = false := by
      have empty : (source_normal_projection after location {}).protectedNodes = [] := by
        unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get]
      rw [empty];rfl
    cases found : after.nodeAt query with
    | some value =>
      let state := (location.perms.get query).getD value.defaultLocationState
      refine ⟨state,projection_state after location {} index query value converted equal found,?_⟩
      have good := policy.live query value found position bounded positive beforeUpper afterLower
      have relationEq := related before after beforeDepth afterDepth paths metadata anchor query node value present found location
      rw [unheld,←equal,relationEq]
      exact good
    | none =>
      have clean := policy.vacant query found position bounded
      have foreign : relation (source_normal_projection after location {}) anchor.toNat index = .ForeignAccess := by
        unfold relation
        have notAncestor : index ∉ (source_normal_projection after location {}).topology.ancestorPath anchor.toNat := by
          intro member
          change index ∈ sourceAncestorPath _ _ _ at member
          rw [topology_size,path after afterDepth location after.nodes.size anchor node present] at member
          obtain ⟨ancestor,inWalk,same⟩ := List.mem_map.mp member
          have sameIndex : ancestor = query := GeneralBorrowNodeUpdate.index_injective ancestor query (same.trans equal.symm)
          subst ancestor
          obtain ⟨value,stored⟩ := (GeneralBorrowExposureAncestorDistinct.present_depth after.nodes afterDepth _ anchor node present query inWalk).1
          change after.nodes.get query = none at found
          rw [found] at stored
          cases stored
        simp only [notAncestor,ite_false]
      refine ⟨⟨.Disabled,false,.None⟩,?_,?_⟩
      · unfold_general_projection
        unfold NormalTreeState.stateAt
        simp only [Array.getElem?_mapIdx,converted,clean,Array.getElem?_map,Array.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]
        have absent : after.nodes.data[index] = none := by
          unfold BorrowTree.nodeAt UniValMap.get at found
          rw [equal,Array.getElem?_eq_getElem bound] at found
          exact found
        simp only [absent]
      · rw [foreign,unheld]
        cases kind <;> exact ⟨rfl,Or.inl rfl⟩
/-- FULL production GC on an arbitrary finite forest preserves any live-tagged
concrete CHILD or ROOT anchor's requested Read/Write ownership. Actual success,
anchor survival, final Forest and exact surviving ancestry are derived internally.
No post-GC ownership or retained-index premise is supplied. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (fits : tree.nodes.size ≤ 4294967296)
    (roots : ∀ root ∈ tree.roots.toList, ∃ node, tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (live : Array BorTag)
    (anchor : UniIndex) (node : TreeNode) (present : tree.nodes.get anchor = some node)
    (held : live.contains node.tag = true) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} anchor kind) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    ∃ current, (tree.removeUnreachableTags live).tree.nodes.get anchor = some current ∧ current.tag = node.tag ∧
      OwnedOn (GeneralBorrowRange.LocationOwned (tree.removeUnreachableTags live).tree {} anchor kind)
        lower upper (tree.removeUnreachableTags live).tree.locations := by
  obtain ⟨success,_,_,capacity,_,forests,_,_,metadata,_⟩ :=
    GeneralBorrowGcForestComplete.complete tree location protections forest depth closed fits roots well live
  obtain ⟨afterDepth,paths⟩ := GeneralBorrowGcSurvivingRootPaths.collect tree location protections forest depth closed fits roots well live
  obtain ⟨current,currentPresent,currentTag⟩ := GeneralBorrowGcLiveRetained.collect tree live anchor node present held
  have policy := GeneralBorrowGcOwnedPolicy.collect tree anchor kind lower upper owned clean live
  have afterFits : (tree.removeUnreachableTags live).tree.nodes.size ≤ 4294967296 := by rw [capacity];exact fits
  exact ⟨success,current,currentPresent,currentTag,ownership tree _ depth afterDepth paths metadata
    (fun loc => Classical.choice (forests loc {})) afterFits anchor current currentPresent kind lower upper policy⟩
end DuplicatePrefix.GeneralBorrowGcAnchorOwnership
