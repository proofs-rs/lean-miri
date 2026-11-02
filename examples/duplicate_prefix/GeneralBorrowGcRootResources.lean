import duplicate_prefix.GeneralBorrowGcRootWrite
import duplicate_prefix.GeneralBorrowGcFullClean
import duplicate_prefix.GeneralBorrowForestFunctionSafety
import duplicate_prefix.GeneralBorrowTerminal
import duplicate_prefix.GeneralBorrowFreshDefaultPathData

namespace DuplicatePrefix.GeneralBorrowGcRootResources
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

abbrev after (tree : BorrowTree) (live : Array BorTag) : BorrowTree := (tree.removeUnreachableTags live).tree

/-- A singleton real ancestor path in a finite Forest certifies that the actual
source node is parentless, without assuming a root metadata field. -/
theorem parentless (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (location : LocationTree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (present : tree.nodes.get root = some node)
    (path : (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat]) : node.parent = none := by
  have valid : root.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  have terminal := GeneralBorrowTerminal.ancestor_terminal (source_normal_projection tree location {}).topology forest root.toNat valid
  rw [path] at terminal
  change (((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩)).parent = none at terminal
  rw [projection_topology_node tree location {} root.toNat root node rfl present] at terminal
  cases edge : node.parent with
  | none => rfl
  | some parent => simp only [edge,Option.map_some] at terminal;cases terminal

structure Collected (tree : BorrowTree) (root : UniIndex) (rootTag tag : BorTag) (offset len : UInt64)
    (reserve : Fin 5 → BorTag) (live : Array BorTag) where
  resources : GeneralBorrowRecursiveSharedResources.Resources (after tree live) root
  node : TreeNode
  present : (after tree live).nodes.get root = some node
  tagged : node.tag = rootTag
  parentless : node.parent = none
  owned : OwnedOn (GeneralBorrowRange.LocationOwned (after tree live) {} root .Write) offset (offset+len) (after tree live).locations
  fresh : GeneralBorrowTagMap.Fresh (after tree live).tagMapping tag
  reserved : ∀ index, GeneralBorrowTagMap.Fresh (after tree live).tagMapping (reserve index)
  completed : (tree.removeUnreachableTags live).outcome = .ok ()
  capacity : (after tree live).locations.size = tree.locations.size

/-- Actual full GC internally rebuilds all recursive allocator/graph/Clean
resources, root Write ownership, next-tag freshness and reservations. Original
finite graph and ownership are data inputs to this helper; generation endpoints
form them from real allocation/constructor histories. -/
def collect (tree : BorrowTree) (root : UniIndex) (rootTag tag : BorTag) (offset len : UInt64)
    (resources : GeneralBorrowRecursiveSharedResources.Resources tree root)
    (node : TreeNode) (present : tree.nodes.get root = some node) (tagged : node.tag = rootTag) (rootless : node.parent = none)
    (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) offset (offset+len) tree.locations)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (reserve : Fin 5 → BorTag)
    (reserved : ∀ index, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve index)) (live : Array BorTag) :
    Collected tree root rootTag tag offset len reserve live := by
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  let forest := GeneralBorrowFreshDefaultPathData.forest_of_owned tree {} root offset len nonzero resources.well bounds owned location {}
  have fits : tree.nodes.size ≤ 4294967296 := by have room := resources.room;omega
  have rootNodes : ∀ index ∈ tree.roots.toList, ∃ current, tree.nodes.get index = some current ∧ current.parent = none := by
    intro index member
    rw [resources.roots] at member
    have same : index = root := by simpa using member
    subst index
    exact ⟨node,present,rootless⟩
  have complete := GeneralBorrowGcForestComplete.complete tree location {} forest resources.depth resources.children fits rootNodes resources.well live
  have rootResult := GeneralBorrowGcRootWrite.collect tree location {} forest resources.depth resources.children fits
    rootNodes resources.well live root node present rootless (by rw [resources.roots];simp) offset (offset+len) owned resources.clean
  let current := Classical.choose rootResult.2
  have currentFacts := Classical.choose_spec rootResult.2
  have success := rootResult.1
  have currentPresent := currentFacts.1
  have currentParent := currentFacts.2.1
  have currentTag := currentFacts.2.2.1
  have currentOwned := currentFacts.2.2.2
  have frame := GeneralBorrowGcResourceFrame.preserves reserve tree live reserved
  have one := GeneralBorrowGcResourceFrame.preserves (n := 1) (fun _ => tag) tree live (fun _ => fresh)
  exact {
    resources := {
      depth := Classical.choice complete.2.2.2.2.1
      children := complete.2.2.2.2.2.2.1
      covered := GeneralBorrowGcNodeMetadata.roots_cover tree live resources.covered
      roots := frame.roots.trans resources.roots
      allocator := GeneralBorrowGcAllocatorFull.preserves tree live resources.allocator
      clean := GeneralBorrowGcFullClean.preserves tree live resources.clean
      well := complete.2.1
      room := by rw [frame.capacity];exact resources.room }
    node := current,present := currentPresent,tagged := currentTag.trans tagged,parentless := currentParent
    owned := currentOwned,fresh := one.fresh 0,reserved := frame.fresh,completed := success,capacity := complete.2.2.1 }

/-- Form the real next FnEntry Data from the actual collected resources and
root ownership; append/reuse choice and every freshness fact are internal. -/
def entryData {tree : BorrowTree} {root : UniIndex} {rootTag tag : BorTag} {offset len : UInt64}
    {reserve : Fin 5 → BorTag} {live : Array BorTag} (s : Collected tree root rootTag tag offset len reserve live) :
    GenericAsMutPtrEntryValidity.Data (after tree live) {} rootTag tag offset len := by
  let current := after tree live
  let depth := GeneralBorrowCanonicalParentDepth.normalize current.nodes s.resources.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned current s.resources.allocator.accounting
  have fits : current.tagMapping.deassigned.back? = none → current.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty;rw [aligned empty]
    have room := s.resources.room
    change current.nodes.data.size+4 ≤ _ at room
    omega
  exact {
    parent := root,root := root,node := s.node,depth := depth
    children := s.resources.children,parentPresent := s.present,roots := s.resources.roots,covered := s.resources.covered
    tagPresent := by
      change current.tagMapping.get rootTag = some root
      simpa only [s.tagged] using s.resources.allocator.nodeTags root s.node s.present
    tagFresh := s.fresh
    protectorFresh := by
      intro row member same
      have recorded := (GeneralBorrowFreshReuseProtection.entries_get current.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := s.resources.allocator.nodeTags row.1 row.2 recorded
      have absent : current.tagMapping.get tag = none := by
        unfold UniKeyMap.get;rw [GeneralBorrowTagMap.fresh_find current.tagMapping tag s.fresh];rfl
      rw [same,absent] at lookup
      cases lookup
    nodeFits := by
      have room : current.nodes.data.size+4 ≤ 4294967295 := s.resources.room
      change current.nodes.data.size ≤ 4294967296
      omega
    slot := GeneralBorrowCanonicalParentDepth.slot current s.resources.depth root s.node s.present s.resources.allocator.pool aligned fits
    well := s.resources.well,owned := s.owned }

end
end DuplicatePrefix.GeneralBorrowGcRootResources
