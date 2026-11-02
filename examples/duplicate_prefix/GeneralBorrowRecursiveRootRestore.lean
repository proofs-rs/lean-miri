import duplicate_prefix.GeneralBorrowRecursiveSharedGeneration
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
import duplicate_prefix.GenericAsMutPtrEntryValidity

namespace DuplicatePrefix.GeneralBorrowRecursiveRootRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- The original parentless mutable root persists while generated descendants
become read-only. These are data facts, never operation-success assumptions. -/
structure RootFacts {root : UniIndex} {offset len : UInt64} (s : State root offset len) (tag : BorTag) : Prop where
  present : ∃ node, s.tree.nodeAt root = some node ∧ node.tag = tag
  path : ∀ location : LocationTree, (source_normal_projection s.tree location {}).topology.ancestorPath root.toNat = [root.toNat]
  ancestor : ∀ location : LocationTree, root.toNat ∈ (source_normal_projection s.tree location {}).topology.ancestorPath s.parent.toNat
  writable : s.writable root.toNat = true
  protections : s.protections = {}

private theorem parentless_path (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (location : LocationTree)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- The checked partition seed supplies root facts internally. -/
theorem of_partition (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : GeneralBorrowPartitionState.State tree root capacity) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    RootFacts (GeneralBorrowRecursiveSharedGeneration.of_partition tree root capacity s offset len bounds) s.node.tag := by
  refine ⟨⟨s.node,s.star.present,rfl⟩,?_,?_,rfl,rfl⟩
  · intro location;exact parentless_path tree root s.node location s.star.present s.star.parentless
  · intro location
    have path := parentless_path tree root s.node location s.star.present s.star.parentless
    change root.toNat ∈ (source_normal_projection tree location {}).topology.ancestorPath root.toNat
    rw [path];simp

/-- A real unprotected shared stage preserves the old root and its mutable
label, while its new child is appended to the actual ancestor path. -/
theorem next_facts {root : UniIndex} {offset len : UInt64} (s : State root offset len) (rootTag tag : BorTag)
    (facts : RootFacts s rootTag) (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag)
    (nonzero : len ≠ 0) (room : s.tree.nodes.size+5 ≤ 4294967295) :
    RootFacts (next s tag fresh nonzero false room) rootTag := by
  let d := supplied s tag fresh nonzero
  obtain ⟨node,present,tagged⟩ := facts.present
  have retained := GeneralBorrowFreshSharedStagePaths.old_node s.tree tag s.parent offset len d s.protections false s.writable s.owned root node present
  obtain ⟨after,presentAfter,tagAfter,exposed⟩ := retained
  have vacant : s.tree.nodes.get (index d) = none := GeneralBorrowFreshSharedWithinStages.slot_vacant s.tree d.depth s.parent d.slot
  have different : root ≠ index d := GeneralBorrowFreshReuseNode.parent_not_vacant s.tree.nodes (index d) root node vacant present
  have differentNat : root.toNat ≠ (index d).toNat := fun equal => different (GeneralBorrowNodeUpdate.index_injective root (index d) equal)
  have valid := GeneralBorrowNodeUpdate.lookup_valid s.tree.nodes root node present
  refine ⟨⟨after,presentAfter,tagAfter.trans tagged⟩,?_,?_,?_,?_⟩
  · intro location
    have attached := GeneralBorrowFreshSharedStageAttachAny.attach s.tree tag s.parent offset len d s.protections false s.writable s.owned location location {}
    have oldSize : (source_normal_projection s.tree location {}).topology.nodes.size = s.tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    have previous := attached.oldPath root.toNat (by rw [oldSize];exact valid) differentNat
    exact previous.trans (facts.path location)
  · intro location
    have attached := GeneralBorrowFreshSharedStageAttachAny.attach s.tree tag s.parent offset len d s.protections false s.writable s.owned location location {}
    change root.toNat ∈ (source_normal_projection (child d s.protections false).tree location {}).topology.ancestorPath (index d).toNat
    rw [attached.childPath]
    exact List.mem_cons_of_mem _ (facts.ancestor location)
  · change (GeneralBorrowFreshMixedChild.extend s.writable (index d).toNat) root.toNat = true
    simp only [GeneralBorrowFreshMixedChild.extend,ite_eq_right differentNat]
    exact facts.writable
  · change registered s.protections tag false = {}
    exact facts.protections

/-- Every unprotected generated descendant chain retains the original mutable
root's data facts. The Read/constructor successes remain conclusions of Run. -/
theorem Run.root_facts {root : UniIndex} {offset len : UInt64} {nonzero : len ≠ 0}
    {initial final : State root offset len} {steps : List (BorTag × Bool)}
    (history : Run nonzero initial steps final) (rootTag : BorTag) (initialFacts : RootFacts initial rootTag)
    (unprotected : ∀ step ∈ steps, step.2 = false) : RootFacts final rootTag := by
  induction history with
  | nil => exact initialFacts
  | cons s tag held rest fresh room readDone childDone active tail ih =>
    have flag := unprotected (tag,held) (by simp)
    change held = false at flag
    subst held
    apply ih (next_facts s rootTag tag initialFacts fresh nonzero room)
    intro step member
    exact unprotected step (by simp [member])

/-- Mixed readonly ancestor labels suffice to restore the ORIGINAL root's
Write ownership: only the retained root remains local and writable; all leaving
shared ancestors are actually unprotected. -/
theorem owned {root : UniIndex} {offset len : UInt64} (s : State root offset len) (rootTag : BorTag)
    (facts : RootFacts s rootTag) :
    OwnedOn (GeneralBorrowRange.LocationOwned s.tree {} root .Write) offset (offset+len) s.tree.locations := by
  obtain ⟨node,present,tagged⟩ := facts.present
  have restore : GeneralBorrowFreshLifetimeRestore.RestoreTo s.tree {} {} s.parent root s.writable := by
    refine ⟨GeneralBorrowNodeUpdate.lookup_valid s.tree.nodes root node present,?_,?_⟩
    · intro location position localAccess
      have member : position ∈ (source_normal_projection s.tree location {}).topology.ancestorPath root.toNat := by
        unfold GeneralBorrowAnchor.relation at localAccess
        split at localAccess
        next member => exact member
        next => cases localAccess
      rw [facts.path location] at member
      have equal : position = root.toNat := List.mem_singleton.mp member
      subst position
      refine ⟨?_,facts.writable⟩
      unfold GeneralBorrowAnchor.relation
      simp only [facts.ancestor location,ite_true]
    · intro location position sourceLocal targetForeign
      have empty : (source_normal_projection s.tree location {}).protectedNodes = [] := by
        unfold_general_projection
        simp [ProtectedTags.contains,ProtectedTags.get]
      rw [empty];rfl
  apply GeneralBorrowFreshLifetimeRestore.restore_owned_on s.tree {} {} (fun _ given => given) s.parent root s.writable restore
  rw [←facts.protections]
  exact s.owned

/-- Form generic retag-entry Data at the original root after arbitrarily deep
shared generation. Canonical rank compression derives the real append/reuse
Slot; graph, allocator, vacant Clean and restored ownership are internal. -/
noncomputable def entryData {root : UniIndex} {offset len : UInt64} (s : State root offset len) (rootTag tag : BorTag)
    (facts : RootFacts s rootTag) (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) :
    GenericAsMutPtrEntryValidity.Data s.tree {} rootTag tag offset len := by
  let node := Classical.choose facts.present
  have present := (Classical.choose_spec facts.present).1
  have tagged := (Classical.choose_spec facts.present).2
  change node.tag = rootTag at tagged
  let depth := GeneralBorrowCanonicalParentDepth.normalize s.tree.nodes s.resources.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned s.tree s.resources.allocator.accounting
  have fits : s.tree.tagMapping.deassigned.back? = none → s.tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty;rw [aligned empty]
    have room := s.resources.room
    change s.tree.nodes.data.size+4 ≤ _ at room
    omega
  exact {
    parent := root,root := root,node := node,depth := depth
    children := s.resources.children,parentPresent := present,roots := s.resources.roots,covered := s.resources.covered
    tagPresent := by
      change s.tree.tagMapping.get rootTag = some root
      simpa only [tagged] using s.resources.allocator.nodeTags root node present
    tagFresh := fresh
    protectorFresh := by
      intro row member same
      have recorded := (GeneralBorrowFreshReuseProtection.entries_get s.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := s.resources.allocator.nodeTags row.1 row.2 recorded
      have absent : s.tree.tagMapping.get tag = none := by
        unfold UniKeyMap.get;rw [GeneralBorrowTagMap.fresh_find s.tree.tagMapping tag fresh];rfl
      rw [same,absent] at lookup
      cases lookup
    nodeFits := by have room := s.resources.room;change s.tree.nodes.data.size+4 ≤ _ at room;omega
    slot := GeneralBorrowCanonicalParentDepth.slot s.tree s.resources.depth root node present s.resources.allocator.pool aligned fits
    well := s.resources.well
    owned := owned s rootTag facts }

/-- Actual allocation initializes the original mutable root facts. -/
theorem allocation_facts (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) :
    RootFacts (GeneralBorrowRecursiveSharedGeneration.allocation capacity nonzero rootTag resourceTag different) rootTag :=
  of_partition (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag resourceTag different)) 0 capacity (by simp)

/-- Actual allocation and any finite unprotected descendant chain derive the
original root's mutable retag-entry Data internally. The final shared descendant
is NOT treated as mutable. Initial graph/ownership/resources, final root facts,
intermediate Data and successful operations are not input premises. -/
theorem generate_entry (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (steps : List (BorTag × Bool))
    (unique : (steps.map Prod.fst).Nodup) (rootUnused : rootTag ∉ steps.map Prod.fst)
    (tagUnused : tag ∉ steps.map Prod.fst) (unprotected : ∀ step ∈ steps, step.2 = false)
    (room : 1+steps.length+4 ≤ 4294967295) :
    let initial := GeneralBorrowRecursiveSharedGeneration.allocation capacity nonzero rootTag tag different
    ∃ final : State GeneralBorrowFullSharedSeed.root 0 capacity,
      Run nonzero initial steps final ∧ height final = steps.length+1 ∧
      RootFacts final rootTag ∧
      OwnedOn (GeneralBorrowRange.LocationOwned final.tree {} GeneralBorrowFullSharedSeed.root .Write) 0 capacity final.tree.locations ∧
      Nonempty (GenericAsMutPtrEntryValidity.Data final.tree {} rootTag tag 0 capacity) := by
  dsimp only
  obtain ⟨final,history,depth,bound,active,future⟩ := GeneralBorrowRecursiveSharedGeneration.generate capacity nonzero rootTag tag different steps unique rootUnused room
  have facts := Run.root_facts history rootTag (allocation_facts capacity nonzero rootTag tag different) unprotected
  refine ⟨final,history,depth,facts,?_,⟨entryData final rootTag tag facts (future tag tagUnused different)⟩⟩
  simpa only [UInt64.zero_add] using owned final rootTag facts

end DuplicatePrefix.GeneralBorrowRecursiveRootRestore
