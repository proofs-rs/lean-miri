import duplicate_prefix.S05CompletedWriteAuthorityRoots
import duplicate_prefix.S05CompletedAncestryConcreteWrite
namespace DuplicatePrefix.S05CompletedWriteAuthorityConcrete
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open S05CompletedAncestryReadMutable (Authority)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem raw_of_normal (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (complete : Completes tree completion)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (slot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections source) :
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source → LocalWrite (RawState location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite (RawState location index node) (protections.contains node.tag)) := by
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 position root slot
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  have projectedSource := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root source sourcePath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ source.toNat normal.component
    root.toNat source.toNat projectedSource normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest source.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions .Write index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  have physical := CompletedBorrowPhysicalSource.same_root_ancestor_iff complete rootPresent parentless present path sourcePath
  have related := GeneralBorrowProjectedDescPath.relation_local_iff tree location protections fits depth forest
    source index sourceNode node sourcePresent present
  constructor
  · intro below
    rw [related.mpr (physical.mp below)] at compatible
    exact compatible
  · intro outside
    have relation : GeneralBorrowAnchor.relation (source_normal_projection tree location protections)
        source.toNat index.toNat = .ForeignAccess := by
      cases current : GeneralBorrowAnchor.relation (source_normal_projection tree location protections)
          source.toNat index.toNat with
      | LocalAccess => exact False.elim (outside (physical.mpr (related.mp current)))
      | ForeignAccess => rfl
    rw [relation] at compatible
    exact compatible

/-- Initial raw tables derive the normal certificate; its preserved Both data
then recovers mutable rights after the actual matching Write and write-back. -/
theorem normal_write (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (complete : Completes tree completion)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (slot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (authority : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source → LocalWrite (RawState location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite (RawState location index node) (protections.contains node.tag)))
    (mode : ChildrenVisitMode) :
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source → LocalWrite
        (RawState (tree.performNormalAccessAt location source .Write protections mode).location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite
        (RawState (tree.performNormalAccessAt location source .Write protections mode).location index node) (protections.contains node.tag)) := by
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion location protections complete formed depth fits
    position root source rootNode slot rootPresent sourcePath
    (fun index node present path => (authority index node present path).1)
    (fun index node present path => (authority index node present path).2)
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root source sourcePath
  obtain ⟨next,_⟩ := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves_component
    tree location protections source .Write mode fits forest projected.valid.2 normal
  exact raw_of_normal tree completion _ protections complete formed depth fits position root source rootNode
    slot rootPresent sourcePath next

theorem access (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial)
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧
      LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source (source_access_location result) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion initial protections complete formed depth fits
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode
    selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  obtain ⟨forest⟩ := formed.forest initial protections
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections)
      source.toNat .Write normal.component := by
    intro index inside valid
    have size : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←size];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root slot different index node present path
    have data := Array.getElem?_eq_some_iff.mp slot
    have member : root ∈ tree.roots.toList := by
      rw [←data.2];exact Array.mem_toList_iff.mpr (Array.getElem_mem data.1)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent
      normal rootPath member (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have normalRights := normal_write tree completion initial protections complete formed depth fits
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath
    (fun index node present _ => authority index node present) mode
  have currentAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source
      (tree.performNormalAccessAt initial source .Write protections mode).location := by
    intro index node present
    obtain ⟨forest⟩ := formed.forest initial protections
    have projectedSelf := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections index index (.refl _ node present)
    obtain ⟨root,rootNode,rootAt,parentless,member,last⟩ := GeneralBorrowRootMembership.terminal
      tree initial protections forest depth formed.covered index node present projectedSelf.valid.1
    obtain ⟨rootPosition,rootSlot⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp member)
    let topology := (source_normal_projection tree initial protections).topology
    have nonempty : topology.ancestorPath index.toNat ≠ [] :=
      GeneralBorrowTerminal.ancestors_nonempty topology topology.nodes.size index.toNat
    have ending : (topology.ancestorPath index.toNat).getLast? = some root.toNat := by
      have lastValue : (topology.ancestorPath index.toNat).getLast! =
          (topology.ancestorPath index.toNat).getLast nonempty := by
        rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty];rfl
      rw [lastValue] at last
      rw [List.getLast?_eq_some_getLast nonempty,last]
    have projectedPath := GeneralBorrowPhysicalRootPath.selected_desc topology forest index.toNat root.toNat
      projectedSelf.valid.1 ending
    obtain ⟨actual,actualNode,actualIndex,actualAt,path⟩ := GeneralBorrowProjectedDescPath.desc_path
      tree initial protections fits root rootNode rootAt index.toNat projectedPath
    have actualEq : actual = index := by
      cases actual;cases index
      simp only [UniIndex.toNat] at actualIndex
      congr
      exact UInt32.toNat_inj.mp actualIndex
    subst actual
    by_cases same : root = selected
    · subst root
      exact normalRights index node present path
    · unfold RawState
      rw [frame rootPosition root rootSlot same index node present path]
      exact authority index node present
  have final := S05CompletedWriteAuthorityRoots.roots tree completion protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath short
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Write protections mode).location normalDone.2.2 afterProfile afterPossible currentAuthority
  have path : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans path
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  exact final


theorem range (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : Path tree selected source)
    (offset len : Size) (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧ Authority tree completion protections source location)
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : GeneralRangeMapState.Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧ Authority tree completion protections source location)
      (fun location => LocationCoherent tree location protections ∧ GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
      (fun _ _ => True) lower upper
      (tree.performBorrowAccessRange (.concrete sourceNode.tag) offset len .Write protections mode) := by
  have mapped : tree.indexOfTag sourceNode.tag = some source :=
    (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections sourceNode.tag source mapped offset len .Write mode
    _ _ _ _ (fun _ authority => authority) (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := access tree completion location protections complete formed depth order position selected source selectedNode
    slot selectedPresent sourcePath authority.2 representation.1 representation.2.1 authority.1 short mode range
  exact ⟨row.1,⟨row.2.2.2.1,row.2.2.2.2⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩


end DuplicatePrefix.S05CompletedWriteAuthorityConcrete
