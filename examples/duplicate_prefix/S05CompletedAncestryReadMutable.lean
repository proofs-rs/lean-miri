import duplicate_prefix.S05CompletedAncestryConcreteRead
import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation
import duplicate_prefix.GeneralBorrowNormalComponentNormalization
import duplicate_prefix.GeneralBorrowRootMembership
import duplicate_prefix.GeneralBorrowConcreteRangeEntry

/-! Mutable raw authority at the selected component after a concrete Read.
The existing normal-phase Both preservation and actual callback column frame
supply the missing selected endpoint. No post-Read authority is a premise. -/
namespace DuplicatePrefix.S05CompletedAncestryReadMutable
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
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

private theorem scalar_of_normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root source : UniIndex)
    (sourcePath : Path tree root source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (kind : AccessKind) :
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible (RawState location index node) kind
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have projectedSource := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root source sourcePath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ source.toNat normal.component
    root.toNat source.toNat projectedSource normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest source.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions kind index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  exact compatible

/-- Initial raw tables derive the normal certificate; its preserved Both data
then recovers mutable rights after the actual associated Read and write-back. -/
theorem normal_read (tree : BorrowTree) (completion : Completion) (location : LocationTree)
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
        (RawState (tree.performNormalAccessAt location source .Read protections mode).location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite
        (RawState (tree.performNormalAccessAt location source .Read protections mode).location index node) (protections.contains node.tag)) := by
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion location protections complete formed depth fits
    position root source rootNode slot rootPresent sourcePath
    (fun index node present path => (authority index node present path).1)
    (fun index node present path => (authority index node present path).2)
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root source sourcePath
  obtain ⟨next,_⟩ := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves_component
    tree location protections source .Read mode fits forest projected.valid.2 normal
  exact raw_of_normal tree completion _ protections complete formed depth fits position root source rootNode
    slot rootPresent sourcePath next

/-- Full concrete Read retains mutable authority in the selected component as
well as each other-root callback component. The production traversal derives
its own normal Read compatibility and successful completion from initial data. -/
theorem access (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (complete : Completes tree completion)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePath : Path tree selected source)
    (authority : ∀ index node, tree.nodes.get index = some node →
      (Below completion index source → LocalWrite (RawState location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite (RawState location index node) (protections.contains node.tag)))
    (coherent : LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some source) .Read protections mode range
    source_access_status result = none ∧
      LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      (∀ index node, tree.nodes.get index = some node →
        (Below completion index source → LocalWrite (RawState (source_access_location result) index node) (protections.contains node.tag)) ∧
        (¬ Below completion index source → ForeignWrite (RawState (source_access_location result) index node) (protections.contains node.tag))) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion location protections complete formed depth fits
    position selected source selectedNode slot selectedPresent sourcePath
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  have completed := S05CompletedAncestryConcreteRead.access tree completion location protections complete formed depth order
    position selected source selectedNode slot selectedPresent sourcePath source sourcePath
    (scalar_of_normal tree location protections formed selected source sourcePath normal .Read)
    (fun _ _ _ _ index node present _ => (authority index node present).1)
    (fun _ _ _ _ index node present _ => (authority index node present).2)
    coherent profile possible short mode range
  have retained := normal_read tree completion location protections complete formed depth fits
    position selected source selectedNode slot selectedPresent sourcePath
    (fun index node present _ => authority index node present) mode
  refine ⟨completed.1,completed.2.1,completed.2.2.1,completed.2.2.2.1,?_⟩
  intro index node present
  obtain ⟨forest⟩ := formed.forest location protections
  have projectedSelf := GeneralBorrowPhysicalRootPath.projection_desc tree location protections index index (.refl _ node present)
  obtain ⟨root,rootNode,rootAt,parentless,member,last⟩ := GeneralBorrowRootMembership.terminal
    tree location protections forest depth formed.covered index node present projectedSelf.valid.1
  obtain ⟨rootPosition,rootSlot⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp member)
  let topology := (source_normal_projection tree location protections).topology
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
    tree location protections fits root rootNode rootAt index.toNat projectedPath
  have actualEq : actual = index := by
    cases actual;cases index
    simp only [UniIndex.toNat] at actualIndex
    congr
    exact UInt32.toNat_inj.mp actualIndex
  subst actual
  by_cases same : root = selected
  · subst root
    unfold RawState
    rw [completed.2.2.2.2.1 index node present path]
    exact retained index node present path
  · exact ⟨completed.2.2.2.2.2.1 rootPosition root rootSlot same index node present path,
      completed.2.2.2.2.2.2 rootPosition root rootSlot same index node present path⟩

/-- Mutable authority relative to the SAME completed source, for every actual
node of one row. It is unchanged by Read; no claim of general Joint simulation
or preservation under protector insertion is made. -/
def Authority (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source : UniIndex) (location : LocationTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    (Below completion index source → LocalWrite (RawState location index node) (protections.contains node.tag)) ∧
    (¬Below completion index source → ForeignWrite (RawState location index node) (protections.contains node.tag))

/-- The actual range iterator preserves initial mutable authority on its owned
window, including split segments and the selected component. It derives every
Read callback's completion; no future table or successful access is supplied. -/
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
      (tree.performBorrowAccessRange (.concrete sourceNode.tag) offset len .Read protections mode) := by
  have mapped : tree.indexOfTag sourceNode.tag = some source :=
    (complete.2.2.2.2.1 source sourceNode sourcePresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections sourceNode.tag source mapped offset len .Read mode
    _ _ _ _ (fun _ authority => authority) (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := access tree completion location protections complete formed depth order position selected source selectedNode
    slot selectedPresent sourcePath authority.2 representation.1 representation.2.1 authority.1 short mode range
  exact ⟨row.1,⟨row.2.2.2.1,row.2.2.2.2⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩

end DuplicatePrefix.S05CompletedAncestryReadMutable

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryReadMutable." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved mutable Read endpoint dependency {dependency}"
