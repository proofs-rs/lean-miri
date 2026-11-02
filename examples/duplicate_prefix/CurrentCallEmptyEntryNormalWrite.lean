import duplicate_prefix.CurrentCallEmptyEntryRootLoop
import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation
import duplicate_prefix.CandidateCurrentWindowAuthority

/-! Current Bool Normal Both survives the actual selected normal Write and
other-root callbacks. The empty-effect consumer derives the callback factory;
no completed ancestry or additional caller capability is imposed. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryNormalWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Extract actual selected-component scalar rights from the current Normal
certificate and a separately derived physical ancestry classification. -/
theorem raw_of_normal (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (root source : UniIndex) (sourcePath : Path tree root source)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source ↔ Path tree index source))
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections source) :
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source → LocalWrite (RawState location index node) (protections.contains node.tag)) ∧
      (¬ Below completion index source → ForeignWrite (RawState location index node) (protections.contains node.tag)) := by
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
  have physical := classification index node present path
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

theorem write (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree selected source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (callback : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ current : LocationTree,LocationCoherent tree current protections →
      GeneralBorrowLocationSifaConsistency.Profile tree current protections →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current →
      (∀ index node,tree.nodes.get index = some node → Path tree root index → current.perms.get index = initial.perms.get index) →
      let result := tree.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
      result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      ∀ query,¬Path tree root query → result.location.perms.get query = current.perms.get query)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) protections source) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨actual,actualAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have actualEq : actual = selectedNode := Option.some.inj (actualAt.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  have fits : tree.nodes.data.size ≤ 4294967296 := formed.fits
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections) source.toNat .Write normal.component := by
    intro index inside valid
    have sizes : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←sizes];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex),tree.roots[position]? = some root → root ≠ selected →
      ∀ index node,tree.nodes.get index = some node → Path tree root index →
      (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root rootAt different index node present path
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent normal rootPath member
      (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have currentNormal := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal
  have final := CurrentCallEmptyEntryRootLoop.roots tree initial protections formed distinct selectedPosition selected selectedSlot
    (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row protections source)) (some selectedNode.tag) .Write
    (fun position root rootAt different current retained cache sifa gp currentFrame => by
      obtain ⟨done,outCache,outProfile,outPossible,outside⟩ := callback position root rootAt different current cache sifa gp currentFrame
      obtain ⟨oldNormal⟩ := retained
      have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
      obtain ⟨nextNormal,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree current _ protections formed
        source selected root sourceNode sourcePresent oldNormal rootPath member (Ne.symm different) (Path tree root)
        (fun _ path => path.present)
        (fun query path => GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path) outside
      exact ⟨done,outCache,outProfile,outPossible,outside,⟨nextNormal⟩⟩)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Write protections mode).location currentNormal normalDone.2.2 afterProfile afterPossible frame
  have ending : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩)

theorem write_authority (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree selected source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      (Below completion index source ↔ Path tree index source))
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (callback : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ current : LocationTree, S05CompletedAncestryReadMutable.Authority tree completion protections source current →
      LocationCoherent tree current protections →
      GeneralBorrowLocationSifaConsistency.Profile tree current protections →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current →
      (∀ index node,tree.nodes.get index = some node → Path tree root index → current.perms.get index = initial.perms.get index) →
      let result := tree.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
      result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,¬Path tree root query → result.location.perms.get query = current.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) protections source) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source (source_access_location result) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨actual,actualAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have actualEq : actual = selectedNode := Option.some.inj (actualAt.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  have fits : tree.nodes.data.size ≤ 4294967296 := formed.fits
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections) source.toNat .Write normal.component := by
    intro index inside valid
    have sizes : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←sizes];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex),tree.roots[position]? = some root → root ≠ selected →
      ∀ index node,tree.nodes.get index = some node → Path tree root index →
      (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root rootAt different index node present path
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent normal rootPath member
      (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have currentNormal := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal
  obtain ⟨currentNormal⟩ := currentNormal
  have currentAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source
      (tree.performNormalAccessAt initial source .Write protections mode).location := by
    have selectedRights := raw_of_normal tree completion _ protections formed depth fits selected source sourcePath classification currentNormal
    intro index node present
    obtain ⟨position,root,rootNode,rootAt,rootPresent,path⟩ := CandidateCurrentWindowAuthority.root_path tree formed index node present
    by_cases same : root = selected
    · subst root
      exact selectedRights index node present path
    · unfold RawState
      rw [frame position root rootAt same index node present path]
      exact authority index node present
  have final := CurrentCallEmptyEntryRootLoop.roots tree initial protections formed distinct selectedPosition selected selectedSlot
    (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row protections source) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source row) (some selectedNode.tag) .Write
    (fun position root rootAt different current retained cache sifa gp currentFrame => by
      obtain ⟨done,outCache,outProfile,outPossible,outside,outAuthority⟩ := callback position root rootAt different current retained.2 cache sifa gp currentFrame
      obtain ⟨oldNormal⟩ := retained.1
      have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
      obtain ⟨nextNormal,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree current _ protections formed
        source selected root sourceNode sourcePresent oldNormal rootPath member (Ne.symm different) (Path tree root)
        (fun _ path => path.present)
        (fun query path => GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path) outside
      exact ⟨done,outCache,outProfile,outPossible,outside,⟨⟨nextNormal⟩,outAuthority⟩⟩)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Write protections mode).location ⟨⟨currentNormal⟩,currentAuthority⟩ normalDone.2.2 afterProfile afterPossible frame
  have ending : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩)

end DuplicatePrefix.CurrentCallEmptyEntryNormalWrite
