import duplicate_prefix.S05CurrentReleaseIterator
import duplicate_prefix.S05CompletedAncestryReadCapability
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.S05CompletedAncestryObserverRead
namespace DuplicatePrefix.S05CurrentReadProtectorRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

def Authority (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (selected source reader : UniIndex) (location : LocationTree) : Prop :=
 GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Nonempty (DuplicatePrefixNormalKind.Capability tree location protections reader .Read) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index →
          (Below completion index source → LocalWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
          (¬Below completion index source → ForeignWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))

private theorem capability_selected (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root reader : UniIndex)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections reader .Read) :
    ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible (CandidateStableCallOwnership.RawState location index node) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root reader readerPath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ reader.toNat normal.component
    root.toNat reader.toNat projected normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest reader.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = CandidateStableCallOwnership.RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  exact compatible

private theorem scalar (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags) (location : LocationTree)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (authority : Authority tree completion protections selected source reader location)
    (representation : LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (range : ByteRange) :
    let access := source_tree_access_at tree location (some reader) .Read protections .SkipChildrenOfAccessed range
    source_access_status access = none ∧ Authority tree completion protections selected source reader (source_access_location access) ∧
      (LocationCoherent tree (source_access_location access) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location access) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location access)) := by
  let mode := ChildrenVisitMode.SkipChildrenOfAccessed
  obtain ⟨normal⟩ := authority.2.1
  have rights := capability_selected tree location protections formed selected reader readerPath normal
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree location protections formed reader readerNode
    readerPresent normal representation.1 representation.2.1 representation.2.2 short mode
  have row := S05CompletedAncestryConcreteRead.access tree completion location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath reader readerPath rights
    (fun position root slot different index node present path below =>
      (authority.2.2 position root slot different index node present path).1 below)
    (fun position root slot different index node present path outside =>
      (authority.2.2 position root slot different index node present path).2 outside)
    representation.1 representation.2.1 authority.1 short mode range
  obtain ⟨afterNormal,componentEq⟩ := normalDone.2.2.2.2.2
  have afterRights := capability_selected tree _ protections formed selected reader readerPath afterNormal
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.size ≤ _;omega
  have cap := GeneralBorrowPhysicalNormalCapability.of_physical_component tree
    (source_access_location (source_tree_access_at tree location (some reader) .Read protections mode range))
    protections formed fits selected reader selectedNode selectedPresent parentless readerPath .Read (by
      intro index node present path
      have right := afterRights index node present path
      unfold CandidateStableCallOwnership.RawState at right
      rw [←row.2.2.2.2.1 index node present path] at right
      exact right)
  refine ⟨row.1,⟨row.2.2.2.1,cap,?_⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩⟩
  intro position root slot different index node present path
  exact ⟨row.2.2.2.2.2.1 position root slot different index node present path,
    row.2.2.2.2.2.2 position root slot different index node present path⟩

private theorem completion_locations (tree : BorrowTree) (completion : Completion)
    (locations : DedupRangeMap LocationTree) (complete : Completes tree completion) :
    Completes {tree with locations := locations} completion := by
  refine ⟨complete.1,complete.2.1,complete.2.2.1,complete.2.2.2.1,complete.2.2.2.2.1,?_,complete.2.2.2.2.2.2⟩
  intro position root slot
  have original := complete.2.2.2.2.2.1 position root slot
  by_cases zero : position = 0
  · simpa only [zero,↓reduceIte] using original
  · simp only [zero,↓reduceIte] at original ⊢
    obtain ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,path,parent⟩ := original
    exact ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := locations}) (after := tree) rfl path,parent⟩

theorem release (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (hidden : readerNode.isExposed = false) (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree reader .Read offset (offset+len))
    (owned : OwnedOn (Authority tree completion global.protectedTags selected source reader) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector readerNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn (Authority tree completion global.protectedTags selected source reader) offset (offset+len) result.tree.locations := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    (LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) ∧
    (range.start.toNat < (offset+len).toNat → offset.toNat < range.stop.toNat →
      Authority tree completion global.protectedTags selected source reader location)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩,
      fun start stop => owned position valid positive start stop⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree reader .Read offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 reader readerNode readerPresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    readerNode.tag reader readerNode readerPresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,readKind⟩ := activeRows position valid state stored accessed kind associated
      have kindEq := readKind rfl
      subst kind
      have current := rows position valid
      have result := scalar tree completion global.protectedTags tree.locations.entries[position].data complete
        runtime.formed.toGraphState depth order selectedPosition selected source reader selectedNode readerNode
        selectedSlot selectedPresent sourcePath readerPresent readerPath (current.2 start stop) current.1 short
        tree.locations.entries[position].range
      exact ⟨result.1,result.2.2,fun _ _ => result.2.1⟩)
  refine ⟨done,frame,?_,?_,capacity,?_⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector readerNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).1.2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1.1
    · intro position valid
      exact (afterRows position valid).1.2.2
  · rw [frame]
    exact completion_locations tree completion _ complete
  · intro position valid _ start stop
    exact (afterRows position valid).2 start stop

theorem release_observer (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (allocation : AllocId) (temporary : UniIndex) (temporaryNode : TreeNode)
    (readerEdge : readerNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some source)
    (hidden : readerNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (offset len : UInt64)
    (positive : offset.toNat < (offset+len).toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree reader .Read offset (offset+len))
    (owned : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧
      S05CompletedAncestryReadMutable.Authority tree completion ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector readerNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source) offset (offset+len) result.tree.locations := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    (LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) ∧
    (range.start.toNat < (offset+len).toNat → offset.toNat < range.stop.toNat →
      S05CompletedAncestryReadMutable.Authority tree completion ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location)
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid
    exact ⟨⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩,
      fun start stop => (owned position valid positive start stop).2⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree reader .Read offset (offset+len) runtime.formed.well active
  obtain ⟨depth⟩ := runtime.formed.depth
  have mapped := (complete.2.2.2.2.1 reader readerNode readerPresent).1
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    readerNode.tag reader readerNode readerPresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,readKind⟩ := activeRows position valid state stored accessed kind associated
      have kindEq := readKind rfl
      subst kind
      have current := rows position valid
      obtain ⟨readable⟩ := (owned position valid positive start stop).1
      have result := S05CompletedAncestryObserverRead.access tree completion tree.locations.entries[position].data global runtime complete
        order selectedPosition selected source reader selectedNode readerNode selectedSlot selectedPresent sourcePath readerPresent readerPath
        allocation temporary temporaryNode readerEdge temporaryPresent temporaryEdge hidden temporaryHidden readable (current.2 start stop)
        current.1.1 current.1.2.1 current.1.2.2 short .SkipChildrenOfAccessed tree.locations.entries[position].range
      exact ⟨result.1,⟨result.2.1,result.2.2.1,result.2.2.2.1⟩,fun _ _ => result.2.2.2.2⟩)
  refine ⟨done,frame,?_,?_,capacity,?_⟩
  · rw [frame]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree (tree.releaseProtector readerNode.tag global.protectedTags).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro position valid
      have profile := (afterRows position valid).1.2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro position valid
      exact (afterRows position valid).1.1
    · intro position valid
      exact (afterRows position valid).1.2.2
  · rw [frame]
    exact completion_locations tree completion _ complete
  · intro position valid _ start stop
    exact (afterRows position valid).2 start stop

end
end DuplicatePrefix.S05CurrentReadProtectorRelease
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CurrentReadProtectorRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current Read release dependency {dependency}"
