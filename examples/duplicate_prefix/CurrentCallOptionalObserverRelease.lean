import duplicate_prefix.CurrentCallOptionalReadQueries
import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.S05CurrentReadProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor

/-! Actual helper Read release with an optional parent interpretation. The
source's full authority is demanded only under its literal future protector
flags, while the protected helper retains its current Read capability. -/
namespace DuplicatePrefix.CurrentCallOptionalObserverRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open BorrowRangeAccess GeneralRangeMapOrigins GeneralRangeMapState CurrentCallResourceNormalization
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

private theorem same_root_ancestor {tree completion} (model : ParentInterpretation tree completion)
    {root query source : UniIndex} {rootNode queryNode : TreeNode}
    (rootAt : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (queryAt : tree.nodes.get query = some queryNode) (queryPath : Path tree root query)
    (sourcePath : Path tree root source) (below : Below completion query source) : Path tree query source := by
  rcases model.physical_or_attachment queryAt below with physical | attachment
  · exact physical
  · obtain ⟨origin,next,originNode,nextNode,path,originAt,_,nextAt,nextNone,edge,after⟩ := attachment
    have nextRoot : Below completion next root := by
      rcases model.physical_suffix sourcePath after with above | physicalNext
      · exact above
      · have same := CompletedBorrowAncestry.physical_roots_unique rootAt parentless nextAt nextNone
          physicalNext (.refl _ nextNode nextAt)
        subst next
        exact .refl root
    have rootOrigin := model.physical_below (CompletedBorrowAncestry.path_trans queryPath path)
    have before := UInt64.le_iff_toNat_le.mp (model.tag_le rootAt originAt rootOrigin)
    have afterTag := UInt64.le_iff_toNat_le.mp (model.tag_le nextAt rootAt nextRoot)
    obtain ⟨actual,actualAt,_,older⟩ := model.virtual_parent nextAt nextNone edge
    have same := Option.some.inj (originAt.symm.trans actualAt)
    subst actual
    have strict := UInt64.lt_iff_toNat_lt.mp older
    omega

private theorem normal_of_authority (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source ↔ Path tree index source))
    (localRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree initial protections source) := by
  obtain ⟨actual,found,parentless⟩ := formed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have rootValid : root.toNat < topology.nodes.size := projectedPath.valid.1
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  change (topology.nodes[root.toNat]?.getD ⟨none,[]⟩) = _ at projectedRoot
  have rootShape : topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'rootValid).parent = none := by
    rw [rootShape];simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro kind slot inside _
  change Desc topology root.toNat slot at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent slot inside
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  let state := (initial.perms.get index).getD node.defaultLocationState
  refine ⟨state,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    have physical := classification index node present path
    have related := GeneralBorrowProjectedDescPath.relation_local_iff tree initial protections fits depth forest
      source index sourceNode node sourcePresent present
    by_cases localPath : Path tree index source
    · rw [related.mpr localPath]
      exact OrdinaryBorrowAuthorityBridge.local_scalar state _ (localRights index node present path (physical.mpr localPath)) kind
    · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections)
          source.toNat index.toNat = .ForeignAccess := by
        cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat with
        | LocalAccess => exact False.elim (localPath (related.mp relation))
        | ForeignAccess => rfl
      rw [foreignRelation]
      have raw := foreignRights index node present path (fun below => localPath (physical.mp below))
      obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step state _ kind raw
      exact (DuplicatePrefixScalarAuthorization.compatible_iff state kind .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩

private theorem finish (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (model : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot)
    (distinct : tree.roots.toList.Nodup)
    (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (slot : tree.roots[position]?=some selected) (selectedPresent : tree.nodes.get selected=some selectedNode)
    (sourcePath : Path tree selected source) (readerPresent : tree.nodeAt reader=some readerNode)
    (readerPath : Path tree selected reader)
    (future : ProtectedTags) (readable : DuplicatePrefixNormalKind.Capability tree initial global.protectedTags reader .Read)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion future source initial)
    (flags : ∀ (p : Nat) (root : UniIndex),tree.roots[p]?=some root → root≠selected → ∀ index node,
      tree.nodes.get index=some node → Path tree root index → future.contains node.tag=global.protectedTags.contains node.tag)
    (coherent : LocationCoherent tree initial global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size<65536) (mode : ChildrenVisitMode) (range : ByteRange)
    (next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location future source) :
    let result := source_tree_access_at tree initial (some reader) .Read global.protectedTags mode range
    source_access_status result=none ∧ LocationCoherent tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      S05CompletedAncestryReadMutable.Authority tree completion future source (source_access_location result) := by
  obtain ⟨depth⟩ := runtime.formed.depth
  let formed := runtime.formed.toGraphState
  obtain ⟨rootNode,rootAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have rootEq : rootNode=selectedNode := Option.some.inj (rootAt.symm.trans selectedPresent)
  subst rootNode
  have classification : ∀ index node,tree.nodes.get index=some node → Path tree selected index →
      (Below completion index source ↔ Path tree index source) := by
    intro index node present path
    exact ⟨same_root_ancestor model selectedPresent parentless present path sourcePath,model.physical_below⟩
  have selectedRights := CurrentCallEmptyEntryNormalWrite.raw_of_normal tree completion _ future formed depth runtime.formed.fits
    selected source sourcePath classification next
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree initial global.protectedTags formed reader readerNode
    readerPresent readable coherent profile possible short mode
  have rootPath := S05CompletedAncestryNormal.root_path tree initial global.protectedTags formed selected reader selectedNode
    selectedPresent parentless readerPath
  have frame : ∀ (p : Nat) (root : UniIndex),tree.roots[p]?=some root → root≠selected → ∀ index node,
      tree.nodes.get index=some node → Path tree root index →
      (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location.perms.get index=initial.perms.get index := by
    intro p root slot different index node present path
    exact (GeneralBorrowNormalOtherRootFrame.access_kind tree initial global.protectedTags formed reader selected root readerNode
      readerPresent .Read readable rootPath (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
      (Ne.symm different) coherent mode).2.2.2 index node present path
  have initialAuthority : S05CompletedAncestryReadMutable.Authority tree completion future source
      (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location := by
    intro index node present
    obtain ⟨p,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree formed index node present
    by_cases same : root=selected
    · subst root;exact selectedRights index node present path
    · unfold RawState
      rw [frame p root slot same index node present path]
      exact authority index node present
  have selectedSlot := slot
  have final := CurrentCallEmptyEntryRootLoop.roots tree initial global.protectedTags formed distinct
    position selected slot (S05CompletedAncestryReadMutable.Authority tree completion future source) (some selectedNode.tag) .Read
    (by
      intro p root slot different current retained cache sifa gp currentFrame
      obtain ⟨done,_,outCache,outSifa,outPossible,_,outside,localRight,foreignRight⟩ :=
        CurrentCallOptionalReadQueries.access_root_preserves (primaryBelow:=primaryBelow) (primarySlot:=primarySlot)
          tree completion current global.protectedTags model depth model.order p position root selected source selectedNode
          slot selectedSlot selectedPresent different sourcePath
          (by intro index node present path below;rw [←flags p root slot different index node present path];exact (retained index node present).1 below)
          (by intro index node present path below;rw [←flags p root slot different index node present path];exact (retained index node present).2 below)
          formed cache short sifa gp
      refine ⟨done,outCache,outSifa,outPossible,outside,?_⟩
      intro index node present
      by_cases path : Path tree root index
      · rw [flags p root slot different index node present path]
        exact ⟨localRight index node present path,foreignRight index node present path⟩
      · unfold RawState
        rw [outside index path]
        exact retained index node present)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree reader else none) mode range
    (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location initialAuthority
    normalDone.2.2.1 normalDone.2.2.2.1 normalDone.2.2.2.2.1 frame
  have ending : ((source_normal_projection tree initial global.protectedTags).topology.ancestorPath reader.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).access.root=selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree initial global.protectedTags)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩)

theorem access_two (tree : BorrowTree) (completion : Completion) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (_order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePath : Path tree selected source) (readerPresent : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree selected reader)
    (allocation : AllocId) (temporary : UniIndex) (temporaryNode : TreeNode)
    (readerEdge : readerNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some source)
    (readerHidden : readerNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (readable : DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read)
    (authority : Authority tree completion
      ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location)
    (coherent : LocationCoherent tree location global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some reader) .Read global.protectedTags mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Authority tree completion
        ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
          (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source (source_access_location result) := by
  let first := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
  let second := first.endCall (({} : FrameState).addProtector allocation temporaryNode.tag)
  obtain ⟨firstRuntime,_,firstOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime allocation
    readerNode.tag reader readerNode readerPresent rfl readerHidden
  obtain ⟨secondRuntime,_,secondOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree first firstRuntime allocation
    temporaryNode.tag temporary temporaryNode temporaryPresent rfl temporaryHidden
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨selectedActual,selectedAt,selectedNone⟩ := complete.graph.rootNodes selected
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have selectedEq : selectedActual=selectedNode := Option.some.inj (selectedAt.symm.trans selectedPresent)
  subst selectedActual
  have classification : ∀ index node,tree.nodes.get index=some node → Path tree selected index →
      (Below completion index source ↔ Path tree index source) := by
    intro index node present path
    exact ⟨same_root_ancestor complete selectedPresent selectedNone present path sourcePath,complete.physical_below⟩
  obtain ⟨normal⟩ := normal_of_authority tree completion location second.protectedTags runtime.formed.toGraphState
    depth runtime.formed.fits position selected source selectedNode slot selectedPresent sourcePath classification
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  obtain ⟨_,_,next,_⟩ := GeneralBorrowObserverReadTwoParents.access tree location global runtime allocation reader temporary source
    readerNode temporaryNode readerPresent readerEdge temporaryPresent temporaryEdge readerHidden temporaryHidden readable normal mode
  apply finish tree completion location global runtime complete primarySlot distinct position selected source reader selectedNode readerNode
    primaryBelow slot selectedPresent sourcePath readerPresent readerPath second.protectedTags readable authority _ coherent profile possible short mode range next
  intro p root rootSlot different index node present path
  obtain ⟨rootNode,rootPresent,parentless⟩ := complete.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  obtain ⟨selectedActual,found,selectedParentless⟩ := complete.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have selectedEq := Option.some.inj (found.symm.trans selectedPresent)
  subst selectedActual
  have temporaryPath : Path tree selected temporary := .step sourcePath temporaryNode temporaryPresent temporaryEdge
  have distinctTag (other : UniIndex) (otherNode : TreeNode) (otherPresent : tree.nodeAt other = some otherNode)
      (otherPath : Path tree selected other) : node.tag ≠ otherNode.tag := by
    intro same
    have one := runtime.formed.allocator.nodeTags index node present
    have two := runtime.formed.allocator.nodeTags other otherNode otherPresent
    rw [same,two] at one
    have eq := Option.some.inj one
    subst other
    exact different (CompletedBorrowAncestry.physical_roots_unique rootPresent parentless selectedPresent selectedParentless path otherPath)
  have firstEq := firstOther node.tag (distinctTag reader readerNode readerPresent readerPath)
  have secondEq := secondOther node.tag (distinctTag temporary temporaryNode temporaryPresent temporaryPath)
  change (second.protectedTags.get node.tag).isSome = (global.protectedTags.get node.tag).isSome
  rw [secondEq,firstEq]

theorem release_two (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
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
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ ParentInterpretation result.tree completion ∧
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
  have mapped := runtime.formed.allocator.nodeTags reader readerNode readerPresent
  obtain ⟨done,frame,afterRows,well,ranges,capacity⟩ := S05CurrentReleaseIterator.release tree global.protectedTags
    readerNode.tag reader readerNode readerPresent hidden mapped P rows runtime.formed.well (by
      intro position valid state stored accessed kind associated
      obtain ⟨start,stop,readKind⟩ := activeRows position valid state stored accessed kind associated
      have kindEq := readKind rfl
      subst kind
      have current := rows position valid
      obtain ⟨readable⟩ := (owned position valid positive start stop).1
      have result := access_two tree completion tree.locations.entries[position].data global runtime complete primarySlot distinct
        order selectedPosition selected source reader selectedNode readerNode primaryBelow selectedSlot selectedPresent sourcePath readerPresent readerPath
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
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ complete.graph,
      complete.order,complete.dimension,complete.physical,complete.edgeLive,complete.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := complete.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := (tree.releaseProtector readerNode.tag global.protectedTags).tree.locations})
        (after := tree) rfl path⟩
  · intro position valid _ start stop
    exact (afterRows position valid).2 start stop

/-- Actual helper release followed by its exact SINGLE whole-frame endCall flags. -/
theorem release (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
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
    (helperFrame : FrameState)
    (frameOwned : helperFrame.protectedTags=#[(allocation,readerNode.tag)])
    (temporaryUnheld : global.protectedTags.contains temporaryNode.tag=false)
    (owned : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧
      S05CompletedAncestryReadMutable.Authority tree completion (global.endCall helperFrame).protectedTags source location) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) :
    let result := tree.releaseProtector readerNode.tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ ParentInterpretation result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree completion (global.endCall helperFrame).protectedTags source) offset (offset+len) result.tree.locations ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree (global.endCall helperFrame) := by
  let first := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
  have firstAbsent : first.protectedTags.contains temporaryNode.tag=false := by
    cases found : first.protectedTags.contains temporaryNode.tag with
    | false => rfl
    | true =>
      have old := GeneralBorrowRelease.end_call_weakens global (({} : FrameState).addProtector allocation readerNode.tag) temporaryNode.tag found
      rw [temporaryUnheld] at old
      contradiction
  have inert : first.protectedTags.remove temporaryNode.tag=first.protectedTags := by
    unfold ProtectedTags.remove
    have filter : first.protectedTags.entries.filter (fun row=>row.1 != temporaryNode.tag)=first.protectedTags.entries := by
      apply Array.filter_eq_self.mpr
      intro row member
      have different : row.1≠temporaryNode.tag := by
        intro same
        have held := (GeneralBorrowRelease.contains_iff_entry first.protectedTags temporaryNode.tag).mpr ⟨row,member,same⟩
        rw [firstAbsent] at held
        contradiction
      simpa using different
    rw [filter]
  have secondSame : first.endCall (({} : FrameState).addProtector allocation temporaryNode.tag)=first := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
    exact congrArg (fun table=>{first with protectedTags:=table}) inert
  have firstSame : first=global.endCall helperFrame := by
    simp [first,GlobalState.endCall,frameOwned,FrameState.addProtector]
  have futureEq : ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
      (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags=(global.endCall helperFrame).protectedTags :=
    congrArg GlobalState.protectedTags (secondSame.trans firstSame)
  have ownedTwo : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧
      Authority tree completion ((global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location)
      offset (offset+len) tree.locations := by simpa only [futureEq] using owned
  obtain ⟨done,frame,afterRuntime,parents,capacity,afterOwned⟩ := release_two tree global completion runtime complete primarySlot distinct
    order selectedPosition selected source reader selectedNode readerNode primaryBelow selectedSlot selectedPresent sourcePath
    readerPresent readerPath allocation temporary temporaryNode readerEdge temporaryPresent temporaryEdge hidden temporaryHidden
    offset len positive active ownedTwo short
  have readerAt : (tree.releaseProtector readerNode.tag global.protectedTags).tree.nodeAt reader=some readerNode := by
    rw [frame];exact readerPresent
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame (tree.releaseProtector readerNode.tag global.protectedTags).tree helperFrame := by
    intro row member index node present sameTag
    rw [frameOwned] at member
    have sameRow : row=(allocation,readerNode.tag) := by simpa using member
    subst row
    have one := afterRuntime.formed.allocator.nodeTags index node present
    have two := afterRuntime.formed.allocator.nodeTags reader readerNode readerAt
    rw [sameTag,two] at one
    have sameIndex := Option.some.inj one
    subst index
    have sameNode := Option.some.inj (present.symm.trans readerAt)
    subst node
    exact hidden
  refine ⟨done,frame,afterRuntime,parents,capacity,?_,S05CompletedChildReanchor.runtime_end_call _ global helperFrame afterRuntime hiddenFrame⟩
  rw [frame]
  intro position valid positive start stop index node present
  have original := afterOwned position valid positive start stop index node present
  simpa only [futureEq] using original


end
end DuplicatePrefix.CurrentCallOptionalObserverRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallOptionalObserverRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved optional observer dependency {dependency}"
