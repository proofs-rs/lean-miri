import duplicate_prefix.CurrentCallOptionalReadQueries
import duplicate_prefix.CurrentCallLenReadCapability
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.S05CurrentReadProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor

/-! Actual helper Read release with an optional parent interpretation. The
source's full authority is demanded only under its literal future protector
flags, while the protected helper retains its current Read capability. -/
namespace DuplicatePrefix.CurrentCallOptionalLenAssociatedRead
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

theorem direct (tree : BorrowTree) (completion : Completion) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (_order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePath : Path tree selected source) (readerPresent : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree selected reader)
    (allocation : AllocId) (readerEdge : readerNode.parent = some source)
    (readerHidden : readerNode.isExposed = false)
    (readable : DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read)
    (authority : Authority tree completion
      (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location)
    (coherent : LocationCoherent tree location global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some reader) .Read global.protectedTags mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Authority tree completion
        (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source (source_access_location result) := by
  let first := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
  obtain ⟨firstRuntime,_,firstOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime allocation
    readerNode.tag reader readerNode readerPresent rfl readerHidden
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨selectedActual,selectedAt,selectedNone⟩ := complete.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have selectedEq : selectedActual=selectedNode := Option.some.inj (selectedAt.symm.trans selectedPresent)
  subst selectedActual
  have classification : ∀ index node,tree.nodes.get index=some node → Path tree selected index → (Below completion index source ↔ Path tree index source) := by
    intro index node present path
    exact ⟨same_root_ancestor complete selectedPresent selectedNone present path sourcePath,complete.physical_below⟩
  obtain ⟨normal⟩ := normal_of_authority tree completion location first.protectedTags runtime.formed.toGraphState
    depth runtime.formed.fits position selected source selectedNode slot selectedPresent sourcePath classification
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  obtain ⟨_,_,next,_⟩ := GeneralBorrowObserverReadDirectParent.access tree location global runtime allocation reader source
    readerNode readerPresent readerEdge readerHidden readable normal runtime.formed.fits mode
  apply finish tree completion location global runtime complete primarySlot distinct position selected source reader selectedNode readerNode
    primaryBelow slot selectedPresent sourcePath readerPresent readerPath first.protectedTags readable authority _ coherent profile possible short mode range next
  intro p root rootSlot different index node present path
  obtain ⟨rootNode,rootPresent,parentless⟩ := complete.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  obtain ⟨selectedActual,found,selectedParentless⟩ := complete.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have selectedEq := Option.some.inj (found.symm.trans selectedPresent)
  subst selectedActual
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
  change (first.protectedTags.get node.tag).isSome = (global.protectedTags.get node.tag).isSome
  rw [firstEq]
private theorem parent_locations (tree : BorrowTree) (completion : Completion) (locations : DedupRangeMap LocationTree)
    (complete : ParentInterpretation tree completion) : ParentInterpretation {tree with locations:=locations} completion := by
  refine ⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ complete.graph,complete.order,complete.dimension,complete.physical,complete.edgeLive,complete.primaryNone,?_⟩
  intro position root slot origin edge
  obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := complete.virtual position root slot origin edge
  exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before:={tree with locations:=locations}) (after:=tree) rfl path⟩

theorem range_direct (tree : BorrowTree) (completion : Completion) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePath : Path tree selected source) (readerPresent : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree selected reader)
    (allocation : AllocId) (readerEdge : readerNode.parent = some source)
    (readerHidden : readerNode.isExposed = false)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧ Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location) lower upper tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let result := tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read global.protectedTags mode
    GeneralBorrowConcreteRangeInvariant.Contract tree (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧ Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location)
      (fun location => LocationCoherent tree location global.protectedTags ∧ GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (fun _ _ => True) lower upper result ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ ParentInterpretation result.tree completion := by
  let future := (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags
  have all : Every (fun location => LocationCoherent tree location global.protectedTags ∧ GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations := by
    intro position valid
    exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨_,_,other⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime allocation readerNode.tag reader
    readerNode readerPresent rfl readerHidden
  have flags : ∀ (p : Nat) (root : UniIndex), tree.roots[p]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → future.contains node.tag = global.protectedTags.contains node.tag := by
    intro p root rootSlot different index node present path
    obtain ⟨rootNode,rootPresent,parentless⟩ := complete.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
    obtain ⟨selectedActual,found,selectedParentless⟩ := complete.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
    have eq := Option.some.inj (found.symm.trans selectedPresent)
    subst selectedActual
    have distinct : node.tag ≠ readerNode.tag := by
      intro same
      have one := runtime.formed.allocator.nodeTags index node present
      have two := runtime.formed.allocator.nodeTags reader readerNode readerPresent
      rw [same,two] at one
      have eq := Option.some.inj one
      subst reader
      exact different (CompletedBorrowAncestry.physical_roots_unique rootPresent parentless selectedPresent selectedParentless path readerPath)
    change (future.get node.tag).isSome = (global.protectedTags.get node.tag).isSome
    rw [other node.tag distinct]
  have capContract := CurrentCallLenReadCapability.access tree completion global.protectedTags complete distinct
    position selected source reader selectedNode readerNode (by intro root found;have equal:=Option.some.inj (primarySlot.symm.trans found);simpa only [←equal] using primaryBelow) slot selectedPresent sourcePath readerPresent readerPath
    offset len lower upper (by
      intro cursor valid positive start stop
      have current := owned cursor valid positive start stop
      refine ⟨runtime.possible cursor valid,current.1,?_⟩
      intro p root atRoot different index node present path
      rw [←flags p root atRoot different index node present path]
      exact current.2 index node present)
    runtime.formed.well all bounds requestLower requestUpper short mode
  have mapped := runtime.formed.allocator.nodeTags reader readerNode readerPresent
  have authorityContract := GeneralBorrowConcreteRangeEntry.access tree global.protectedTags readerNode.tag reader mapped offset len .Read mode
    (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧ Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location) (fun location => Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location) (fun location => LocationCoherent tree location global.protectedTags ∧ GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (fun _ _ => True)
    (fun _ initial => initial.2) (fun _ => trivial) (by
      intro location current representation range
      obtain ⟨readable⟩ := current.1
      have row := direct tree completion location global runtime complete primarySlot distinct order position selected source reader selectedNode readerNode
        primaryBelow slot selectedPresent sourcePath readerPresent readerPath allocation readerEdge readerHidden readable current.2
        representation.1 representation.2.1 representation.2.2 short mode range
      exact ⟨row.1,row.2.2.2.2,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩)
    lower upper owned runtime.formed.well all bounds requestLower requestUpper
  have combined : GeneralBorrowConcreteRangeInvariant.Contract tree (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧ Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location)
      (fun location => LocationCoherent tree location global.protectedTags ∧ GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (fun _ _ => True) lower upper
      (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read global.protectedTags mode) :=
    { completed := authorityContract.completed
      runtime := authorityContract.runtime
      rows := by
        intro cursor valid positive start stop
        exact ⟨(capContract.rows cursor valid positive start stop).2.1,
          authorityContract.rows cursor valid positive start stop⟩
      well := authorityContract.well
      capacity := authorityContract.capacity
      frames := authorityContract.frames
      nodes := authorityContract.nodes
      roots := authorityContract.roots
      tags := authorityContract.tags }
  refine ⟨combined,?_,?_⟩
  · rw [combined.tree_eq]
    have graph := GeneralBorrowStructuralHistoryState.graph_locations tree
      (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read global.protectedTags mode).tree.locations runtime.formed.toGraphState
    refine ⟨⟨⟨graph,combined.well⟩,?_⟩,?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro cursor valid
      have profile := (combined.runtime cursor valid).2.1
      exact ⟨profile.present,profile.vacant⟩
    · intro cursor valid
      exact (combined.runtime cursor valid).1
    · intro cursor valid
      exact (combined.runtime cursor valid).2.2
  · rw [combined.tree_eq]
    exact parent_locations tree completion _ complete
private theorem end_flags (global : GlobalState) (allocation : AllocId) (tag query : BorTag)
    (quiet : global.protectedTags.contains tag = false ∨ query ≠ tag) :
    (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags.contains query = global.protectedTags.contains query := by
  have table : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags = global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rw [table]
  by_cases same : query = tag
  · subst query
    have absent : global.protectedTags.contains tag = false := quiet.resolve_right (by simp)
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    exact absent.symm
  · unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other global.protectedTags tag query same]

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
theorem prepare (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup) (order : ParentTagOrder tree)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source) (readerAt : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree root reader) (readerEdge : readerNode.parent = some source)
    (hidden : readerNode.isExposed = false) (readerUnheld : global.protectedTags.contains readerNode.tag = false)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size < 65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations) :
    let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
    let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
      registration.1.protectedTags .VisitChildrenOfAccessed
    let future := (registration.1.endCall (({} : FrameState).addProtector allocation global.nextPointerTag)).protectedTags
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      ParentInterpretation accessed.tree completion ∧ accessed.tree.nodes = tree.nodes ∧ accessed.tree.roots = tree.roots ∧
      accessed.tree.tagMapping = tree.tagMapping ∧ accessed.tree.locations.size = tree.locations.size ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read) ∧
        Authority accessed.tree completion future source location) offset (offset+len) accessed.tree.locations := by
  obtain ⟨_,_,_,current,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have unheld : registration.1.protectedTags.contains readerNode.tag = false := (flags reader readerNode readerAt).trans readerUnheld
  obtain ⟨actualRoot,found,parentless⟩ := complete.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same := Option.some.inj (found.symm.trans rootAt)
  subst actualRoot
  have rows : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location registration.1.protectedTags reader .Read) ∧
      Authority tree completion (registration.1.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := readable cursor valid positive start stop
    have authority := owned cursor valid positive start stop
    constructor
    · apply GeneralBorrowPhysicalNormalCapability.of_physical_component tree _ registration.1.protectedTags current.formed.toGraphState
        current.formed.fits root reader rootNode rootAt parentless readerPath .Read
      intro index node present path
      rw [flags index node present]
      exact capability_selected tree _ global.protectedTags runtime.formed.toGraphState root reader readerPath normal index node present path
    · intro index node present
      rw [end_flags registration.1 allocation readerNode.tag node.tag (.inl unheld),flags index node present]
      exact authority index node present
  obtain ⟨contract,afterRuntime,afterComplete⟩ := range_direct tree completion registration.1 current complete primarySlot distinct order
    position root source reader rootNode readerNode primaryBelow rootSlot rootAt sourcePath readerAt readerPath allocation readerEdge hidden
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  refine ⟨contract.completed,afterRuntime,afterComplete,contract.nodes,contract.roots,contract.tags,contract.capacity,?_⟩
  rw [contract.tree_eq]
  intro cursor valid positive start stop
  have result := contract.rows cursor valid positive start stop
  obtain ⟨capability⟩ := result.1
  refine ⟨⟨⟨capability.component,capability.permissions⟩⟩,?_⟩
  intro index node present
  have freshNode : node.tag ≠ global.nextPointerTag :=
    nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present))
  rw [end_flags registration.1 allocation global.nextPointerTag node.tag (.inr freshNode)]
  have authority := result.2 index node present
  rw [end_flags registration.1 allocation readerNode.tag node.tag (.inl unheld)] at authority
  exact authority
end
end DuplicatePrefix.CurrentCallOptionalLenAssociatedRead
