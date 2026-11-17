import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowObserverReadTwoParents
import duplicate_prefix.S05CompletedAncestryReadCapability
namespace DuplicatePrefix.S05CompletedAncestryObserverRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open BorrowRangeAccess GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section
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
private theorem finish (tree : BorrowTree) (completion : Completion) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePath : Path tree selected source) (_readerPresent : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree selected reader)
    (future : ProtectedTags) (readable : DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read)
    (authority : Authority tree completion future source location)
    (flags : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ (index : UniIndex) (node : TreeNode), tree.nodes.get index = some node → Path tree root index →
      future.contains node.tag = global.protectedTags.contains node.tag)
    (coherent : LocationCoherent tree location global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange)
    (next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location reader .Read global.protectedTags mode).location future source) :
    let result := source_tree_access_at tree location (some reader) .Read global.protectedTags mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Authority tree completion future source (source_access_location result) := by
  obtain ⟨depth⟩ := runtime.formed.depth
  have formed := runtime.formed.toGraphState
  have fits := runtime.formed.fits
  have rights := capability_selected tree location global.protectedTags formed selected reader readerPath readable
  have completed := S05CompletedAncestryConcreteRead.access tree completion location global.protectedTags complete formed depth order
    position selected source selectedNode slot selectedPresent sourcePath reader readerPath rights
    (by intro p root atRoot different index node present path below
        rw [←flags p root atRoot different index node present path]
        exact (authority index node present).1 below)
    (by intro p root atRoot different index node present path outside
        rw [←flags p root atRoot different index node present path]
        exact (authority index node present).2 outside)
    coherent profile possible short mode range
  have retained := raw_of_normal tree completion _ future complete formed depth fits position selected source selectedNode
    slot selectedPresent sourcePath next
  refine ⟨completed.1,completed.2.1,completed.2.2.1,completed.2.2.2.1,?_⟩
  intro index node present
  obtain ⟨forest⟩ := formed.forest location global.protectedTags
  have projectedSelf := GeneralBorrowPhysicalRootPath.projection_desc tree location global.protectedTags index index (.refl _ node present)
  obtain ⟨root,rootNode,rootAt,parentless,member,last⟩ := GeneralBorrowRootMembership.terminal
    tree location global.protectedTags forest depth formed.covered index node present projectedSelf.valid.1
  obtain ⟨rootPosition,rootSlot⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp member)
  let topology := (source_normal_projection tree location global.protectedTags).topology
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
    tree location global.protectedTags fits root rootNode rootAt index.toNat projectedPath
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
  · rw [flags rootPosition root rootSlot same index node present path]
    exact ⟨completed.2.2.2.2.2.1 rootPosition root rootSlot same index node present path,
      completed.2.2.2.2.2.2 rootPosition root rootSlot same index node present path⟩

theorem access (tree : BorrowTree) (completion : Completion) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
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
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion location second.protectedTags complete runtime.formed.toGraphState
    depth runtime.formed.fits position selected source selectedNode slot selectedPresent sourcePath
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  obtain ⟨_,_,next,_⟩ := GeneralBorrowObserverReadTwoParents.access tree location global runtime allocation reader temporary source
    readerNode temporaryNode readerPresent readerEdge temporaryPresent temporaryEdge readerHidden temporaryHidden readable normal mode
  apply finish tree completion location global runtime complete order position selected source reader selectedNode readerNode
    slot selectedPresent sourcePath readerPresent readerPath second.protectedTags readable authority _ coherent profile possible short mode range next
  intro p root rootSlot different index node present path
  obtain ⟨rootNode,rootPresent,parentless⟩ := complete.2.2.2.1 p root rootSlot
  obtain ⟨selectedActual,found,selectedParentless⟩ := complete.2.2.2.1 position selected slot
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
theorem direct (tree : BorrowTree) (completion : Completion) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
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
  obtain ⟨normal⟩ := S05CompletedAncestryNormal.normal tree completion location first.protectedTags complete runtime.formed.toGraphState
    depth runtime.formed.fits position selected source selectedNode slot selectedPresent sourcePath
    (fun index node present _ => (authority index node present).1)
    (fun index node present _ => (authority index node present).2)
  obtain ⟨_,_,next,_⟩ := GeneralBorrowObserverReadDirectParent.access tree location global runtime allocation reader source
    readerNode readerPresent readerEdge readerHidden readable normal runtime.formed.fits mode
  apply finish tree completion location global runtime complete order position selected source reader selectedNode readerNode
    slot selectedPresent sourcePath readerPresent readerPath first.protectedTags readable authority _ coherent profile possible short mode range next
  intro p root rootSlot different index node present path
  obtain ⟨rootNode,rootPresent,parentless⟩ := complete.2.2.2.1 p root rootSlot
  obtain ⟨selectedActual,found,selectedParentless⟩ := complete.2.2.2.1 position selected slot
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

theorem range_direct (tree : BorrowTree) (completion : Completion) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (position : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
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
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ Completes result.tree completion := by
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
    obtain ⟨rootNode,rootPresent,parentless⟩ := complete.2.2.2.1 p root rootSlot
    obtain ⟨selectedActual,found,selectedParentless⟩ := complete.2.2.2.1 position selected slot
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
  have capContract := S05CompletedAncestryReadCapability.access tree completion global.protectedTags complete runtime.formed.toGraphState
    depth order position selected source reader selectedNode readerNode slot selectedPresent sourcePath readerPresent readerPath
    offset len lower upper (by
      intro cursor valid positive start stop
      have current := owned cursor valid positive start stop
      refine ⟨runtime.possible cursor valid,current.1,?_⟩
      intro p root atRoot different index node present path
      rw [←flags p root atRoot different index node present path]
      exact current.2 index node present)
    runtime.formed.well all bounds requestLower requestUpper short mode
  have mapped := (complete.2.2.2.2.1 reader readerNode readerPresent).1
  have authorityContract := GeneralBorrowConcreteRangeEntry.access tree global.protectedTags readerNode.tag reader mapped offset len .Read mode
    (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read) ∧ Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location) (fun location => Authority tree completion (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location) (fun location => LocationCoherent tree location global.protectedTags ∧ GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) (fun _ _ => True)
    (fun _ initial => initial.2) (fun _ => trivial) (by
      intro location current representation range
      obtain ⟨readable⟩ := current.1
      have row := direct tree completion location global runtime complete order position selected source reader selectedNode readerNode
        slot selectedPresent sourcePath readerPresent readerPath allocation readerEdge readerHidden readable current.2
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
    exact completion_locations tree completion _ complete

end
end DuplicatePrefix.S05CompletedAncestryObserverRead
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryObserverRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved observer Read dependency {dependency}"
