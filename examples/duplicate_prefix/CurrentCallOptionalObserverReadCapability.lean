import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.S05CompletedAncestryReadCapability
import duplicate_prefix.CurrentCallOptionalLenAssociatedRead
namespace DuplicatePrefix.CurrentCallOptionalObserverReadCapability
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open BorrowRangeAccess GeneralRangeMapOrigins GeneralRangeMapState CurrentCallResourceNormalization
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

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
      S05CompletedAncestryReadMutable.Authority tree completion future source (source_access_location result) ∧
      Nonempty (DuplicatePrefixNormalKind.Capability tree (source_access_location result) global.protectedTags reader .Read) := by
  obtain ⟨depth⟩ := runtime.formed.depth
  let formed := runtime.formed.toGraphState
  obtain ⟨rootNode,rootAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have rootEq : rootNode=selectedNode := Option.some.inj (rootAt.symm.trans selectedPresent)
  subst rootNode
  have classification : ∀ index node,tree.nodes.get index=some node → Path tree selected index →
      (Below completion index source ↔ Path tree index source) := by
    intro index node present path
    exact ⟨(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.same_root_ancestor") model selectedPresent parentless present path sourcePath,model.physical_below⟩
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
  obtain ⟨afterNormal,componentEq⟩ := normalDone.2.2.2.2.2
  have afterRights := (spatial_install_rule ".S05CompletedAncestryReadCapability.capability_selected") tree
    (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location global.protectedTags
    formed selected reader readerPath afterNormal
  let scanned := (forIn (List.range' 0 tree.roots.size)
    ((tree.performNormalAccessAt initial reader .Read global.protectedTags mode).location,none,false)
    (GeneralBorrowConcreteRowCutoffAccess.scan tree selected (some selectedNode.tag)
      (if mode == .SkipChildrenOfAccessed then source_min_exposed tree reader else none) .Read global.protectedTags mode range) : Id GeneralBorrowConcreteRowCutoffAccess.State)
  have afterCap := GeneralBorrowPhysicalNormalCapability.of_physical_component tree scanned.1 global.protectedTags
    formed runtime.formed.fits selected reader selectedNode selectedPresent parentless readerPath .Read (by
      intro index node present path
      have rights := afterRights index node present path
      unfold RawState at rights
      rw [←final.2.2.2.2.1 index node present path] at rights
      exact rights)
  have ending : ((source_normal_projection tree initial global.protectedTags).topology.ancestorPath reader.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial reader .Read global.protectedTags mode).access.root=selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree initial global.protectedTags)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2,afterCap⟩)

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
        (global.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source (source_access_location result) ∧
      Nonempty (DuplicatePrefixNormalKind.Capability tree (source_access_location result) global.protectedTags reader .Read) := by
  let first := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
  obtain ⟨firstRuntime,_,firstOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime allocation
    readerNode.tag reader readerNode readerPresent rfl readerHidden
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨selectedActual,selectedAt,selectedNone⟩ := complete.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have selectedEq : selectedActual=selectedNode := Option.some.inj (selectedAt.symm.trans selectedPresent)
  subst selectedActual
  have classification : ∀ index node,tree.nodes.get index=some node → Path tree selected index → (Below completion index source ↔ Path tree index source) := by
    intro index node present path
    exact ⟨(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.same_root_ancestor") complete selectedPresent selectedNone present path sourcePath,complete.physical_below⟩
  obtain ⟨normal⟩ := (spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.normal_of_authority") tree completion location first.protectedTags runtime.formed.toGraphState
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
end
end DuplicatePrefix.CurrentCallOptionalObserverReadCapability
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallOptionalObserverReadCapability" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved optional observer capability dependency {dependency}"
