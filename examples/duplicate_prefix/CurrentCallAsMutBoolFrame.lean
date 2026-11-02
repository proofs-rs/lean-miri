import duplicate_prefix.S05ConcreteFnEntryDisjoint
import duplicate_prefix.S05CurrentMutableProtectorRelease
import duplicate_prefix.CurrentCallRootActivity
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
import duplicate_prefix.CandidateCurrentWindowAuthority

namespace DuplicatePrefix.CurrentCallAsMutBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowView
open S05ConcreteProtectedChildCompletion OrdinaryBorrowAuthority
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Inserting another slot preserves the old anchor's activity at every byte.
The real range iterator may split segments; no unchanged-tree claim is used. -/
private theorem materialized_active (tree : BorrowTree) (child target : UniIndex)
    (different : target ≠ child) (offset len : Size) (kind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    GeneralBorrowFreshActiveWithin.Profile
      (tree.locations.modifyRange offset len (fun _ location =>
        GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
      target kind lower upper := by
  let prepared := tree.locations.iterMut offset len
  let modify := fun (_ : ByteRange) location =>
    GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside
  let updated := (tree.locations.modifyRange offset len modify).state
  have good := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have old := GeneralBorrowFreshActiveWithin.refines tree.locations prepared.state good.2.1 target kind lower upper active
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro point location valueAt state stored accessed accessKind associated
  obtain ⟨position,valid,start,stop,data⟩ := valueAt
  have oldValid : position < prepared.state.entries.size := by
    change position < updated.entries.size at valid
    omega
  obtain ⟨_,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshChild.inside)
    well bounds position oldValid
  change updated.entries[position] = _ at entry
  have range : updated.entries[position].range = prepared.state.entries[position].range := by
    have known := congrArg RangeMapSegment.range entry
    split at known <;> exact known
  change updated.entries[position].data = location at data
  have lookup : updated.entries[position].data.perms.get target = prepared.state.entries[position].data.perms.get target := by
    rw [entry]
    split
    · exact GeneralBorrowFreshLocation.get_other _ _ _ _ different
    · rfl
  rw [←data,lookup] at stored
  rw [range] at start stop
  exact old point prepared.state.entries[position].data ⟨position,oldValid,start,stop,rfl⟩ state stored accessed accessKind associated

private theorem old_node (tree after : BorrowTree) (child parent target : UniIndex)
    (parentNode targetNode : TreeNode) (newTag : BorTag) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (vacant : tree.nodes.get child = none)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshChild.child newTag parent) mapping locations)) :
    ∃ next, after.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) mapping locations
  have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
  have atStage : stage.nodes.get target = some targetNode := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
    exact targetAt
  obtain ⟨next,found,tag,parentEq,children,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape target targetNode atStage
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure target
  rw [found,atStage] at flags
  exact ⟨next,found,tag,parentEq,children,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

/-- A distinct existing Bool child retains its exact leaf and exposure fields
and its bytewise activity through either actual Default allocator branch. -/
private theorem old_facets (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    (∃ next, actual.tree.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target kind lower upper := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildMutable.index input
    have vacant : tree.nodes.get child = none := by
      have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildMutable.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) target kind lower upper staged⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildMutableReuse.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) (GeneralBorrowFreshMetadataChildMutableReuse.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) target kind lower upper staged⟩

/-- The actual AsMut mutable FnEntry operation and helper release preserve the
current Bool child through the helper's whole endCall. The fresh helper's raw
source authority derives release success; Bool postrights are conclusions. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (allocation : AllocId) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (position : Nat) (selected parent target : UniIndex)
    (selectedNode parentNode targetNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedAt : tree.nodes.get selected = some selectedNode)
    (parentAt : tree.nodeAt parent = some parentNode) (path : Path tree selected parent)
    (targetAt : tree.nodeAt target = some targetNode) (leaf : targetNode.children = #[])
    (hidden : targetNode.isExposed = false) (different : target ≠ parent)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size+1 < 65536)
    (offset len boolOffset : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (boolBounds : boolOffset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (disjoint : (offset+len).toNat ≤ boolOffset.toNat ∨ (boolOffset+1).toNat ≤ offset.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target) boolOffset (boolOffset+1) tree.locations)
    (boolActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write boolOffset (boolOffset+1)) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (helper : UniIndex),
      GeneralBorrowForestFnEntry.operation tree global {} allocation parentNode.tag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.child.tree.indexOfTag output.tag = some helper ∧
      let released := output.child.tree.releaseProtector output.tag output.global.protectedTags
      released.status = .Released ∧ released.tree = {output.child.tree with locations := released.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released.tree output.global ∧ Completes released.tree (extend completion helper parent) ∧
      released.tree.locations.size = tree.locations.size ∧ released.tree.nodes.size ≤ tree.nodes.size+1 ∧
      OwnedOn (Authority released.tree (extend completion helper parent) (output.global.endCall output.frame).protectedTags target)
        boolOffset (boolOffset+1) released.tree.locations ∧
      (∃ next, released.tree.nodeAt target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
        next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released.tree target .Write boolOffset (boolOffset+1) := by
  have pointDisjoint : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat := by
    intro point start stop
    rcases disjoint with left | right <;> omega
  obtain ⟨output,actual,tag,outputGlobal,frameEq,readDone,childDone,afterRuntime,capacity,growth,afterBounds,afterOrder,
    targetLookup,helper,lookup,roots,afterComplete,helperOwned,afterBool⟩ := S05ConcreteFnEntryDisjoint.invoke_window
    tree global {} allocation completion runtime complete order position selected parent selectedNode parentNode slot selectedAt parentAt path
    room nodeRoom (by omega) offset len nonzero bounds owned target targetNode targetAt boolOffset 1 (by simpa using boolBounds) pointDisjoint boolOwned
  obtain ⟨allocated,held,_,registeredRuntime,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let canonical : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete parentNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have canonicalActual : GeneralBorrowForestFnEntry.operation tree global {} allocation parentNode.tag offset len .VisitChildrenOfAccessed = .ok canonical := by
    simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  have outputEq : output = canonical := Except.ok.inj (actual.symm.trans canonicalActual)
  subst output
  obtain ⟨_,readRuntime,readComplete,_,readNodes,_,readTags,readCapacity⟩ := S05ConcreteFnEntryRaw.prepare_read
    tree global {} allocation completion runtime complete order position selected parent selectedNode parentNode slot selectedAt parentAt path
    room offset len bounds owned (by omega) .VisitChildrenOfAccessed
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have registeredOwned : OwnedOn (Authority tree completion registration.1.protectedTags parent) offset (offset+len) tree.locations := by
    intro cursor valid positive start stop index node present
    rw [flags index node present]
    exact owned cursor valid positive start stop index node present
  have activeRead : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree target .Write boolOffset (boolOffset+1) :=
    CurrentCallRootActivity.concrete tree registration.1 registeredRuntime completion complete position selected parent target selectedNode parentNode
      slot selectedAt parentAt path parentNode.tag ((complete.2.2.2.2.1 parent parentNode parentAt).1) offset len bounds registeredOwned
      targetNode targetAt leaf hidden different boolOffset (boolOffset+1) boolActive .Read .VisitChildrenOfAccessed
  have parentAfter : accessed.tree.nodeAt parent = some parentNode := by change accessed.tree.nodes.get parent = _;rw [readNodes];exact parentAt
  have targetAfter : accessed.tree.nodeAt target = some targetNode := by change accessed.tree.nodes.get target = _;rw [readNodes];exact targetAt
  have tagged : accessed.tree.indexOfTag parentNode.tag = some parent := (readComplete.2.2.2.2.1 parent parentNode parentAfter).1
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [readTags];exact fresh
  have roomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  obtain ⟨⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩,activeChild⟩ := old_facets accessed.tree registration.1 readRuntime
    parentNode.tag global.nextPointerTag parent target parentNode targetNode tagged parentAfter targetAfter different freshAfter roomAfter
    offset len nonzero boundsAfter .Write boolOffset (boolOffset+1) activeRead
  obtain ⟨activityHelper,activityLookup,helperActive⟩ := GeneralBorrowConstructorChildActivity.Protected.construct accessed.tree registration.1 readRuntime
    parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter roomAfter offset len nonzero boundsAfter
  have activityEq : activityHelper = helper := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityHelper
  obtain ⟨metadataHelper,metadataLookup,⟨helperNode,helperAt,helperTag,helperHidden⟩,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct
    accessed.tree registration.1 readRuntime parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter roomAfter offset len nonzero boundsAfter
  have metadataEq : metadataHelper = helper := Option.some.inj (metadataLookup.symm.trans lookup)
  subst metadataHelper
  have helperDifferent : target ≠ helper := by
    intro equal
    have found : canonical.child.tree.nodeAt helper = some next := by simpa only [canonical,BorrowTree.nodeAt,equal] using nextAt
    have nodeEq := Option.some.inj (found.symm.trans helperAt)
    have freshTag := nodeFresh (target,targetNode) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes target targetNode).mpr targetAt))
    exact freshTag (nextTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans helperTag))
  have sourcePositive : offset.toNat < (offset+len).toNat := by
    have sum : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt_size
    have lenPositive : len.toNat ≠ 0 := by intro zero;apply nonzero;apply UInt64.toNat_inj.mp;exact zero
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt sum]
    omega
  have boolPositive : boolOffset.toNat < (boolOffset+1).toNat := by
    have sum : boolOffset.toNat+1 < 2^64 := Nat.lt_of_le_of_lt boolBounds tree.locations.size.bytes.toNat_lt_size
    rw [UInt64.toNat_add]
    simp only [show (1:UInt64).toNat=1 from rfl,Nat.mod_eq_of_lt sum]
    omega
  obtain ⟨releasePosition,releaseRoot,releaseRootNode,releaseSlot,releaseRootAt,releasePath⟩ := CandidateCurrentWindowAuthority.root_path
    canonical.child.tree afterRuntime.formed.toGraphState helper helperNode helperAt
  have shortAfter : canonical.child.tree.nodes.size < 65536 := by omega
  obtain ⟨released,releaseFrame,releaseRuntime,releaseComplete,releaseCapacity,retained,activeRelease⟩ :=
    S05CurrentMutableProtectorRelease.release_preserving_disjoint_activity canonical.child.tree canonical.global (extend completion helper parent)
      afterRuntime afterComplete afterOrder releasePosition releaseRoot helper releaseRootNode helperNode releaseSlot releaseRootAt releasePath helperAt helperHidden
      offset len sourcePositive helperActive helperOwned boolOffset (boolOffset+1) boolPositive
      (Authority canonical.child.tree (extend completion helper parent) canonical.global.protectedTags target) disjoint afterBool
      target next nextAt (nextChildren.trans leaf) (nextHidden.trans hidden) helperDifferent activeChild shortAfter
  rw [helperTag] at released releaseFrame releaseRuntime releaseComplete releaseCapacity retained activeRelease
  refine ⟨canonical,helper,canonicalActual,rfl,lookup,released,releaseFrame,releaseRuntime,releaseComplete,releaseCapacity.trans capacity,?_,?_,?_,activeRelease⟩
  · change (canonical.child.tree.releaseProtector canonical.tag canonical.global.protectedTags).tree.nodes.size ≤ _
    rw [releaseFrame]
    exact growth
  · intro cursor valid positive start stop index node nodeAt
    have oldAt : canonical.child.tree.nodes.get index = some node := by rw [releaseFrame] at nodeAt;exact nodeAt
    have rights := retained cursor valid positive start stop index node oldAt
    have weaken := GeneralBorrowRelease.end_call_weakens canonical.global canonical.frame node.tag
    refine ⟨?_,?_⟩
    · intro below
      obtain ⟨possible,disabled,frozen,reserved⟩ := rights.1 below
      exact ⟨possible,disabled,frozen,fun held => reserved (weaken held)⟩
    · intro outside
      obtain ⟨possible,quiet⟩ := rights.2 outside
      exact ⟨possible,fun held => quiet (weaken held)⟩
  · refine ⟨next,?_,nextTag,nextParent,nextChildren,nextHidden⟩
    change (canonical.child.tree.releaseProtector canonical.tag canonical.global.protectedTags).tree.nodeAt target = some next
    rw [releaseFrame]
    exact nextAt

end
end DuplicatePrefix.CurrentCallAsMutBoolFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallAsMutBoolFrame").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved AsMut Bool frame dependency {dependency}"
