import duplicate_prefix.CurrentCallSharedConstructorFrame
import duplicate_prefix.CurrentCallReadRootActivity
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.CurrentCallBoolWindow
import duplicate_prefix.CurrentCallCheckpointLenRuntime
import duplicate_prefix.CurrentCallCheckpointLenRelease
import duplicate_prefix.CurrentCallResourceCopyInstall
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.CurrentCallCheckpointLenControl
import duplicate_prefix.CurrentCallCheckpointLen
import duplicate_prefix.CurrentCallSpatialLenAssociatedRead
import duplicate_prefix.CurrentCallExclusiveWindowFrame
import duplicate_prefix.S02DisjointReleaseFrame
import duplicate_prefix.CurrentCallCheckpointShared

namespace DuplicatePrefix.CurrentCallCheckpointSharedBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter
open CandidateCurrentJointCall
open CandidateStableCallOwnership OrdinaryBorrowAuthority CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open GeneralBorrowView GeneralBorrowFreshGraph GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
open Lean Elab Term in
elab "checkpoint_bool_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_) => name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)] => return mkConst name
  | _ => throwError "expected unique checked checkpoint Bool helper {suffix.getString}"
noncomputable section

/-- Physical capabilities are recovered per original row from its fixed cell. -/
theorem spatial_readable {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (tag : BorTag) (parent : UniIndex)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra
      location tracker.global.protectedTags parent .Read)) start (start+amount) role.backing.allocation.extra.locations := by
  have fit : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have endEq : (start+amount).toNat=offset+length := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fit,startEq,amountEq]
  intro cursor valid positive beforeUpper afterLower
  let segment := role.backing.allocation.extra.locations.entries[cursor]
  have rowPositive := (GeneralRangeMapGeometry.facts _ runtime.formed.well (by omega)).2.1 cursor valid
  let point := max start.toNat segment.range.start.toNat
  have pointLower : start.toNat≤point := Nat.le_max_left _ _
  have rowLower : segment.range.start.toNat≤point := Nat.le_max_right _ _
  have pointUpper : point<(start+amount).toNat := by dsimp only [point]; dsimp only [segment] at *;omega
  have rowUpper : point<segment.range.stop.toNat := by dsimp only [point]; dsimp only [segment] at *;omega
  have request : CandidateStableCallOwnership.Window role.backing.id offset length (role.backing.id,point) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  let overlap : CurrentCallSpatialSourceCover.Active role i := ⟨_,request,cell⟩
  let W := CurrentCallSpatialRows.singleByte role i overlap _ request cell
  obtain ⟨G⟩ := geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have inside := CurrentCallSpatialRows.singleByte_inside role i overlap _ request cell
  have sourceAt := CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have sourceMapped : CurrentCallSpatialRows.source role=some parent := by
    simp only [CurrentCallSpatialRows.source,concrete,mapped]
  have grant : W.pointer.grant=parent := Option.some.inj (sourceAt.symm.trans sourceMapped)
  have member : segment∈role.backing.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := CurrentCallResourceAccess.selected_normal W G rfl _ inside segment member rowLower rowUpper
    (runtime.formed.profile cursor valid) (runtime.possible cursor valid)
  rw [grant] at normal
  exact ⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal .Read⟩

/-- Location-only accesses preserve the optional graph interpretation. -/
theorem parents_locations (tree : BorrowTree) (C : Completion)
    (parents : ParentInterpretation tree C) (locations : DedupRangeMap LocationTree) :
    ParentInterpretation {tree with locations := locations} C := by
  refine ⟨GeneralBorrowStructuralHistoryState.graph_locations tree locations parents.graph,
    parents.order,parents.dimension,parents.physical,parents.edgeLive,parents.primaryNone,?_⟩
  intro position root slot origin edge
  obtain ⟨earlier,originRoot,rootNode,originNode,older,earlierSlot,rootAt,originAt,exposed,ordered,path⟩ :=
    parents.virtual position root slot origin edge
  exact ⟨earlier,originRoot,rootNode,originNode,older,earlierSlot,rootAt,originAt,exposed,ordered,
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := locations}) (after := tree) rfl path⟩

/-- The actual associated Read frames only the independent target bank. No
source authority in this target completion is required. -/
theorem read_frame (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parents : ParentInterpretation tree C)
    (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (sourceAt : tree.nodeAt source=some sourceNode) (tagged : tree.indexOfTag tag=some source)
    (targetAt : tree.nodeAt target=some targetNode) (leaf : targetNode.children=#[])
    (hidden : targetNode.isExposed=false) (different : target≠source)
    (start amount lower upper : UInt64)
    (bounds : start.toNat+amount.toNat≤tree.locations.size.bytes.toNat)
    (readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags source .Read))
      start (start+amount) tree.locations)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→
      point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper)
    (visit : ChildrenVisitMode)
    (shape : (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read global.protectedTags visit).tree = {tree with locations := (tree.performBorrowAccessRange (.concrete tag)
        (Size.ofBytes start) (Size.ofBytes amount) .Read global.protectedTags visit).tree.locations}) :
    let after := (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read global.protectedTags visit).tree
    ParentInterpretation after C ∧ OwnedOn (Authority after C global.protectedTags target) lower upper after.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin after target .Write lower upper := by
  have nodes := congrArg BorrowTree.nodes shape
  have retained := GeneralBorrowRangeOutsideOwned.owned (Authority tree C global.protectedTags target)
    tree (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read global.protectedTags visit
    runtime.formed.well bounds lower upper apart owned
  refine ⟨?_,?_,CurrentCallReadRootActivity.concrete_of_normal tree global runtime tag source target sourceNode sourceAt
    start amount bounds readable tagged targetNode targetAt leaf hidden different lower upper active visit⟩
  · rw [shape]
    exact parents_locations tree C parents _
  · intro cursor valid positive begin finish index node found
    rw [nodes] at found
    exact retained cursor valid positive begin finish index node found

/-- Actual hidden observer release preserves the independent Bool bank using
only the observer's physical Read profile and disjoint callback footprint. -/
theorem release_frame (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parents : ParentInterpretation tree C)
    (tag : BorTag) (helper target : UniIndex) (helperNode targetNode : TreeNode)
    (tagged : tree.indexOfTag tag=some helper) (helperAt : tree.nodeAt helper=some helperNode)
    (helperHidden : helperNode.isExposed=false) (targetAt : tree.nodeAt target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠helper)
    (start stop lower upper : UInt64)
    (helperActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree helper .Read start stop)
    (readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags helper .Read)) start stop tree.locations)
    (apart : stop.toNat≤lower.toNat∨upper.toNat≤start.toNat)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let actual := tree.releaseProtector tag global.protectedTags
    ParentInterpretation actual.tree C ∧ OwnedOn (Authority actual.tree C global.protectedTags target) lower upper actual.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper := by
  have writeProfile : GeneralBorrowFreshActiveWithin.ActiveWithin tree helper .Write start stop := by
    intro point location atPoint state stored accessed kind associated
    have old := helperActive point location atPoint state stored accessed kind associated
    exact ⟨old.1,old.2.1,by intro impossible;cases impossible⟩
  have retained := S02DisjointReleaseFrame.release tree global.protectedTags tag helper helper helperNode tagged helperAt helperHidden
    start stop writeProfile writeProfile (Authority tree C global.protectedTags target) lower upper apart owned runtime.formed.well
  have shape := GeneralBorrowStructuralReleaseGeometryFrame.release tree global.protectedTags tag
  have nodes := congrArg BorrowTree.nodes shape
  refine ⟨?_,?_,CurrentCallReadRootActivity.release tree global runtime tag helper target helperNode targetNode tagged helperAt helperHidden
    targetAt leaf hidden different start stop lower upper helperActive readable active⟩
  · rw [shape]
    exact parents_locations tree C parents _
  · intro cursor valid positive begin finish index node found
    rw [nodes] at found
    exact retained cursor valid positive begin finish index node found

theorem metadata_any (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (unheld : global.protectedTags.contains newTag = held)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        LeafFrame tree actual.tree child parent ∧
        ∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission := by
  have output := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held unheld offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildShared.index input
    have data := GeneralBorrowFreshMetadataChildShared.append input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get child = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have size : (GeneralBorrowFreshMetadataChildShared.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildShared.result input).nodes.size = _
      rw [data.size,atEnd]
      change tree.nodes.data.size+1 = _
      omega
    have frame := (checkpoint_bool_rule "CurrentCallSharedConstructorFrame.frame_of_stage") tree (GeneralBorrowFreshMetadataChildShared.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildShared.mapping input)
      (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.shape input)
      (GeneralBorrowFreshMetadataChildShared.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := (checkpoint_bool_rule "CurrentCallSharedConstructorFrame.old_default_of_stage") tree (GeneralBorrowFreshMetadataChildShared.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildShared.mapping input) (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have size : (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.size = _
      rw [data.size]
      change tree.nodes.data.size = _
      omega
    have frame := (checkpoint_bool_rule "CurrentCallSharedConstructorFrame.frame_of_stage") tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
      (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
      (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := (checkpoint_bool_rule "CurrentCallSharedConstructorFrame.old_default_of_stage") tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩

theorem construct_any (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (unheld : global.protectedTags.contains newTag = held)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (apart : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value ≤ newTag.value)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧ LeafFrame tree actual.tree child parent ∧
        ParentInterpretation actual.tree (extend completion child parent) ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations ∧
        (∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,leaf,old⟩ := metadata_any tree global runtime
    parentTag newTag parent parentNode tagged present fresh room tagBound held unheld offset len nonzero bounds
  obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := CurrentCallSharedConstructorFrame.disjoint tree global completion runtime complete
    parentTag newTag parent target parentNode targetNode tagged present targetAt fresh room tagBound held unheld
    offset len lower upper nonzero bounds apart owned
  have same : framedChild=child := Option.some.inj (framedLookup.symm.trans lookup)
  subst framedChild
  have order := GeneralBorrowSharedChildParentTagOrder.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room held offset len nonzero bounds complete.order parentOrder
  have parents := CurrentCallParentInsertion.of_leaf tree _ completion complete child parent leaf primaryLive afterRuntime.formed.toGraphState order
  exact ⟨done,afterRuntime,capacity,growth,child,lookup,leaf,parents,framed,old⟩
/-- SAME Default shared operation, framed in an independent optional target
completion. Source resources are consumed only through the spatial role. -/
theorem shared {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (C : Completion) (parents : ParentInterpretation role.backing.allocation.extra C)
    (tag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (parentAt : role.backing.allocation.extra.nodeAt parent=some parentNode)
    (targetAt : role.backing.allocation.extra.nodeAt target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠parent)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount lower upper : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (primaryLive : ∃node,role.backing.allocation.extra.nodes.get allocationRoot=some node)
    (owned : OwnedOn (Authority role.backing.allocation.extra C tracker.global.protectedTags target) lower upper role.backing.allocation.extra.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write lower upper) :
    let actual := GeneralBorrowRawSharedExpression.child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    ∃child,actual.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      ParentInterpretation actual.tree (extend C child parent) ∧
      OwnedOn (Authority actual.tree (extend C child parent) tracker.global.protectedTags target) lower upper actual.tree.locations ∧
      (∃next,actual.tree.nodeAt target=some next ∧next.tag=targetNode.tag ∧next.parent=targetNode.parent ∧next.children=targetNode.children ∧next.isExposed=targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper := by
  obtain ⟨other,node,otherMapped,nodeAt,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,normal,cellParents⟩ :=
    CurrentCallSpatialDefaultShared.prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  have same : other=parent := Option.some.inj (otherMapped.symm.trans mapped)
  subst other
  have sameNode : node=parentNode := Option.some.inj (nodeAt.symm.trans parentAt)
  subst node
  let accessed := CurrentCallSpatialDefaultShared.accessed role tag start amount
  obtain ⟨contract,_,_⟩ := CurrentCallSpatialRead.access_runtime role rfl runtime distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed
  have actualRead : role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed=accessed := by
    simp only [CurrentCallSpatialRows.provenance,concrete,accessed,CurrentCallSpatialDefaultShared.accessed,GeneralBorrowRawSharedExpression.read]
  rw [actualRead] at contract
  have readable := spatial_readable role runtime tag parent concrete mapped start amount startEq amountEq bounds
  obtain ⟨afterParents,afterOwned,afterActive⟩ := read_frame role.backing.allocation.extra tracker.global C runtime parents tag parent target parentNode targetNode
    parentAt mapped targetAt leaf hidden different start amount lower upper bounds readable apart owned active .VisitChildrenOfAccessed contract.tree_eq
  have high := GeneralBorrowForestTagHighWater.complete role.backing.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above role.backing.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have taggedAfter : accessed.tree.indexOfTag tag=some parent := by change accessed.tree.tagMapping.get tag=_;rw [tags];exact mapped
  have parentAfter : accessed.tree.nodeAt parent=some parentNode := by change accessed.tree.nodes.get parent=_;rw [nodes];exact parentAt
  have targetAfter : accessed.tree.nodeAt target=some targetNode := by change accessed.tree.nodes.get target=_;rw [nodes];exact targetAt
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat<(GeneralBorrowFnEntryRegistration.advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have order : parentNode.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime parent parentNode parentAt)
  have primary : ∃node,accessed.tree.nodes.get allocationRoot=some node := by rw [nodes];exact primaryLive
  obtain ⟨done,nextRuntime,cap,growth,child,lookup,frame,nextParents,nextOwned,oldFields⟩ := construct_any accessed.tree
    (GeneralBorrowFnEntryRegistration.advanced tracker.global room) C readRuntime afterParents tag tracker.global.nextPointerTag parent target parentNode targetNode
    taggedAfter parentAfter targetAfter freshAfter roomAfter tagBound false unheld start amount lower upper nonzero boundsAfter apart primary order afterOwned
  have facets := S05SharedConstructorDisjoint.old_facets accessed.tree (GeneralBorrowFnEntryRegistration.advanced tracker.global room) readRuntime
    tag tracker.global.nextPointerTag parent target parentNode targetNode taggedAfter parentAfter targetAfter different freshAfter roomAfter false start amount nonzero boundsAfter .Write lower upper afterActive
  exact ⟨child,lookup,nextParents,nextOwned,facets⟩


open CurrentCallPostEntryCheckpoint in
/-- Equality of actual first live lookups identifies the SAME allocation. -/
theorem same_allocation {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    cp.output.window.allocation=cp.source.role.backing.allocation := by
  have live := cp.output.physical.live
  rw [cp.output.physicalId,same] at live
  have entries := congrArg Prod.snd (Option.some.inj (live.symm.trans cp.sourceLive))
  exact cp.output.physicalAllocation.symm.trans ((congrArg (fun e : LocalAllocation Provenance BorrowTree MiriMemoryKind=>e.allocation) entries).trans cp.sourceAllocation)

open CurrentCallPostEntryCheckpoint in
/-- The concrete checkpoint's SAME-allocation Default Read and r constructor
retain Bool authority and hidden-leaf activity in its own completion. -/
theorem shared_same {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    ∃reader,(CurrentCallCheckpointShared.tree cp).indexOfTag cp.tracker.global.nextPointerTag=some reader ∧
      ParentInterpretation (CurrentCallCheckpointShared.tree cp) (extend cp.output.window.precise.completion reader cp.source.grant) ∧
      OwnedOn (Authority (CurrentCallCheckpointShared.tree cp) (extend cp.output.window.precise.completion reader cp.source.grant)
        cp.tracker.global.protectedTags cp.output.window.pointer.grant) cp.output.physical.offset (cp.output.physical.offset+1) (CurrentCallCheckpointShared.tree cp).locations ∧
      (∃node,(CurrentCallCheckpointShared.tree cp).nodeAt cp.output.window.pointer.grant=some node ∧node.tag=cp.output.node.tag ∧
        node.parent=cp.output.node.parent ∧node.children=cp.output.node.children ∧node.isExposed=cp.output.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointShared.tree cp) cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1) := by
  let Q := CurrentCallCheckpointShared.role cp
  have allocation : cp.output.window.allocation=Q.backing.allocation := same_allocation cp same
  have short : Q.backing.allocation.extra.nodes.size<65536 := by have h:=cp.source.nodes;change Q.backing.allocation.extra.nodes.size+6<65536 at h;omega
  have nodeRoom : Q.backing.allocation.extra.nodes.size+1≤4294967295 := by omega
  have mapped : Q.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant := by
    rw [←cp.source.nodeTag];exact cp.source.runtime.formed.allocator.nodeTags _ _ cp.source.nodeAt
  have targetAt : Q.backing.allocation.extra.nodeAt cp.output.window.pointer.grant=some cp.output.node := by
    change Q.backing.allocation.extra.nodes.get _=_
    rw [←allocation];exact cp.output.nodeAt
  have different : cp.output.window.pointer.grant≠cp.source.grant := by
    intro eq
    rw [eq] at targetAt
    have nodeEq := Option.some.inj (targetAt.symm.trans cp.source.nodeAt)
    exact cp.sourceBoolTags (cp.source.nodeTag.symm.trans (congrArg TreeNode.tag nodeEq).symm)
  have boolEnd : (cp.output.physical.offset+1).toNat=cp.output.offset+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt,cp.output.physicalOffset]
    exact Nat.lt_of_le_of_lt cp.output.physical.bounds cp.output.physical.capacity.toNat_lt
  have initial := (checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") cp.output.window rfl cp.output.runtime
    cp.output.physical.offset (cp.output.physical.offset+1) (by have h:=cp.output.physicalOffset;omega) (by rw [boolEnd];exact Nat.le_refl _)
  have parents : ParentInterpretation Q.backing.allocation.extra cp.output.window.precise.completion := by rw [←allocation];exact cp.output.window.parents
  have owned : OwnedOn (Authority Q.backing.allocation.extra cp.output.window.precise.completion cp.tracker.global.protectedTags cp.output.window.pointer.grant)
      cp.output.physical.offset (cp.output.physical.offset+1) Q.backing.allocation.extra.locations := by rw [←allocation];exact initial
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1) := by rw [←allocation];exact cp.output.activity
  obtain ⟨root,rootAt,_,_,_⟩ := cp.output.window.issued.capability.rootNode
  have primary : ∃node,Q.backing.allocation.extra.nodes.get allocationRoot=some node := by rw [←allocation];exact ⟨root,rootAt⟩
  have nonzero : len≠0 := by intro eq;have h:=cp.source.positive;rw [eq] at h;cases h
  have sourceEnd : (UInt64.ofNat cp.offset+len).toNat=cp.offset+len.toNat := by
    rw [UInt64.toNat_add,CurrentCallCheckpointShared.start_eq cp,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (by simpa only [CurrentCallCheckpointShared.start_eq cp] using CurrentCallCheckpointShared.bounds cp) Q.backing.allocation.extra.locations.size.bytes.toNat_lt
  have apart : ∀point : UInt64,cp.output.physical.offset.toNat≤point.toNat→point.toNat<(cp.output.physical.offset+1).toNat→
      point.toNat<(UInt64.ofNat cp.offset).toNat∨(UInt64.ofNat cp.offset+len).toNat≤point.toNat := by
    intro point lower upper
    by_cases left : point.toNat<cp.offset
    · exact Or.inl (by rw [CurrentCallCheckpointShared.start_eq cp];exact left)
    · by_cases right : cp.offset+len.toNat≤point.toNat
      · exact Or.inr (by rw [sourceEnd];exact right)
      · exact False.elim (cp.separate same (cp.output.id,point.toNat) ⟨same,by omega,by omega⟩ ⟨rfl,by rw [←cp.output.physicalOffset];exact lower,by rw [←boolEnd];exact upper⟩)
  exact shared Q cp.source.runtime cp.source.distinct short nodeRoom cp.output.window.precise.completion parents cp.source.tag cp.source.grant cp.output.window.pointer.grant
    cp.source.node cp.output.node cp.source.concrete mapped cp.source.nodeAt targetAt cp.output.leaf cp.output.hidden different (CurrentCallCheckpointShared.room cp)
    (UInt64.ofNat cp.offset) len cp.output.physical.offset (cp.output.physical.offset+1) rfl rfl nonzero (CurrentCallCheckpointShared.bounds cp) apart primary owned active


theorem observer {before tracker ctx roleOffset roleLength}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut roleOffset roleLength)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (complete : ParentInterpretation role.backing.allocation.extra completion)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (parentTag : BorTag) (source reader target : UniIndex) (readerNode targetNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (sourceTagged : role.backing.allocation.extra.indexOfTag parentTag=some source)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some source) (hidden : readerNode.isExposed=false)
    (readerUnheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (targetAt : role.backing.allocation.extra.nodeAt target=some targetNode)
    (targetLeaf : targetNode.children=#[]) (targetHidden : targetNode.isExposed=false) (different : target≠reader)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (offset len lower upper : UInt64) (offsetEq : offset.toNat=roleOffset) (lenEq : len.toNat=roleLength) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ role.backing.allocation.extra.locations.size.bytes.toNat)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1 ≤ 4294967295) (short : role.backing.allocation.extra.nodes.size+1 < 65536)
    (disjoint : (offset+len).toNat ≤ lower.toNat ∨ upper.toNat ≤ offset.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location tracker.global.protectedTags reader .Read))
      offset (offset+len) role.backing.allocation.extra.locations)
    (targetOwned : OwnedOn (Authority role.backing.allocation.extra completion tracker.global.protectedTags target) lower upper role.backing.allocation.extra.locations)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write lower upper) :
    let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} role.backing.id room
    let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    let released := child.tree.releaseProtector tracker.global.nextPointerTag registration.1.protectedTags
    ∃ helper, child.tree.indexOfTag tracker.global.nextPointerTag = some helper ∧
      ParentInterpretation released.tree (extend completion helper reader) ∧
      (∀query old,role.backing.allocation.extra.nodes.get query=some old→∃next,released.tree.nodes.get query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) ∧
      OwnedOn (Authority released.tree (extend completion helper reader)
        (registration.1.endCall registration.2).protectedTags target) lower upper released.tree.locations ∧
      (∃ next, released.tree.nodeAt target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
        next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released.tree target .Write lower upper := by
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} role.backing.id room
  let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,readRuntime,_⟩ := CurrentCallSpatialLenAssociatedRead.prepare role rfl runtime distinct (by omega)
    parentTag source reader readerNode concrete sourceTagged readerAt readerEdge hidden readerUnheld room offset len offsetEq lenEq nonzero bounds readable .VisitChildrenOfAccessed
  have nodes := contract.nodes
  have roots := contract.roots
  have tags := contract.tags
  have capacity := contract.capacity
  change accessed.tree.nodes=role.backing.allocation.extra.nodes at nodes
  change accessed.tree.roots=role.backing.allocation.extra.roots at roots
  change accessed.tree.tagMapping=role.backing.allocation.extra.tagMapping at tags
  change accessed.tree.locations.size=role.backing.allocation.extra.locations.size at capacity
  have readShape : accessed.tree={role.backing.allocation.extra with locations:=accessed.tree.locations} := contract.tree_eq
  have readComplete : ParentInterpretation accessed.tree completion := by
    rw [readShape]
    exact parents_locations role.backing.allocation.extra completion complete _
  obtain ⟨_,held,_,current,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global {} role.backing.id room runtime
  have flags : ∀ index node, role.backing.allocation.extra.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = tracker.global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get role.backing.allocation.extra.nodes index node).mpr present)))
  have targetRegistered : OwnedOn (Authority role.backing.allocation.extra completion registration.1.protectedTags target) lower upper role.backing.allocation.extra.locations := by
    intro cursor valid positive start stop index node present
    rw [flags index node present]
    exact targetOwned cursor valid positive start stop index node present
  have pointDisjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat := by
    intro point start stop
    rcases disjoint with before | after <;> omega
  have targetAfter : accessed.tree.nodeAt target = some targetNode := by
    change accessed.tree.nodes.get target = _
    rw [nodes]
    exact targetAt
  have targetOwnedRead : OwnedOn (Authority accessed.tree completion registration.1.protectedTags target) lower upper accessed.tree.locations := by
    have retained := GeneralBorrowRangeOutsideOwned.owned (Authority role.backing.allocation.extra completion registration.1.protectedTags target)
      role.backing.allocation.extra (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
      runtime.formed.well bounds lower upper pointDisjoint targetRegistered
    intro cursor valid positive start stop index node present
    exact retained cursor valid positive start stop index node (by rw [nodes] at present;exact present)
  have readRegistered : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location registration.1.protectedTags reader .Read))
      offset (offset+len) role.backing.allocation.extra.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := readable cursor valid positive start stop
    have projection := GeneralBorrowProtector.normal_projection role.backing.allocation.extra role.backing.allocation.extra.locations.entries[cursor].data tracker.global.protectedTags
      tracker.global.nextPointerTag .StrongProtector nodeFresh
    refine ⟨⟨normal.component,?_⟩⟩
    intro index included bounded
    have table : registration.1.protectedTags = tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector := rfl
    rw [table,projection]
    exact normal.permissions index included bounded
  have targetActiveRead : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree target .Write lower upper :=
    CurrentCallReadRootActivity.concrete_of_normal role.backing.allocation.extra registration.1 current readerNode.tag reader target readerNode readerAt
      offset len bounds readRegistered (runtime.formed.allocator.nodeTags reader readerNode readerAt)
      targetNode targetAt targetLeaf targetHidden different lower upper targetActive .VisitChildrenOfAccessed
  have present : accessed.tree.nodeAt reader = some readerNode := by change accessed.tree.nodes.get reader = _;rw [nodes];exact readerAt
  have tagged : accessed.tree.indexOfTag readerNode.tag = some reader := readRuntime.formed.allocator.nodeTags reader readerNode present
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have nodeRoomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have heldTag : registration.1.protectedTags.contains tracker.global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have tagBound : tracker.global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have step := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have lengthPositive : 0<roleLength := by
    have positive : 0<len.toNat := Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
    omega
  have first : CandidateStableCallOwnership.Window role.backing.id roleOffset roleLength (role.backing.id,roleOffset) := ⟨rfl,Nat.le_refl _,by omega⟩
  obtain ⟨cell,contains⟩ := role.covered _ first
  let overlap : CurrentCallSpatialSourceCover.Active role cell := ⟨_,first,contains⟩
  obtain ⟨root,rootAt,_,_,_⟩ := (role.roles cell overlap).issued.capability.rootNode
  have primary : ∃node,accessed.tree.nodes.get allocationRoot=some node := by rw [nodes];exact ⟨root,rootAt⟩
  have parentOrder : readerNode.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime reader readerNode readerAt)
  obtain ⟨_,childRuntime,_,_,helper,lookup,childFrame,childParents,boolOwned,oldFields⟩ := construct_any accessed.tree registration.1 completion
    readRuntime readComplete readerNode.tag tracker.global.nextPointerTag reader target readerNode targetNode tagged present targetAfter freshAfter nodeRoomAfter
    tagBound true heldTag offset len lower upper nonzero boundsAfter pointDisjoint primary parentOrder targetOwnedRead
  obtain ⟨⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩,boolActive⟩ := S05SharedConstructorDisjoint.old_facets
    accessed.tree registration.1 readRuntime readerNode.tag tracker.global.nextPointerTag reader target readerNode targetNode tagged present targetAfter different
    freshAfter nodeRoomAfter true offset len nonzero boundsAfter .Write lower upper targetActiveRead
  let afterTree := (accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree
  have normalRead : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read))
      offset (offset+len) accessed.tree.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := contract.rows cursor valid positive start stop
    have transport (location : LocationTree)
        (old : DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location registration.1.protectedTags reader .Read) :
        Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read) := by
      rw [readShape]
      exact ⟨⟨old.component,old.permissions⟩⟩
    exact transport _ normal
  obtain ⟨_,_,_,_,capHelper,capLookup,capabilities⟩ := GeneralBorrowSharedReadConstructor.construct accessed.tree registration.1
    readRuntime readerNode.tag tracker.global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter normalRead
  have capEq : capHelper = helper := Option.some.inj (capLookup.symm.trans lookup)
  subst capHelper
  obtain ⟨activeIndex,activeAt,activeWithin⟩ := (S05SharedChildActivity.construct accessed.tree registration.1 readRuntime readerNode.tag tracker.global.nextPointerTag
    reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter).2
  have activeEq : activeIndex = helper := Option.some.inj (activeAt.symm.trans lookup)
  subst activeIndex
  obtain ⟨graphHelper,graphLookup,⟨helperNode,helperAt,helperTag,helperEdge,helperHidden⟩,_⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree registration.1
    readRuntime readerNode.tag tracker.global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter true offset len nonzero boundsAfter
  have graphEq : graphHelper = helper := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphHelper
  have helperWrite := GeneralBorrowFreshActiveWithin.to_write afterTree helper offset (offset+len) activeWithin
  have preserved := S02DisjointReleaseFrame.release afterTree registration.1.protectedTags tracker.global.nextPointerTag helper helper helperNode lookup helperAt helperHidden
    offset (offset+len) helperWrite helperWrite (Authority afterTree (extend completion helper reader) registration.1.protectedTags target)
    lower upper disjoint boolOwned childRuntime.formed.well
  have targetDifferent : target ≠ helper := by
    intro equal
    have same := Option.some.inj (nextAt.symm.trans (equal ▸ helperAt))
    have oldFresh := nodeFresh (target,targetNode) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get role.backing.allocation.extra.nodes target targetNode).mpr targetAt))
    apply oldFresh
    exact nextTag.symm.trans ((congrArg TreeNode.tag same).trans helperTag)
  have boolActiveRelease := CurrentCallReadRootActivity.release afterTree registration.1 childRuntime tracker.global.nextPointerTag helper target helperNode next
    lookup helperAt helperHidden nextAt (nextChildren.trans targetLeaf) (nextHidden.trans targetHidden) targetDifferent
    offset (offset+len) lower upper activeWithin
    (fun cursor valid positive start stop => (capabilities cursor valid positive start stop).2) boolActive
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release afterTree registration.1.protectedTags tracker.global.nextPointerTag
  refine ⟨helper,lookup,?_,?_,?_,?_,boolActiveRelease⟩
  · rw [releaseFrame]
    exact parents_locations afterTree (extend completion helper reader) childParents _
  · intro query old atOld
    have atRead : accessed.tree.nodeAt query=some old := by change accessed.tree.nodes.get query=some old;rw [nodes];exact atOld
    obtain ⟨changed,changedAt,tagEq,parentEq,exposureEq,defaultEq⟩ := oldFields query old atRead
    refine ⟨changed,?_,tagEq,parentEq,exposureEq,defaultEq⟩
    change (afterTree.releaseProtector tracker.global.nextPointerTag registration.1.protectedTags).tree.nodes.get query=some changed
    rw [releaseFrame]
    exact changedAt
  · intro cursor valid positive start stop index node nodeAt
    have oldAt : afterTree.nodes.get index = some node := by
      change (afterTree.releaseProtector tracker.global.nextPointerTag registration.1.protectedTags).tree.nodes.get index = some node at nodeAt
      rw [releaseFrame] at nodeAt
      exact nodeAt
    have authority := preserved cursor valid positive start stop index node oldAt
    have weaken := GeneralBorrowRelease.end_call_weakens registration.1 registration.2 node.tag
    refine ⟨?_,?_⟩
    · intro below
      obtain ⟨possible,disabled,frozen,reserved⟩ := authority.1 below
      exact ⟨possible,disabled,frozen,fun held => reserved (weaken held)⟩
    · intro outside
      obtain ⟨possible,quiet⟩ := authority.2 outside
      exact ⟨possible,fun held => quiet (weaken held)⟩
  · refine ⟨next,?_,nextTag,nextParent,nextChildren,nextHidden⟩
    change (afterTree.releaseProtector tracker.global.nextPointerTag registration.1.protectedTags).tree.nodeAt target = some next
    rw [releaseFrame]
    exact nextAt

open CurrentCallPostEntryCheckpoint in
theorem checkpoint_apart {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    (UInt64.ofNat cp.offset+len).toNat≤cp.output.physical.offset.toNat ∨
      (cp.output.physical.offset+1).toNat≤(UInt64.ofNat cp.offset).toNat := by
  have startEq := CurrentCallCheckpointShared.start_eq cp
  have sourceEnd : (UInt64.ofNat cp.offset+len).toNat=cp.offset+len.toNat := by
    rw [UInt64.toNat_add,startEq,Nat.mod_eq_of_lt]
    have bound := CurrentCallCheckpointShared.bounds cp
    change (UInt64.ofNat cp.offset).toNat+len.toNat≤cp.source.role.backing.allocation.extra.locations.size.bytes.toNat at bound
    rw [startEq] at bound
    exact Nat.lt_of_le_of_lt bound cp.source.role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have boolEnd : (cp.output.physical.offset+1).toNat=cp.output.offset+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt,cp.output.physicalOffset]
    exact Nat.lt_of_le_of_lt cp.output.physical.bounds cp.output.physical.capacity.toNat_lt
  rw [sourceEnd,boolEnd,startEq,cp.output.physicalOffset]
  by_cases before : cp.offset+len.toNat≤cp.output.offset
  · exact Or.inl before
  · right
    by_cases after : cp.output.offset+1≤cp.offset
    · exact after
    · exact False.elim (cp.separate same (cp.output.id,cp.output.offset) ⟨same,by omega,by omega⟩ ⟨rfl,Nat.le_refl _,by omega⟩)

open CurrentCallPostEntryCheckpoint in
/-- SAME checkpoint Shared/r, Strong/h and actual h release retain the Bool
bank. The two parent extensions are common actual reader/helper indices. -/
theorem same_after_helper {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    let p := CurrentCallCheckpointLen.prepared cp
    let registration := GeneralBorrowFnEntryRegistration.registered (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room
    let accessed := p.source.backing.allocation.extra.performBorrowAccessRange (.concrete p.readerNode.tag) (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := accessed.tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete p.readerNode.tag) (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    let released := child.tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag registration.1.protectedTags
    ∃helper,child.tree.indexOfTag (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag=some helper ∧
      ParentInterpretation released.tree (extend (extend cp.output.window.precise.completion p.reader cp.source.grant) helper p.reader) ∧
      (∀query old,p.source.backing.allocation.extra.nodes.get query=some old→∃next,released.tree.nodes.get query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) ∧
      OwnedOn (Authority released.tree (extend (extend cp.output.window.precise.completion p.reader cp.source.grant) helper p.reader)
        (registration.1.endCall registration.2).protectedTags cp.output.window.pointer.grant)
        cp.output.physical.offset (cp.output.physical.offset+1) released.tree.locations ∧
      (∃node,released.tree.nodeAt cp.output.window.pointer.grant=some node ∧node.tag=cp.output.node.tag ∧node.parent=cp.output.node.parent ∧node.children=cp.output.node.children ∧node.isExposed=cp.output.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released.tree cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1) := by
  let p := CurrentCallCheckpointLen.prepared cp
  obtain ⟨reader,lookup,parents,owned,⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,active⟩ := shared_same cp same
  have readerLookup : (CurrentCallCheckpointShared.tree cp).indexOfTag cp.tracker.global.nextPointerTag=some p.reader := by
    rw [←p.tree,←p.readerTag]
    exact p.runtime.formed.allocator.nodeTags _ _ p.readerAt
  have readerEq : reader=p.reader := Option.some.inj (lookup.symm.trans readerLookup)
  subst reader
  have parentCurrent : ParentInterpretation p.source.backing.allocation.extra (extend cp.output.window.precise.completion p.reader cp.source.grant) := by rw [p.tree];exact parents
  have ownedCurrent : OwnedOn (Authority p.source.backing.allocation.extra (extend cp.output.window.precise.completion p.reader cp.source.grant)
      (CurrentCallCheckpointShared.tracker cp).global.protectedTags cp.output.window.pointer.grant) cp.output.physical.offset (cp.output.physical.offset+1) p.source.backing.allocation.extra.locations := by rw [p.tree];exact owned
  have targetAt : p.source.backing.allocation.extra.nodeAt cp.output.window.pointer.grant=some node := by rw [p.tree];exact nodeAt
  have activeCurrent : GeneralBorrowFreshActiveWithin.ActiveWithin p.source.backing.allocation.extra cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1) := by rw [p.tree];exact active
  have different : cp.output.window.pointer.grant≠p.reader := by
    intro eq
    rw [eq] at targetAt
    have nodeEq := Option.some.inj (targetAt.symm.trans p.readerAt)
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh _ _ cp.output.runtime _ cp.output.node cp.output.nodeAt
    rw [←nodeTag,nodeEq,p.readerTag] at older
    exact (UInt64.lt_irrefl _ older)
  have nonzero : len≠0 := by intro eq;have h:=cp.source.positive;rw [eq] at h;cases h
  obtain ⟨helper,hLookup,hParents,old,retained,⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩,activity⟩ := observer p.source
    (extend cp.output.window.precise.completion p.reader cp.source.grant) p.runtime parentCurrent p.distinct cp.source.tag cp.source.grant p.reader cp.output.window.pointer.grant
    p.readerNode node p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld targetAt (nodeChildren.trans cp.output.leaf) (nodeHidden.trans cp.output.hidden)
    different p.room (UInt64.ofNat cp.offset) len cp.output.physical.offset (cp.output.physical.offset+1) rfl rfl nonzero p.bounds p.nodeRoom
    (by have h:=cp.source.nodes;have growth:=(CurrentCallCheckpointShared.operation cp).2.2.2.2.1;rw [p.tree];change (CurrentCallCheckpointShared.role cp).backing.allocation.extra.nodes.size+6<65536 at h;omega)
    (checkpoint_apart cp same) p.readable ownedCurrent activeCurrent
  exact ⟨helper,hLookup,hParents,old,retained,⟨next,nextAt,nextTag.trans nodeTag,nextParent.trans nodeParent,nextChildren.trans nodeChildren,nextHidden.trans nodeHidden⟩,activity⟩


private theorem parents_completion {tree : BorrowTree} {oldC newC : Completion}
    (equal : oldC=newC) (old : ParentInterpretation tree oldC) : ParentInterpretation tree newC := by cases equal;exact old
private theorem owned_completion {tree : BorrowTree} {oldC newC : Completion} {flags target lower upper}
    (equal : oldC=newC) (old : OwnedOn (Authority tree oldC flags target) lower upper tree.locations) :
    OwnedOn (Authority tree newC flags target) lower upper tree.locations := by cases equal;exact old
private theorem owned_flags {tree : BorrowTree} {C : Completion} {oldF newF target lower upper}
    (equal : oldF=newF) (old : OwnedOn (Authority tree C oldF target) lower upper tree.locations) :
    OwnedOn (Authority tree C newF target) lower upper tree.locations := by cases equal;exact old
open CurrentCallPostEntryCheckpoint in
def completion {options remaining span len count place} (cp : Checkpoint options remaining span len count place) : Completion :=
  extend (extend cp.output.window.precise.completion (CurrentCallCheckpointLen.prepared cp).reader cp.source.grant)
    (CurrentCallCheckpointLenControl.helperIndex cp) (CurrentCallCheckpointLen.prepared cp).reader

open CurrentCallPostEntryCheckpoint in
/-- Named actual helper-return/release tree used by the common control leaf. -/
theorem same_named {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    ParentInterpretation (CurrentCallCheckpointLenControl.releasedTree cp) (completion cp) ∧
    OwnedOn (Authority (CurrentCallCheckpointLenControl.releasedTree cp) (completion cp)
      (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags cp.output.window.pointer.grant)
      cp.output.physical.offset (cp.output.physical.offset+1) (CurrentCallCheckpointLenControl.releasedTree cp).locations ∧
    (∃node,(CurrentCallCheckpointLenControl.releasedTree cp).nodeAt cp.output.window.pointer.grant=some node ∧node.tag=cp.output.node.tag ∧
      node.parent=cp.output.node.parent ∧node.children=cp.output.node.children ∧node.isExposed=cp.output.node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointLenControl.releasedTree cp) cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1) := by
  let p := CurrentCallCheckpointLen.prepared cp
  obtain ⟨helper,lookup,parents,old,owned,facets,active⟩ := same_after_helper cp same
  have idEq : p.source.backing.id=cp.source.role.backing.id := by
    rw [←p.source.id,p.family]
    exact (CurrentCallCheckpointShared.role cp).id
  have treeEq : p.source.backing.allocation.extra=CurrentCallCheckpointShared.tree cp := p.tree
  have finalEq : CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len =
      CurrentCallCheckpointLenControl.borrowedTree cp := by
    rw [treeEq,p.readerTag]
    rfl
  change (CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).indexOfTag _=some helper at lookup
  rw [finalEq] at lookup
  have helperEq : CurrentCallCheckpointLenControl.helperIndex cp=helper := by
    unfold CurrentCallCheckpointLenControl.helperIndex
    rw [lookup]
    rfl
  have releasedEq : ((CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.held cp).global.protectedTags).tree =
      CurrentCallCheckpointLenControl.releasedTree cp := by rw [finalEq];rfl
  change ParentInterpretation ((CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.held cp).global.protectedTags).tree _ at parents
  rw [releasedEq] at parents
  have releaseFlags : (GeneralBorrowFnEntryRegistration.registered (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room).1.endCall
      (GeneralBorrowFnEntryRegistration.registered (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room).2 =
      (CurrentCallCheckpointLenControl.postTracker cp).global := by
    rw [idEq]
    rfl
  change OwnedOn (Authority _ _ _ _) _ _ _ at owned
  change OwnedOn (Authority ((CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.held cp).global.protectedTags).tree _ _ _) _ _ _ at owned
  rw [releasedEq] at owned
  change GeneralBorrowFreshActiveWithin.ActiveWithin ((CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.held cp).global.protectedTags).tree _ _ _ _ at active
  rw [releasedEq] at active
  change (∃node,((CurrentCallLenArgumentCopy.finalTree p.source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp) p.readerNode.tag (UInt64.ofNat cp.offset) len).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.held cp).global.protectedTags).tree.nodeAt _=some node ∧_) at facets
  rw [releasedEq] at facets
  have completionEq : extend (extend cp.output.window.precise.completion p.reader cp.source.grant) helper p.reader=completion cp :=
    congrArg (fun index=>extend (extend cp.output.window.precise.completion p.reader cp.source.grant) index p.reader) helperEq.symm
  have namedParents :=  parents_completion completionEq parents
  have namedOwned := owned
  rw [completionEq] at namedOwned
  have flagEq := congrArg GlobalState.protectedTags releaseFlags
  rw [flagEq] at namedOwned
  have literalReleasedEq :
      (((p.source.backing.allocation.extra.performBorrowAccessRange (.concrete p.readerNode.tag)
          (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len) .Read
          (GeneralBorrowFnEntryRegistration.registered (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room).1.protectedTags
          .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete p.readerNode.tag)
          (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
          (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree.releaseProtector
          (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
          (GeneralBorrowFnEntryRegistration.registered (CurrentCallCheckpointShared.tracker cp).global {} p.source.backing.id p.room).1.protectedTags).tree
        =CurrentCallCheckpointLenControl.releasedTree cp := by
    rw [p.tree,p.readerTag]
    rfl
  rw [literalReleasedEq] at namedOwned
  have namedOwnedFlags := namedOwned
  exact ⟨namedParents,namedOwnedFlags,facets,active⟩


private theorem remove_fresh_insert (flags : ProtectedTags) (tag : BorTag)
    (fresh : ∀row∈flags.entries,row.1≠tag) : (flags.insert tag .StrongProtector).remove tag=flags := by
  have filtered : flags.entries.filter (fun row=>row.1!=tag)=flags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using fresh row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,filtered]

open CurrentCallPostEntryCheckpoint in
theorem final_flags {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags=cp.tracker.global.protectedTags := by
  change (cp.tracker.global.protectedTags.insert (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag .StrongProtector).remove
    (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag=cp.tracker.global.protectedTags
  apply remove_fresh_insert
  intro row member equal
  have below := cp.source.runtime.below.protectors row member
  have successor := GenericFunctionEntryNumerics.successor_value cp.tracker.global.nextPointerTag (CurrentCallCheckpointShared.room cp)
  change (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat=cp.tracker.global.nextPointerTag.value.toNat+1 at successor
  rw [equal] at below
  omega

open CurrentCallPostEntryCheckpoint in
theorem final_counter {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat=cp.tracker.global.nextPointerTag.value.toNat+2 := by
  have first := GenericFunctionEntryNumerics.successor_value cp.tracker.global.nextPointerTag (CurrentCallCheckpointShared.room cp)
  have second := GenericFunctionEntryNumerics.successor_value (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (CurrentCallCheckpointLenControl.room cp)
  change (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat=cp.tracker.global.nextPointerTag.value.toNat+1 at first
  change (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat=(CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat+1 at second
  omega

open CurrentCallPostEntryCheckpoint in
theorem final_root {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) (id : AllocId) :
    (CurrentCallCheckpointLenControl.postTracker cp).global.rootTag? id=cp.tracker.global.rootTag? id := by rfl

open CurrentCallPostEntryCheckpoint in
theorem different_runtime {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    DuplicatePrefixBorrowContract.RuntimeFacts cp.output.window.allocation.extra (CurrentCallCheckpointLenControl.postTracker cp).global := by
  have flags := final_flags cp
  have counter := final_counter cp
  refine ⟨by rw [flags];exact cp.output.runtime.formed,by rw [flags];exact cp.output.runtime.coherent,cp.output.runtime.possible,⟨?_,?_⟩⟩
  · intro row member;exact Nat.lt_of_lt_of_le (cp.output.runtime.below.mapping row member) (by omega)
  · intro row member
    rw [flags] at member
    exact Nat.lt_of_lt_of_le (cp.output.runtime.below.protectors row member) (by omega)

/-- Install only the retained Bool family in the ACTUAL final world. The
finite pointer/loan slots are unchanged; only the precise completion is appended. -/
theorem install {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (post : Before) (next : MachineHooks.BorrowState) (tree : BorrowTree) (C : Completion)
    (present : Present (ActualWorld post) id (B.allocation.setExtra tree))
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree next.global)
    (parents : ParentInterpretation tree C)
    (capacity : tree.locations.size=B.allocation.extra.locations.size)
    (roots : ∀(position : Nat) (root : UniIndex),B.allocation.extra.roots[position]?=some root→tree.roots[position]?=some root)
    (metadata : ∀query old,B.allocation.extra.nodes.get query=some old→∃changed,tree.nodes.get query=some changed ∧
      changed.tag=old.tag ∧changed.parent=old.parent ∧changed.isExposed=old.isExposed ∧changed.defaultInitialPermission=old.defaultInitialPermission)
    (edges : ∀(query origin : UniIndex),B.precise.completion.parents[query.toNat]?=some (some origin)→C.parents[query.toNat]?=some (some origin))
    (start : UInt64) (startEq : start.toNat=offset)
    (owned : OwnedOn (Authority tree C next.global.protectedTags B.pointer.grant) start (start+1) tree.locations) :
    ∃nextData,∃Q : UniformWindow post next nextData owner id offset 1 .ret,
      Q.pointer=B.pointer ∧Q.loan=B.loan ∧Q.allocation=B.allocation.setExtra tree ∧Q.precise.completion=C := by
  have issued := CurrentCallAllocationLicense.spatial B.issued post next (B.allocation.setExtra tree) present rootTag rfl rfl capacity roots metadata C edges
  have binding : PointerBinds (B.allocation.setExtra tree) B.pointer := by
    obtain ⟨node,found,_,provenance⟩ := B.binding
    obtain ⟨changed,changedAt,tag,parent,exposure,_⟩ := metadata B.pointer.grant node found
    refine ⟨changed,changedAt,runtime.formed.allocator.nodeTags _ _ changedAt,?_⟩
    cases prov : B.pointer.value.provenance with
    | concrete supplied parentTag=>simp only [prov] at provenance ⊢;exact ⟨provenance.1,provenance.2.trans tag.symm⟩
    | wildcard=>simp only [prov] at provenance ⊢;exact exposure.trans provenance
  have firstByte := (B.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have endFits : start.toNat+1<2^64 := by
    have cap:=UInt64.toNat_lt B.allocation.byteSize.bytes
    have extent:=B.issued.capability.extent
    omega
  have endEq : (start+1).toNat=offset+1 := by rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endFits,startEq]
  let nextData : Identities := {data with interpretation:={data.interpretation with precise:=data.interpretation.precise.push (id,{B.precise with completion:=C})}}
  let Q : UniformWindow post next nextData owner id offset 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation.setExtra tree,precise:={B.precise with completion:=C}
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=B.pointerId,present:=present,preciseAt:=by simp [nextData]
    binding:=binding,issued:=issued,parents:=parents,window:=by
      intro byte inside
      refine ⟨(B.window byte inside).1,?_⟩
      intro segment member lower upper index node found
      obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      change tree.locations.entries[position].range.start.toNat≤byte.2 at lower
      change byte.2<tree.locations.entries[position].range.stop.toNat at upper
      have rights := owned position valid (by omega) (by have h:=inside.2;omega) (by have h:=inside.2;omega) index node found
      have realized:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node found) ((runtime.formed.profile position valid).present index node found)
      exact ⟨fun below=>(checkpoint_bool_rule "CurrentCallResourceCopyInstall.local_token") _ _ realized (rights.1 below),
        fun clash=>Classical.byContradiction (fun outside=>(checkpoint_bool_rule "CurrentCallResourceCopyInstall.foreign_no_clash") _ _ realized (rights.2 outside) clash)⟩}
  exact ⟨nextData,Q,rfl,rfl,rfl,rfl⟩


open CurrentCallPostEntryCheckpoint in
private theorem release_tree_eq {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    ((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree=CurrentCallCheckpointLenControl.releasedTree cp := by
  exact (congrArg (fun tree : BorrowTree=>(tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree) (CurrentCallCheckpointLenRelease.actual_eq cp)).trans
      (congrArg (fun global : GlobalState=>((CurrentCallCheckpointLenControl.borrowedTree cp).releaseProtector
        (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag global.protectedTags).tree) (CurrentCallCheckpointLenRelease.held_eq cp))

private theorem edge_extend {tree : BorrowTree} {C : Completion}
    (parents : ParentInterpretation tree C) (child parent : UniIndex)
    (vacant : tree.nodes.get child=none) (query origin : UniIndex)
    (edge : C.parents[query.toNat]?=some (some origin)) :
    (extend C child parent).parents[query.toNat]?=some (some origin) := by
  obtain ⟨node,present⟩ := (parents.edgeLive query origin edge).1
  have different : query≠child := by intro eq;rw [eq,vacant] at present;cases present
  rw [old_parent C child parent query different (by rw [parents.dimension];exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present)]
  exact edge

open CurrentCallPostEntryCheckpoint in
theorem same_metadata {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) :
    (∀query old,cp.output.window.allocation.extra.nodes.get query=some old→∃next,
      (CurrentCallCheckpointLenControl.releasedTree cp).nodes.get query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧
      next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) ∧
    (∀(query origin : UniIndex),cp.output.window.precise.completion.parents[query.toNat]?=some (some origin)→
      (completion cp).parents[query.toNat]?=some (some origin)) := by
  let p := CurrentCallCheckpointLen.prepared cp
  have allocation := same_allocation cp same
  obtain ⟨helper,lookup,_,old,_,_,_⟩ := same_after_helper cp same
  change ∀query old,p.source.backing.allocation.extra.nodes.get query=some old→∃next,
    (((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree).nodes.get query=some next ∧_ at old
  rw [release_tree_eq cp] at old
  obtain ⟨reader,rNode,rLookup,rAt,rTag,rParent,rHidden,roots,qMeta,qActivity,sharedOld⟩ := CurrentCallCheckpointShared.metadata cp
  have readerLookup : (CurrentCallCheckpointShared.tree cp).indexOfTag cp.tracker.global.nextPointerTag=some p.reader := by
    rw [←p.tree,←p.readerTag];exact p.runtime.formed.allocator.nodeTags _ _ p.readerAt
  have readerEq : reader=p.reader := Option.some.inj (rLookup.symm.trans readerLookup)
  subst reader
  have metadata : ∀query previous,cp.source.role.backing.allocation.extra.nodes.get query=some previous→∃next,
      (CurrentCallCheckpointLenControl.releasedTree cp).nodes.get query=some next ∧next.tag=previous.tag ∧next.parent=previous.parent ∧
      next.isExposed=previous.isExposed ∧next.defaultInitialPermission=previous.defaultInitialPermission := by
    intro query previous atPrevious
    obtain ⟨middle,middleAt,middleTag,middleParent,middleHidden,middleDefault⟩ := sharedOld query previous atPrevious
    have middleCurrent : p.source.backing.allocation.extra.nodes.get query=some middle := by rw [p.tree];exact middleAt
    obtain ⟨next,nextAt,nextTag,nextParent,nextHidden,nextDefault⟩ := old query middle middleCurrent
    exact ⟨next,nextAt,nextTag.trans middleTag,nextParent.trans middleParent,nextHidden.trans middleHidden,nextDefault.trans middleDefault⟩
  refine ⟨?_,?_⟩
  · intro query previous atPrevious
    rw [allocation] at atPrevious
    exact metadata query previous atPrevious
  · have rVacant : cp.source.role.backing.allocation.extra.nodes.get p.reader=none := by
      cases atOld : cp.source.role.backing.allocation.extra.nodes.get p.reader with
      | none=>rfl
      | some previous=>
        obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := sharedOld p.reader previous atOld
        have nodeEq := Option.some.inj (changedAt.symm.trans rAt)
        have older := GeneralBorrowParentTagInvariant.parent_below_fresh _ _ cp.source.runtime p.reader previous atOld
        rw [←changedTag,nodeEq,rTag] at older
        exact False.elim (UInt64.lt_irrefl _ older)
    have nonzero : len≠0 := by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
    obtain ⟨h,hNode,hLookup,hAt,hTag,hParent,hHidden,hVacant,_⟩ := CurrentCallCheckpointLenMetadata.graph p.source rfl p.runtime p.distinct p.short p.nodeRoom
      cp.source.tag cp.source.grant p.reader p.readerNode p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room
      (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
    have hLookupNamed : (CurrentCallCheckpointLenControl.borrowedTree cp).indexOfTag (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag=some h := by
      change (CurrentCallCheckpointLenRelease.actual cp).tree.indexOfTag _=some h at hLookup
      rw [CurrentCallCheckpointLenRelease.actual_eq cp] at hLookup
      exact hLookup
    have hEq : CurrentCallCheckpointLenControl.helperIndex cp=h := by
      unfold CurrentCallCheckpointLenControl.helperIndex;rw [hLookupNamed];rfl
    obtain ⟨r,rLookupExact,rParents,_,_,_⟩ := shared_same cp same
    have rEq : r=p.reader := Option.some.inj (rLookupExact.symm.trans readerLookup)
    subst r
    have firstParents : ParentInterpretation p.source.backing.allocation.extra (extend cp.output.window.precise.completion p.reader cp.source.grant) := by rw [p.tree];exact rParents
    have originalParents : ParentInterpretation cp.source.role.backing.allocation.extra cp.output.window.precise.completion := by rw [←allocation];exact cp.output.window.parents
    intro query origin edge
    have first := edge_extend originalParents p.reader cp.source.grant rVacant query origin edge
    have second := edge_extend firstParents h p.reader hVacant query origin first
    change (extend (extend cp.output.window.precise.completion p.reader cp.source.grant) (CurrentCallCheckpointLenControl.helperIndex cp) p.reader).parents[query.toNat]?=some (some origin)
    rw [hEq]
    exact second


open CurrentCallPostEntryCheckpoint in
/-- Runtime and physical graph geometry of the same completed observer release. -/
theorem geometry {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place)
    (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointLenControl.releasedTree cp) (CurrentCallCheckpointLenControl.postTracker cp).global ∧
    (CurrentCallCheckpointLenControl.releasedTree cp).locations.size=cp.source.role.backing.allocation.extra.locations.size ∧
    (CurrentCallCheckpointLenControl.releasedTree cp).roots=cp.source.role.backing.allocation.extra.roots ∧
    (CurrentCallCheckpointLenControl.releasedTree cp).nodes.size≤cp.source.role.backing.allocation.extra.nodes.size+2 := by
  let p := CurrentCallCheckpointLen.prepared cp
  have nonzero : len≠0 := by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨done,runtime,shape,capacity,context,Q,allocation,idEq,treeEq,family,rows⟩ := CurrentCallCheckpointLenRelease.release cp result.helper
  obtain ⟨_,_,hRuntime,hCapacity,hGrowth,h,hLookup,caps,active,cells⟩ := CurrentCallCheckpointLen.operations cp
  have finalRuntime := CurrentCallCheckpointLenRuntime.runtime cp result
  have sharedCapacity := (CurrentCallCheckpointShared.operation cp).2.2.2.1
  have sharedGrowth := (CurrentCallCheckpointShared.operation cp).2.2.2.2.1
  change (CurrentCallCheckpointLenRelease.actual cp).tree.locations.size=p.source.backing.allocation.extra.locations.size at hCapacity
  change (CurrentCallCheckpointLenRelease.actual cp).tree.nodes.size≤p.source.backing.allocation.extra.nodes.size+1 at hGrowth
  have rawNodes := congrArg BorrowTree.nodes shape
  change (((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree).nodes=(CurrentCallCheckpointLenRelease.actual cp).tree.nodes at rawNodes
  rw [release_tree_eq cp] at rawNodes
  obtain ⟨_,_,leaf,_⟩ := CurrentCallCheckpointLenMetadata.frame p.source rfl p.runtime p.distinct p.short p.nodeRoom cp.source.tag cp.source.grant p.reader p.readerNode
    p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  obtain ⟨contract,_,_⟩ := CurrentCallSpatialLenAssociatedRead.prepare p.source rfl p.runtime p.distinct p.short cp.source.tag cp.source.grant p.reader p.readerNode
    p.concrete p.tagged p.readerAt p.readerEdge p.hidden p.unheld p.room (UInt64.ofNat cp.offset) len rfl rfl nonzero p.bounds p.readable .VisitChildrenOfAccessed
  have hRoots := leaf.roots.trans contract.roots
  change (CurrentCallCheckpointLenRelease.actual cp).tree.roots=p.source.backing.allocation.extra.roots at hRoots
  obtain ⟨_,_,_,_,_,_,_,sharedRoots,_⟩ := CurrentCallCheckpointShared.metadata cp
  have rawRoots := congrArg BorrowTree.roots shape
  change (((CurrentCallCheckpointLenRelease.actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    (CurrentCallCheckpointLenRelease.registered cp).global.protectedTags).tree).roots=(CurrentCallCheckpointLenRelease.actual cp).tree.roots at rawRoots
  rw [release_tree_eq cp] at rawRoots
  refine ⟨finalRuntime,?_,?_,?_⟩
  · rw [←release_tree_eq cp,capacity,hCapacity,p.tree]
    exact sharedCapacity
  · rw [rawRoots,hRoots,p.tree]
    exact sharedRoots
  · have sizeEq := congrArg (fun nodes : UniValMap TreeNode=>nodes.size) rawNodes
    rw [sizeEq]
    rw [p.tree] at hGrowth
    have oldGrowth : (CurrentCallCheckpointShared.tree cp).nodes.size≤cp.source.role.backing.allocation.extra.nodes.size+1 := sharedGrowth
    omega


open CurrentCallPostEntryCheckpoint in
def allocation {options remaining span len count place} (cp : Checkpoint options remaining span len count place) : Allocation Provenance BorrowTree :=
  if cp.output.id=cp.source.role.backing.id then (CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)
  else cp.output.window.allocation

open CurrentCallPostEntryCheckpoint in
def bank {options remaining span len count place} (cp : Checkpoint options remaining span len count place) : Completion :=
  if cp.output.id=cp.source.role.backing.id then completion cp else cp.output.window.precise.completion

open CurrentCallPostEntryCheckpoint in
def entry {options remaining span len count place} (cp : Checkpoint options remaining span len count place) : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  if cp.output.id=cp.source.role.backing.id then {cp.sourceEntry with allocation:=allocation cp}
  else {cp.output.physical.entry with allocation:=allocation cp}

open CurrentCallPostEntryCheckpoint in
theorem allocation_same {options remaining span len count place} (cp : Checkpoint options remaining span len count place)
    (same : cp.output.id=cp.source.role.backing.id) : allocation cp=cp.output.window.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp) := by
  dsimp only [allocation]
  rw [ite_eq_left same]
  change cp.sourceEntry.allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)=_
  rw [cp.sourceAllocation,←same_allocation cp same]

open CurrentCallPostEntryCheckpoint in
theorem allocation_different {options remaining span len count place} (cp : Checkpoint options remaining span len count place)
    (different : cp.output.id≠cp.source.role.backing.id) : allocation cp=cp.output.window.allocation := by
  simp only [allocation,ite_eq_right different]

open CurrentCallPostEntryCheckpoint in
theorem entry_allocation {options remaining span len count place} (cp : Checkpoint options remaining span len count place) :
    (entry cp).allocation=allocation cp := by by_cases same : cp.output.id=cp.source.role.backing.id <;>simp only [entry,same,↓reduceIte]

open CurrentCallPostEntryCheckpoint in
theorem live {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
    (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    result.machine.memory.live.find? (fun row=>row.1==cp.output.id)=some (cp.output.id,entry cp) := by
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have actual := result.sourceLive
    simpa only [entry,allocation,ite_eq_left same,same,CurrentCallCheckpointLenControl.entry,↓reduceIte] using actual
  · have oldLive : cp.machine.memory.live.find? (fun row=>row.1==cp.output.id)=some (cp.output.id,cp.output.physical.entry) := by
      rw [←cp.output.physicalId]
      exact cp.output.physical.live
    have intermediate := StackPopRelease.lookup_commit_other cp.machine.memory cp.source.role.backing.id cp.output.id cp.sourceEntry
      cp.output.physical.entry (CurrentCallCheckpointShared.tree cp) same oldLive
    change (CurrentCallCheckpointShared.machine cp).memory.live.find? (fun row=>row.1==cp.output.id)=some (cp.output.id,cp.output.physical.entry) at intermediate
    simp only [entry,ite_eq_right same,allocation_different cp same,←cp.output.physicalAllocation]
    rw [result.memory]
    exact StackPopRelease.lookup_commit_other (CurrentCallCheckpointShared.machine cp).memory cp.source.role.backing.id cp.output.id
      (CurrentCallCheckpointLenControl.entry cp) cp.output.physical.entry (CurrentCallCheckpointLenControl.releasedTree cp) same intermediate

open CurrentCallPostEntryCheckpoint in
theorem present {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
    (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    Present (ActualWorld result.machine) cp.output.id (allocation cp) := by
  simp only [Present,ActualWorld,Array.toList_map]
  have actual := live cp result
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some actual)
  have value : (cp.output.id,allocation cp)=(cp.output.id,(entry cp).allocation) := by rw [entry_allocation cp]
  rw [value]
  exact List.mem_map.mpr ⟨_,member,rfl⟩

open CurrentCallPostEntryCheckpoint in
structure Resources {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) where
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (allocation cp).extra (CurrentCallCheckpointLenControl.postTracker cp).global
  parents : ParentInterpretation (allocation cp).extra (bank cp)
  owned : OwnedOn (Authority (allocation cp).extra (bank cp) (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags cp.output.window.pointer.grant)
    cp.output.physical.offset (cp.output.physical.offset+1) (allocation cp).extra.locations
  distinct : (allocation cp).extra.roots.toList.Nodup
  short : (allocation cp).extra.nodes.size<65536
  capacity : (allocation cp).extra.locations.size=cp.output.window.allocation.extra.locations.size
  roots : (allocation cp).extra.roots=cp.output.window.allocation.extra.roots
  metadata : ∀query old,cp.output.window.allocation.extra.nodes.get query=some old→∃next,(allocation cp).extra.nodes.get query=some next ∧
    next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission
  edges : ∀(query origin : UniIndex),cp.output.window.precise.completion.parents[query.toNat]?=some (some origin)→(bank cp).parents[query.toNat]?=some (some origin)
  node : TreeNode
  nodeAt : (allocation cp).extra.nodeAt cp.output.window.pointer.grant=some node
  tag : node.tag=cp.output.node.tag
  parent : node.parent=cp.output.node.parent
  leaf : node.children=#[]
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin (allocation cp).extra cp.output.window.pointer.grant .Write cp.output.physical.offset (cp.output.physical.offset+1)

open CurrentCallPostEntryCheckpoint in
theorem resources {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) : Nonempty (Resources cp result) := by
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have alloc := allocation_same cp same
    have tree := congrArg Allocation.extra alloc
    dsimp only [Allocation.setExtra,Allocation.mapExtra] at tree
    have C : bank cp=completion cp := by simp only [bank,ite_eq_left same]
    obtain ⟨parents,owned,⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,activity⟩ := same_named cp same
    obtain ⟨runtime,capacity,roots,growth⟩ := geometry cp result
    obtain ⟨metadata,edges⟩ := same_metadata cp same
    have oldAlloc := same_allocation cp same
    have capacityOld : (CurrentCallCheckpointLenControl.releasedTree cp).locations.size=cp.output.window.allocation.extra.locations.size := by rw [oldAlloc];exact capacity
    have rootsOld : (CurrentCallCheckpointLenControl.releasedTree cp).roots=cp.output.window.allocation.extra.roots := by rw [oldAlloc];exact roots
    refine ⟨{
      runtime:=?_,parents:=?_,owned:=?_,distinct:=?_,short:=?_,capacity:=?_,roots:=?_,metadata:=?_,edges:=?_,
      node:=node,nodeAt:=?_,tag:=nodeTag,parent:=nodeParent,leaf:=nodeChildren.trans cp.output.leaf,hidden:=nodeHidden.trans cp.output.hidden,activity:=?_}⟩
    · rw [tree];exact runtime
    · rw [tree,C];exact parents
    · rw [tree,C];exact owned
    · rw [tree,rootsOld];exact cp.output.distinct
    · rw [tree]
      have margin:=cp.source.nodes
      omega
    · rw [tree];exact capacityOld
    · rw [tree];exact rootsOld
    · rw [tree];exact metadata
    · rw [C];exact edges
    · rw [tree];exact nodeAt
    · rw [tree];exact activity
  · have alloc := allocation_different cp same
    have C : bank cp=cp.output.window.precise.completion := by simp only [bank,ite_eq_right same]
    have endEq : (cp.output.physical.offset+1).toNat=cp.output.offset+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt,cp.output.physicalOffset]
      exact Nat.lt_of_le_of_lt cp.output.physical.bounds cp.output.physical.capacity.toNat_lt
    have initial := (checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") cp.output.window rfl cp.output.runtime
      cp.output.physical.offset (cp.output.physical.offset+1) (by have h:=cp.output.physicalOffset;omega) (by rw [endEq];exact Nat.le_refl _)
    refine ⟨{
      runtime:=?_,parents:=?_,owned:=?_,distinct:=?_,short:=?_,capacity:=?_,roots:=?_,metadata:=?_,edges:=?_,
      node:=cp.output.node,nodeAt:=?_,tag:=rfl,parent:=rfl,leaf:=cp.output.leaf,hidden:=cp.output.hidden,activity:=?_}⟩
    · rw [alloc];exact different_runtime cp
    · rw [alloc,C];exact cp.output.window.parents
    · rw [alloc,C,final_flags cp];exact initial
    · rw [alloc];exact cp.output.distinct
    · rw [alloc];exact cp.output.short
    · rw [alloc]
    · rw [alloc]
    · rw [alloc];intro query old found;exact ⟨old,found,rfl,rfl,rfl,rfl⟩
    · rw [C];intro query origin edge;exact edge
    · rw [alloc];exact cp.output.nodeAt
    · rw [alloc];exact cp.output.activity

open CurrentCallPostEntryCheckpoint in
theorem allocation_extra {options remaining span len count place} (cp : Checkpoint options remaining span len count place) :
    allocation cp=cp.output.window.allocation.setExtra (allocation cp).extra := by
  by_cases same : cp.output.id=cp.source.role.backing.id
  · rw [allocation_same cp same]
    dsimp only [Allocation.setExtra,Allocation.mapExtra]
  · rw [allocation_different cp same]
    dsimp only [Allocation.setExtra,Allocation.mapExtra]

open CurrentCallPostEntryCheckpoint in
theorem window {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    ∃data,∃Q : UniformWindow result.machine (CurrentCallCheckpointLenControl.postTracker cp) data cp.output.owner cp.output.id cp.output.offset 1 .ret,
      Q.pointer=cp.output.window.pointer ∧Q.loan=cp.output.window.loan ∧Q.allocation=allocation cp ∧Q.precise.completion=bank cp := by
  obtain ⟨R⟩ := resources cp result
  have actual := present cp result
  rw [allocation_extra cp] at actual
  obtain ⟨data,Q,pointer,loan,allocated,completed⟩ := install cp.output.window result.machine (CurrentCallCheckpointLenControl.postTracker cp)
    (allocation cp).extra (bank cp) actual (final_root cp cp.output.id) R.runtime R.parents R.capacity
    (by intro position root found;rw [R.roots];exact found) R.metadata R.edges cp.output.physical.offset cp.output.physicalOffset R.owned
  exact ⟨data,Q,pointer,loan,allocated.trans (allocation_extra cp).symm,completed⟩

open CurrentCallPostEntryCheckpoint in
theorem original_issued {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    SpatialDelegation result.machine (CurrentCallCheckpointLenControl.postTracker cp) cp.output.id (allocation cp) (bank cp) cp.output.original.grant := by
  obtain ⟨R⟩ := resources cp result
  apply CurrentCallAllocationLicense.spatial cp.output.originalIssued result.machine (CurrentCallCheckpointLenControl.postTracker cp) (allocation cp)
    (present cp result) (final_root cp cp.output.id)
  · rw [allocation_extra cp]
    dsimp only [Allocation.setExtra,Allocation.mapExtra]
    rfl
  · rw [allocation_extra cp]
    dsimp only [Allocation.setExtra,Allocation.mapExtra]
    rfl
  · exact R.capacity
  · intro position root found;rw [R.roots];exact found
  · exact R.metadata
  · exact R.edges

open CurrentCallPostEntryCheckpoint in
theorem original_binding {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    PointerBinds (allocation cp) cp.output.original := by
  obtain ⟨R⟩ := resources cp result
  obtain ⟨node,found,_,provenance⟩ := cp.output.originalBinding
  obtain ⟨changed,changedAt,tag,parent,exposure,_⟩ := R.metadata cp.output.original.grant node found
  refine ⟨changed,changedAt,R.runtime.formed.allocator.nodeTags _ _ changedAt,?_⟩
  cases prov : cp.output.original.value.provenance with
  | concrete supplied parentTag=>simp only [prov] at provenance ⊢;exact ⟨provenance.1,provenance.2.trans tag.symm⟩
  | wildcard=>simp only [prov] at provenance ⊢;exact exposure.trans provenance

open CurrentCallPostEntryCheckpoint in
theorem edge {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    (bank cp).parents[cp.output.window.pointer.grant.toNat]?=some (some cp.output.original.grant) := by
  obtain ⟨R⟩ := resources cp result
  exact R.edges _ _ cp.output.edge

open CurrentCallPostEntryCheckpoint in
private theorem shared_addresses {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    (CurrentCallCheckpointShared.machine cp).user.addresses=cp.machine.user.addresses := by
  change (RootZeroCompleteState.tick options remaining span cp.machine).user.addresses=cp.machine.user.addresses
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl
open CurrentCallPostEntryCheckpoint in
private theorem shared_extras {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    (CurrentCallCheckpointShared.machine cp).user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras := by
  change (RootZeroCompleteState.tick options remaining span cp.machine).user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

open CurrentCallPostEntryCheckpoint in
theorem addresses {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    result.machine.user.addresses=cp.machine.user.addresses :=
  result.flags.addresses.trans (result.helper.addresses.trans (shared_addresses cp))

open CurrentCallPostEntryCheckpoint in
theorem extras {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    result.machine.user.payload.payload.user.runtime.extras=cp.machine.user.payload.payload.user.runtime.extras :=
  result.flags.extras.trans (result.helper.extras.trans (shared_extras cp))

open CurrentCallPostEntryCheckpoint in
theorem entry_bool {options remaining span len count place} (cp : Checkpoint options remaining span len count place) :
    entry cp={cp.output.physical.entry with allocation:=cp.output.physical.entry.allocation.setExtra (allocation cp).extra} := by
  have alloc : allocation cp=cp.output.physical.entry.allocation.setExtra (allocation cp).extra := by
    rw [cp.output.physicalAllocation]
    exact allocation_extra cp
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have oldLive := cp.output.physical.live
    rw [cp.output.physicalId,same] at oldLive
    have oldEntry : cp.output.physical.entry=cp.sourceEntry := congrArg Prod.snd (Option.some.inj (oldLive.symm.trans cp.sourceLive))
    simp only [entry,ite_eq_left same]
    rw [←oldEntry]
    exact congrArg (fun updated : Allocation Provenance BorrowTree=>{cp.output.physical.entry with allocation:=updated}) alloc
  · simp only [entry,ite_eq_right same]
    exact congrArg (fun updated : Allocation Provenance BorrowTree=>{cp.output.physical.entry with allocation:=updated}) alloc

open CurrentCallPostEntryCheckpoint in
def scalar {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    CurrentCallBoolScalarWrite.Window result.machine place :=
  {cp.output.physical with
    entry:={cp.output.physical.entry with allocation:=cp.output.physical.entry.allocation.setExtra (allocation cp).extra}
    live:=by
      have actual := live cp result
      rw [entry_bool cp] at actual
      rw [cp.output.physicalId]
      exact actual
    cachedBase:=by rw [addresses cp result];exact cp.output.physical.cachedBase}

open CurrentCallPostEntryCheckpoint in
theorem scalar_allocation {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    (scalar cp result).entry.allocation=allocation cp := by
  change cp.output.physical.entry.allocation.setExtra (allocation cp).extra=allocation cp
  rw [cp.output.physicalAllocation]
  exact (allocation_extra cp).symm

open CurrentCallPostEntryCheckpoint in
theorem binding {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    CandidateCallBindings.WindowBinding result.machine cp.output.physical.pointer cp.output.id cp.output.offset 1 := by
  obtain ⟨oldEntry,base,oldLive,cached,byteLength,room,bounds,address,nonnull,provenance⟩ := cp.output.binding
  have physicalLive := cp.output.physical.live
  rw [cp.output.physicalId] at physicalLive
  have oldEq : oldEntry=cp.output.physical.entry := congrArg Prod.snd (Option.some.inj (oldLive.symm.trans physicalLive))
  rw [oldEq,cp.output.physicalAllocation] at byteLength room bounds provenance
  have lenEq : (allocation cp).len=cp.output.window.allocation.len := by
    calc
      (allocation cp).len=(cp.output.window.allocation.setExtra (allocation cp).extra).len := congrArg Allocation.len (allocation_extra cp)
      _=cp.output.window.allocation.len := rfl
  have sizeEq : (allocation cp).byteSize=cp.output.window.allocation.byteSize := by
    calc
      (allocation cp).byteSize=(cp.output.window.allocation.setExtra (allocation cp).extra).byteSize := congrArg Allocation.byteSize (allocation_extra cp)
      _=cp.output.window.allocation.byteSize := rfl
  refine ⟨entry cp,base,live cp result,?_,?_,?_,?_,address,nonnull,?_⟩
  · rw [addresses cp result];exact cached
  · rw [entry_allocation,lenEq,sizeEq];exact byteLength
  · rw [entry_allocation,lenEq];exact room
  · rw [entry_allocation,lenEq];exact bounds
  · rw [addresses cp result,entry_allocation,sizeEq]
    exact provenance

open CurrentCallPostEntryCheckpoint in
structure Packet {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) where
  current : Return result.machine (CurrentCallCheckpointLenControl.postTracker cp) place
  id : current.id=cp.output.id
  offset : current.offset=cp.output.offset
  pointer : current.window.pointer=cp.output.window.pointer
  original : current.original=cp.output.original
  allocated : current.window.allocation=allocation cp
  completion : current.window.precise.completion=bank cp
  tag : current.node.tag=cp.output.node.tag
  parent : current.node.parent=cp.output.node.parent

open CurrentCallPostEntryCheckpoint in
/-- The actual common helper-pop machine retains the protected Bool child and
its ORIGINAL return destination license in both allocation cases. -/
theorem invoke {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place) (result : CurrentCallCheckpointLenReturn.Result cp limits) :
    Nonempty (Packet cp result) := by
  obtain ⟨R⟩ := resources cp result
  obtain ⟨data,Q,pointer,loan,allocated,completed⟩ := window cp result
  let current : Return result.machine (CurrentCallCheckpointLenControl.postTracker cp) place := {
    data:=data,owner:=cp.output.owner,id:=cp.output.id,offset:=cp.output.offset,window:=Q,physical:=scalar cp result
    physicalId:=cp.output.physicalId,physicalOffset:=cp.output.physicalOffset
    physicalAllocation:=(scalar_allocation cp result).trans allocated.symm
    binding:=binding cp result,original:=cp.output.original,originalId:=cp.output.originalId,originalPointer:=cp.output.originalPointer
    originalIssued:=by rw [allocated,completed];exact original_issued cp result
    originalBinding:=by rw [allocated];exact original_binding cp result
    edge:=by rw [pointer,completed];exact edge cp result
    runtime:=by rw [allocated];exact R.runtime
    distinct:=by rw [allocated];exact R.distinct
    short:=by rw [allocated];exact R.short
    node:=R.node,nodeAt:=by rw [allocated,pointer];exact R.nodeAt
    leaf:=R.leaf,hidden:=R.hidden
    activity:=by rw [allocated,pointer];exact R.activity
    profile:=CurrentCallBoolProtection.WindowReady.transport cp.output.profile (extras cp result)}
  exact ⟨{current:=current,id:=rfl,offset:=rfl,pointer:=pointer,original:=rfl,allocated:=allocated,completion:=completed,tag:=R.tag,parent:=R.parent}⟩


end
end DuplicatePrefix.CurrentCallCheckpointSharedBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointSharedBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Bool dependency {dependency}"
