import duplicate_prefix.CurrentCallSharedReference
import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.GeneralBorrowSharedCapabilityConstructor
import duplicate_prefix.GeneralBorrowSharedChildParentTagOrder
import duplicate_prefix.S05CompletedAncestryRangeRead
import duplicate_prefix.S05DefaultSharedAuthority
import duplicate_prefix.GeneralBorrowRawSharedFnEntry
import duplicate_prefix.CurrentCallLenArgumentCopy
import duplicate_prefix.PushThread
import duplicate_prefix.CurrentCallLenSharedFrame
import duplicate_prefix.S05CurrentReadProtectorRelease
import duplicate_prefix.S05SharedChildActivity
import duplicate_prefix.GeneralBorrowSharedReadConstructor
import duplicate_prefix.S05UnprotectedSharedOldAuthority
import duplicate_prefix.S05CompletedAncestryObserverRead
import duplicate_prefix.S05CurrentLenAssociatedRead
import duplicate_prefix.LenReturnFromReleaseRuntime
import duplicate_prefix.CurrentCallEntryProtectionData
import duplicate_prefix.GeneralBorrowRawTargetActivity

namespace DuplicatePrefix.CurrentCallLen
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership GeneralBorrowProjection
open S05ConcreteProtectedChildCompletion
open GeneralBorrowRawSharedExpression
open CanonicalConfigFacts ActualReferenceContext CurrentCallLenArgumentCopy
open LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
open GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority GeneralBorrowWildcardParentTagOrder
open GeneralBorrowExposureCardinality GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem get_none (tags : ProtectedTags) (tag : BorTag) (unheld : tags.contains tag = false) : tags.get tag = none := by
  cases found : tags.get tag with
  | none => rfl
  | some kind => simp [ProtectedTags.contains,found] at unheld

private def old_core (before after : BorrowTree) : Prop :=
  ∀ index node, before.nodes.get index = some node →
    ∃ next, after.nodes.get index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed

private theorem physical_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    tree.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (node.parent = none ↔ index ∈ tree.roots.toList) := by
  obtain ⟨forest⟩ := runtime.formed.forest default global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree default global.protectedTags forest depth
  refine ⟨runtime.formed.allocator.nodeTags index node present,?_,?_⟩
  · intro child
    constructor
    · intro member
      obtain ⟨childNode,childAt⟩ := runtime.formed.children index node present child member
      let topology := (source_normal_projection tree default global.protectedTags).topology
      have size : topology.nodes.size = tree.nodes.data.size := by
        unfold topology
        unfold_general_projection
        unfold_general_topology
        simp only [Array.size_map]
      have indexValid : index.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
      have childValid : child.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ childAt
      have parentProjection := projection_topology_node tree default global.protectedTags index.toNat index node rfl present
      have childProjection := projection_topology_node tree default global.protectedTags child.toNat child childNode rfl childAt
      change (topology.nodes[index.toNat]?.getD ⟨none,[]⟩) = _ at parentProjection
      change (topology.nodes[child.toNat]?.getD ⟨none,[]⟩) = _ at childProjection
      simp only [Array.getElem?_eq_getElem indexValid,Option.getD_some] at parentProjection
      simp only [Array.getElem?_eq_getElem childValid,Option.getD_some] at childProjection
      have projectedMember : child.toNat ∈ (topology.nodes[index.toNat]'indexValid).children := by
        rw [parentProjection]
        exact List.mem_map.mpr ⟨child,member,rfl⟩
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat indexValid child.toNat projectedMember
      rw [childProjection] at edge
      have parentEq : childNode.parent = some index := by
        cases h : childNode.parent with
        | none => simp [h] at edge
        | some actual =>
          simp only [h,Option.map_some] at edge
          have same : actual = index := GeneralBorrowNodeUpdate.index_injective _ _ (Option.some.inj edge)
          exact congrArg some same
      exact ⟨childNode,childAt,parentEq⟩
    · rintro ⟨childNode,childAt,edge⟩
      obtain ⟨parentNode,parentAt,member⟩ := reciprocal child childNode childAt index edge
      have same : parentNode = node := Option.some.inj (parentAt.symm.trans present)
      simpa only [same] using member
  · constructor
    · exact runtime.formed.covered index node present
    · intro member
      obtain ⟨rootNode,rootAt,parentless⟩ := runtime.formed.rootNodes index member
      have same : node = rootNode := Option.some.inj (present.symm.trans rootAt)
      simpa only [same] using parentless

open GeneralBorrowView GeneralBorrowFreshGraph

set_option maxHeartbeats 200000 in
private theorem shared_frame (tree after : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts after global)
    (child parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations))
    (size : after.nodes.data.size = max tree.nodes.data.size (child.toNat+1))
    (roots : after.roots = tree.roots) : LeafFrame tree after child parent := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshAnchor.sharedNode newTag parent) mapping locations
  have different : parent ≠ child := by
    intro same; rw [same,vacant] at parentAt; cases parentAt
  have parentStage : stage.nodes.get parent = some (updatedParent parentNode child) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,updatedParent]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have childStage : stage.nodes.get child = some (GeneralBorrowFreshAnchor.sharedNode newTag parent) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same]
  have otherStage : ∀ query, query ≠ parent → query ≠ child → stage.nodes.get query = tree.nodes.get query := by
    intro query notParent notChild
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ notParent,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
  refine ⟨vacant,size,roots,⟨parentNode,parentAt⟩,?_,?_,?_,physical_runtime after global runtime⟩
  · obtain ⟨next,found,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape child _ childStage
    exact ⟨next,found,parentEq⟩
  · intro query node present
    have notChild : query ≠ child := by intro same; rw [same,vacant] at present; cases present
    have staged : ∃ stagedNode, stage.nodes.get query = some stagedNode ∧
        stagedNode.tag = node.tag ∧ stagedNode.parent = node.parent ∧ stagedNode.isExposed = node.isExposed := by
      by_cases same : query = parent
      · subst query
        have nodeEq : node = parentNode := Option.some.inj (present.symm.trans parentAt)
        subst node
        exact ⟨_,parentStage,rfl,rfl,rfl⟩
      · exact ⟨node,(otherStage query same notChild).trans present,rfl,rfl,rfl⟩
    obtain ⟨stagedNode,stagedAt,tagEq,parentEq,exposedEq⟩ := staged
    obtain ⟨next,found,tagAfter,parentAfter,_,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape query stagedNode stagedAt
    have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure query
    rw [found,stagedAt] at flags
    have sameExposure : next.isExposed = stagedNode.isExposed := by
      simpa only [Option.map_some,Option.some.injEq] using flags
    exact ⟨next,found,tagAfter.trans tagEq,parentAfter.trans parentEq,sameExposure.trans exposedEq⟩
  · intro query node present
    by_cases same : query = child
    · exact Or.inl same
    · right
      obtain ⟨stagedNode,stagedAt,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after stage shape.symm query node present
      by_cases isParent : query = parent
      · subst query
        have nodeEq : stagedNode = updatedParent parentNode child := Option.some.inj (stagedAt.symm.trans parentStage)
        exact ⟨parentNode,parentAt,by simpa only [nodeEq,updatedParent] using parentEq.symm⟩
      · exact ⟨stagedNode,(otherStage query isParent same).symm.trans stagedAt,parentEq.symm⟩

/-- Actual concrete protected child construction extends the SAME completed
origin assignment, including sparse vacant-slot reuse. The input runtime/tree
is the post-parent-Read state; no callback Positive or future rights are inputs. -/
private theorem shared_completion (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (isProtected : Bool) (held : global.protectedTags.contains newTag = isProtected)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        S05ConcreteProtectedChildCompletion.LeafFrame tree actual.tree child parent ∧ Completes actual.tree (extend completion child parent) ∧
        (∀ ancestor, Below completion ancestor parent → Below (extend completion child parent) ancestor child) := by
  have output := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound isProtected held offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,runtime.formed.well,bounds⟩
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
    have frame := shared_frame tree (GeneralBorrowFreshMetadataChildShared.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildShared.mapping input)
      (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.shape input)
      (GeneralBorrowFreshMetadataChildShared.exposure input) size data.roots
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,isProtected,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have size : (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.size = _
      rw [data.size]
      change tree.nodes.data.size = _
      omega
    have frame := shared_frame tree (GeneralBorrowFreshMetadataChildSharedReuse.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
      (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
      (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) size data.roots
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩
private theorem default_shared (tree : BorrowTree) (global : GlobalState)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : CandidateStableCallOwnership.Completes tree completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : tree.roots[position]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode)
    (parentPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected parent)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags parent)
      offset (offset+len) tree.locations) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global room
    (read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed).status = .Completed ∧
    (child tree advanced.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () ∧
    let result := (child tree advanced.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    DuplicatePrefixBorrowContract.RuntimeFacts result advanced ∧ result.locations.size = tree.locations.size ∧
    result.nodes.size ≤ tree.nodes.size+1 ∧ ∃ child,
      result.indexOfTag global.nextPointerTag = some child ∧
      S05ConcreteProtectedChildCompletion.LeafFrame (read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed).tree result child parent ∧
      CandidateStableCallOwnership.Completes result (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowSharedCapabilityRange.Both result advanced.protectedTags parent child)
        offset (offset+len) result.locations ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority result (extend completion child parent) advanced.protectedTags parent)
        offset (offset+len) result.locations ∧
      ParentTagOrder result ∧ ∃ node, result.nodes.get child = some node ∧ node.tag = global.nextPointerTag ∧
        node.parent = some parent ∧ node.isExposed = false ∧ old_core tree result ∧
        (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len) →
          GeneralBorrowFreshActiveWithin.ActiveWithin result target .Write offset (offset+len)) := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global room
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced = allocated := congrArg Prod.fst
    (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by
      simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced,GeneralBorrowFnEntryRegistration.advanced] using below⟩
  obtain ⟨depth⟩ := current.formed.depth
  have rows : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion advanced.protectedTags parent location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨current.possible cursor valid,owned cursor valid positive start stop⟩
  have accessed := S05CompletedAncestryReadMutable.range tree completion advanced.protectedTags complete
    current.formed.toGraphState depth order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows current.formed.well
    (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let after := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
  have same : after.tree = {tree with locations := after.tree.locations} := accessed.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts after.tree advanced := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,accessed.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(accessed.runtime cursor valid).2.1.present,(accessed.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid; exact (accessed.runtime cursor valid).1
    · intro cursor valid; exact (accessed.runtime cursor valid).2.2
  have tagged : after.tree.indexOfTag parentNode.tag = some parent := by
    unfold BorrowTree.indexOfTag
    change (tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed).tree.tagMapping.get parentNode.tag = _
    rw [accessed.tags]
    exact (complete.2.2.2.2.1 parent parentNode parentPresent).1
  have present : after.tree.nodeAt parent = some parentNode := by
    change after.tree.nodes.get parent = some parentNode
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using parentPresent
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping global.nextPointerTag := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.tags] using fresh
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have afterComplete : Completes after.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have afterOwned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority after.tree completion advanced.protectedTags parent)
      offset (offset+len) after.tree.locations := by
    intro cursor valid positive start stop index node nodeAt
    have authority := (accessed.rows cursor valid positive start stop).2
    exact authority index node (by simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeAt)
  have nodeRoomAfter : after.tree.nodes.size+1 ≤ 4294967295 := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ after.tree.locations.size.bytes.toNat := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.capacity] using bounds
  have normalRows : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Normal after.tree location advanced.protectedTags parent))
      offset (offset+len) after.tree.locations := by
    have rootAt : after.tree.nodes.get selected = some selectedNode := by
      simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using selectedPresent
    have rootSlot : after.tree.roots[position]? = some selected := by
      simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.roots] using slot
    have path : GeneralBorrowExposedNonleafPrimaryPath.Path after.tree selected parent :=
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := after.tree) (after := tree) accessed.nodes.symm parentPath
    obtain ⟨afterDepth⟩ := afterRuntime.formed.depth
    have fits : after.tree.nodes.data.size ≤ 4294967296 := by change after.tree.nodes.size ≤ _;omega
    intro cursor valid positive start stop
    have authority := afterOwned cursor valid positive start stop
    exact S05CompletedAncestryNormal.normal after.tree completion _ advanced.protectedTags afterComplete
      afterRuntime.formed.toGraphState afterDepth fits position selected parent selectedNode rootSlot rootAt path
      (fun index node found _ => (authority index node found).1)
      (fun index node found _ => (authority index node found).2)
  obtain ⟨done,resultRuntime,capacity,growth,index,lookup,frame,resultComplete,_⟩ := shared_completion after.tree advanced completion
    afterRuntime afterComplete parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter
    tagBound false unheld offset len nonzero boundsAfter
  obtain ⟨_,_,_,_,capIndex,capLookup,capabilities⟩ := GeneralBorrowSharedCapabilityConstructor.construct after.tree advanced afterRuntime
    parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter tagBound unheld offset len nonzero boundsAfter normalRows
  have equal : capIndex = index := Option.some.inj (capLookup.symm.trans lookup)
  subst capIndex
  obtain ⟨_,_,_,_,authorityIndex,authorityLookup,parentAuthority⟩ := S05DefaultSharedAuthority.construct after.tree advanced completion
    afterRuntime afterComplete parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter tagBound unheld
    offset len nonzero boundsAfter afterOwned
  have authorityEqual : authorityIndex = index := Option.some.inj (authorityLookup.symm.trans lookup)
  subst authorityIndex
  obtain ⟨graphIndex,graphLookup,⟨newNode,newAt,newTag,newParent,newHidden⟩,oldNodes⟩ := GeneralBorrowSharedChildGraph.construct after.tree advanced
    afterRuntime parentNode.tag global.nextPointerTag parent parentNode tagged present freshAfter nodeRoomAfter false offset len nonzero boundsAfter
  have graphEqual : graphIndex = index := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphIndex
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame tree after.tree accessed.nodes order
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent parentNode parentPresent
  have resultOrder := GeneralBorrowSharedChildParentTagOrder.construct after.tree advanced afterRuntime parentNode.tag global.nextPointerTag
    parent parentNode tagged present freshAfter nodeRoomAfter false offset len nonzero boundsAfter readOrder
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older)))
  refine ⟨accessed.completed,done,resultRuntime,capacity.trans accessed.capacity,?_,index,lookup,frame,resultComplete,capabilities,
    parentAuthority,resultOrder,newNode,newAt,newTag,newParent,newHidden,?_,?_⟩
  · simpa only [after,GeneralBorrowRawSharedExpression.read,GeneralBorrowRawSharedExpression.child,accessed.nodes] using growth
  · intro query node nodeAt
    exact oldNodes query node (by change after.tree.nodes.get query = _;rw [same];exact nodeAt)
  · intro target active
    have afterActive := GeneralBorrowFreshActiveWithinAccess.normal tree parentNode.tag (Size.ofBytes offset) (Size.ofBytes len) .Read
      advanced.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
    exact GeneralBorrowRawTargetActivity.shared after.tree advanced afterRuntime parentNode.tag global.nextPointerTag parent parentNode
      tagged present freshAfter nodeRoomAfter false offset len nonzero boundsAfter target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) afterActive


private theorem reader_range (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        DuplicatePrefixScalarAuthorization.Compatible ((location.perms.get index).getD node.defaultLocationState) .Read
          (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
          (protections.contains node.tag)) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index →
          (Below completion index source → LocalWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
          (¬Below completion index source → ForeignWrite
            ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))))
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
        ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
          ∀ index node, tree.nodes.get index = some node → Path tree root index →
            (Below completion index source → LocalWrite
              ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
            (¬Below completion index source → ForeignWrite
              ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
      (fun location => LocationCoherent tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
      (fun before after => before = after ∨
        ∀ index node, tree.nodes.get index = some node → Path tree selected index →
          after.perms.get index =
            (tree.performNormalAccessAt before reader .Read protections mode).location.perms.get index)
      lower upper (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read protections mode) := by
  have mapped : tree.indexOfTag readerNode.tag = some reader :=
    (complete.2.2.2.2.1 reader readerNode readerPresent).1
  apply GeneralBorrowConcreteRangeEntry.access tree protections readerNode.tag reader mapped offset len .Read mode
    _ _ _ _ (fun _ initial => ⟨initial.1,initial.2.2⟩) (fun _ => Or.inl rfl) _
    lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := S05CompletedAncestryConcreteRead.access tree completion location protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath reader readerPath authority.2.1
    (fun position root slot different index node present path below =>
      (authority.2.2 position root slot different index node present path).1 below)
    (fun position root slot different index node present path outside =>
      (authority.2.2 position root slot different index node present path).2 outside)
    representation.1 representation.2.1 authority.1 short mode range
  refine ⟨row.1,⟨row.2.2.2.1,?_⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,Or.inr row.2.2.2.2.1⟩
  intro position root slot different index node present path
  exact ⟨row.2.2.2.2.2.1 position root slot different index node present path,
    row.2.2.2.2.2.2 position root slot different index node present path⟩

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

/-- The actual protected Len FnEntry associated Read, from the current Frozen
reader and the retained old-source authority. The fresh Strong registration
and every normal/other-root callback are derived, not successful inputs. -/
theorem prepare_len_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (readerAt : tree.nodes.get reader = some readerNode)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size < 65536)
    (readable : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty
      (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations) :
    let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
    let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
      registration.1.protectedTags .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
    Completes accessed.tree completion ∧ accessed.tree.nodes = tree.nodes ∧ accessed.tree.roots = tree.roots ∧
    accessed.tree.tagMapping = tree.tagMapping ∧ accessed.tree.locations.size = tree.locations.size ∧
    OwnedOn (S05CurrentReadProtectorRelease.Authority tree completion registration.1.protectedTags root source reader)
      offset (offset+len) accessed.tree.locations := by
  obtain ⟨_,_,_,current,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp
        ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  obtain ⟨depth⟩ := current.formed.depth
  obtain ⟨actualRoot,actualRootAt,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have sameRoot : actualRoot = rootNode := Option.some.inj (actualRootAt.symm.trans rootAt)
  subst actualRoot
  have rows : OwnedOn (S05CurrentReadProtectorRelease.Authority tree completion registration.1.protectedTags root source reader)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := readable cursor valid positive start stop
    have authority := owned cursor valid positive start stop
    refine ⟨current.possible cursor valid,?_,?_⟩
    · apply GeneralBorrowPhysicalNormalCapability.of_physical_component tree _ registration.1.protectedTags
        current.formed.toGraphState current.formed.fits root reader rootNode rootAt parentless readerPath .Read
      intro index node present path
      rw [flags index node present]
      exact capability_selected tree _ global.protectedTags runtime.formed.toGraphState root reader readerPath normal index node present path
    · intro otherPosition otherRoot slot different index node present path
      rw [flags index node present]
      exact authority index node present
  have result := S05CompletedAncestryReadCapability.access tree completion registration.1.protectedTags complete
    current.formed.toGraphState depth order position root source reader rootNode readerNode rootSlot rootAt sourcePath readerAt readerPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows current.formed.well
    (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
    registration.1.protectedTags .VisitChildrenOfAccessed
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 := by
    rw [result.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,result.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(result.runtime cursor valid).2.1.present,(result.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid;exact (result.runtime cursor valid).1
    · intro cursor valid;exact (result.runtime cursor valid).2.2
  have afterComplete : Completes accessed.tree completion := by
    rw [result.tree_eq]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  exact ⟨result.completed,afterRuntime,afterComplete,result.nodes,result.roots,result.tags,result.capacity,result.rows⟩

/-- The actual protected shared borrowing operation used by Len's FnEntry.
Its associated Read and real Frozen constructor both derive internally. -/
theorem len_operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (readerAt : tree.nodes.get reader = some readerNode)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (readable : OwnedOn (fun location => Nonempty
      (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read)) offset (offset+len) tree.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations) :
    ∃ output, GeneralBorrowRawSharedFnEntry.operation tree global frame allocation readerNode.tag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧ ∃ child,
      output.child.tree.indexOfTag output.tag = some child ∧
      Completes output.child.tree (extend completion child reader) ∧ LeafFrame output.access.tree output.child.tree child reader ∧
      OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities output.child.tree output.global.protectedTags reader child)
        offset (offset+len) output.child.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Read offset (offset+len) := by
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
  let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
    registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone,readRuntime,readComplete,nodes,roots,tags,capacity,readOwned⟩ := prepare_len_read tree global frame allocation completion runtime
    complete order position root source reader rootNode readerNode rootSlot rootAt sourcePath readerAt readerPath room offset len bounds short readable owned
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at readRuntime
  change Completes accessed.tree completion at readComplete
  obtain ⟨allocated,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  have present : accessed.tree.nodeAt reader = some readerNode := by change accessed.tree.nodes.get reader = _;rw [nodes];exact readerAt
  have tagged : accessed.tree.indexOfTag readerNode.tag = some reader := (readComplete.2.2.2.2.1 reader readerNode present).1
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have nodeRoomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨childDone,afterRuntime,_,_,child,lookup,leaf,afterComplete,_⟩ := shared_completion accessed.tree registration.1 completion
    readRuntime readComplete readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag
    offset len nonzero boundsAfter
  have readTreeEq : accessed.tree = {tree with locations := accessed.tree.locations} := by
    generalize accessed.tree = after at nodes roots tags ⊢
    cases tree
    cases after
    simp_all
  have readNormal : OwnedOn (fun location => Nonempty
      (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read))
      offset (offset+len) accessed.tree.locations := by
    have transport : ∀ location, Nonempty (DuplicatePrefixNormalKind.Capability tree location registration.1.protectedTags reader .Read) →
        Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read) := by
      intro location old
      rw [readTreeEq]
      obtain ⟨old⟩ := old
      exact ⟨{component := old.component, permissions := old.permissions}⟩
    intro cursor valid positive start stop
    exact transport _ (readOwned cursor valid positive start stop).2.1
  obtain ⟨_,_,_,_,capChild,capLookup,capabilities⟩ := GeneralBorrowSharedReadConstructor.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag
    offset len nonzero boundsAfter readNormal
  have sameChild : capChild = child := Option.some.inj (capLookup.symm.trans lookup)
  subst capChild
  obtain ⟨_,activeChild,activeLookup,activity⟩ := S05SharedChildActivity.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag
    offset len nonzero boundsAfter
  have sameActive : activeChild = child := Option.some.inj (activeLookup.symm.trans lookup)
  subst activeChild
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩
  refine ⟨output,?_,rfl,rfl,readDone,childDone,afterRuntime,child,lookup,afterComplete,leaf,capabilities,activity⟩
  simp only [GeneralBorrowRawSharedFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
  rfl
private theorem entry_from_authority
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : entry.allocation.extra.roots[position]? = some root) (rootAt : entry.allocation.extra.nodes.get root = some rootNode)
    (sourcePath : Path entry.allocation.extra root source) (readerAt : entry.allocation.extra.nodes.get reader = some readerNode)
    (readerPath : Path entry.allocation.extra root reader) (readerTag : readerNode.tag = exprTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295) (short : entry.allocation.extra.nodes.size < 65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability entry.allocation.extra location tracker.global.protectedTags reader .Read))
      offset (offset+len) entry.allocation.extra.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags source)
      offset (offset+len) entry.allocation.extra.locations)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get
      (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
        (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current))) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := finalTree entry.allocation.extra tracker exprTag offset len
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  have treeBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [allocationSize];exact bounds
  have nonzeroLen : len ≠ 0 := by intro zero;subst len;exact (by decide : ¬((0 : UInt64)<0)) positive
  obtain ⟨output,actual,_,_,readDone,childDone,_⟩ := len_operation entry.allocation.extra tracker.global {} id completion runtime complete order
    position root source reader rootNode readerNode rootSlot rootAt sourcePath readerAt readerPath fresh offset len nonzeroLen treeBounds nodeRoom short readable owned
  simp only [readerTag] at actual
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh
  let accessed := entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let expected : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩
  have literal : GeneralBorrowRawSharedFnEntry.operation entry.allocation.extra tracker.global {} id exprTag offset len .VisitChildrenOfAccessed = .ok expected := by
    simp only [GeneralBorrowRawSharedFnEntry.operation,TypedRetagEmpty.allocate_tag tracker.global fresh,Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = expected := Except.ok.inj (actual.symm.trans literal)
  rw [equal] at readDone childDone
  have readCompleted : (CurrentCallLenArgumentCopy.readOperation entry.allocation.extra tracker exprTag offset len).status = .Completed := by
    simpa only [expected,accessed,CurrentCallLenArgumentCopy.readOperation,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
      TypedBorrowSteps.registeredGlobal] using readDone
  have childCompleted : (CurrentCallLenArgumentCopy.childOperation entry.allocation.extra tracker exprTag offset len).outcome = .ok () := by
    simpa only [expected,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
      TypedBorrowSteps.registeredGlobal,NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState] using childDone
  exact CurrentCallLenArgumentCopy.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled fresh readCompleted childCompleted
    bounds allocationSize localId valid old live cached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata cacheOrigins

/-- Derived actual post-Ref execution data, retained for the subsequent MIR consumer.
This is an output record, not a current-call admission predicate. -/
structure SharedStage {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data) (count : UInt64) where
  out : CurrentCallEntry.Output input #[]
  facts : CurrentCallEntry.Facts out count
  parent : CompilerFrameContext.ActualFrame
  shape : GenericFunctionEntryPrefix.Shape (out.frame count) parent count
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  room : out.borrowed.output.global.nextPointerTag.value < 18446744073709551615
  valid : (RootReferenceFacts.destination true) < parent.locals.size
  extra : entry.allocation.extra = CurrentCallSharedReference.sourceTree out.borrowed
  live : (out.machine count).memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry)
  cached : (out.machine count).user.addresses.baseAddr.find? (fun row => row.allocId == call.sourceId) = some ⟨call.sourceId,base⟩

namespace SharedStage
variable {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data} {count : UInt64}

def held (s : SharedStage input count) : MachineHooks.BorrowState :=
  ReferenceBorrowDriver.allocatedTracker ⟨s.out.borrowed.output.global,.Default⟩ s.room

def tree (s : SharedStage input count) : BorrowTree :=
  (GeneralBorrowRawSharedExpression.child s.entry.allocation.extra s.out.borrowed.output.global.protectedTags
    s.out.source.base.raw.output.tag s.out.borrowed.output.global.nextPointerTag
    (UInt64.ofNat call.sourceOffset) len .VisitChildrenOfAccessed).tree

def value (s : SharedStage input count) : RvalueImmTy Provenance :=
  RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete call.sourceId s.out.borrowed.output.global.nextPointerTag)
      (Size.ofBytes (s.base+UInt64.ofNat call.sourceOffset))) len (RootReferenceInfo.layout true)

def frame (s : SharedStage input count) : CompilerFrameContext.ActualFrame :=
  CopyHelperSteps.advance (ActualLocalCopy.written s.parent (RootReferenceFacts.destination true)
    (RootReferenceInfo.layout true) s.valid s.value.imm) (RootReferenceFacts.location true)

def machine (s : SharedStage input count) : CandidateCurrentJointCall.Before :=
  {ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span (s.out.machine count))
    ⟨s.out.borrowed.output.global,.Default⟩ s.room with
    memory := RetagEntry.updatedMemory (RootZeroCompleteState.tick options remaining span (s.out.machine count)).memory
      call.sourceId s.entry s.tree}
end SharedStage

private theorem shared_stage {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) :
    ∃ s : SharedStage input count,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count))
        (Storage.withCurrent #[] s.frame s.machine) := by
  obtain ⟨out,facts,parent,_,shape,entry,base,room,valid,extra,_,trace,live,cached⟩ :=
    CurrentCallSharedReference.invoke input stackReady memoryReady positive count nonzero
  exact ⟨⟨out,facts,parent,shape,entry,base,room,valid,extra,live,cached⟩,trace⟩

def SharedStage.completion {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (reader : UniIndex) : Completion :=
  extend (CurrentCallSharedReference.sourceCompletion s.out.borrowed) reader s.out.source.base.raw.child

theorem SharedStage.logical {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat) :
    ∃ (reader : UniIndex) (node : TreeNode),
      DuplicatePrefixBorrowContract.RuntimeFacts s.tree s.held.global ∧ Completes s.tree (s.completion reader) ∧ ParentTagOrder s.tree ∧
      s.tree.nodes.get reader = some node ∧ node.tag = s.out.borrowed.output.global.nextPointerTag ∧
      node.parent = some s.out.source.base.raw.child ∧ node.isExposed = false ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability s.tree location s.held.global.protectedTags reader .Read))
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) s.tree.locations ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority s.tree (s.completion reader) s.held.global.protectedTags s.out.source.base.raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) s.tree.locations ∧
      s.tree.locations.size = s.entry.allocation.byteSize ∧
      (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ s.tree.locations.size.bytes.toNat ∧
      s.tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+1 ∧ old_core s.entry.allocation.extra s.tree ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin s.tree s.out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
  let prepared := CurrentCallPush.prepared_input input #[]
  let raw := s.out.source.base.raw
  obtain ⟨runtime,complete,order,owned⟩ := CurrentCallSharedReference.source_ready prepared {} raw s.out.borrowed s.facts.written
  obtain ⟨parentNode,parentAt,parentTag⟩ := CurrentCallSharedReference.source_node raw s.out.borrowed s.facts.written
  rw [←s.extra] at runtime complete order owned parentAt
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path s.entry.allocation.extra runtime.formed.toGraphState raw.child parentNode parentAt
  obtain ⟨entry,base,live,_,storage,room,physicalBounds,_,_,_⟩ := s.facts.sourceWindow
  have sameEntry : entry = s.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans s.live))).2
  subst entry
  have offsetEq : (UInt64.ofNat call.sourceOffset).toNat = call.sourceOffset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  obtain ⟨actual,actualLive,_,_,actualLength,_,_,_,_,_⟩ := s.facts.source_allocation positive
  have actualEq : actual = s.entry := (Prod.mk.inj (Option.some.inj (actualLive.symm.trans s.live))).2
  rw [actualEq] at actualLength
  obtain ⟨_,_,_,_,_,rawSize⟩ := CandidateCurrentLiveRuntime.live options limits remaining (CurrentCallPush.preparedMachine before #[]) tracker len
    prepared.machine.state prepared.machine.resources call.sourceId raw.sourceAllocation raw.sourcePresent
  have capacityBefore : s.entry.allocation.extra.locations.size = s.entry.allocation.byteSize := by
    have size : s.entry.allocation.extra.locations.size.bytes.toNat = s.entry.allocation.byteSize.bytes.toNat := by
      rw [s.extra,CurrentCallSharedReference.source_capacity raw s.out.borrowed s.facts.written,rawSize,←actualLength,storage]
    exact congrArg Size.ofBytes (UInt64.toNat_inj.mp size)
  have bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacityBefore,←storage,offsetEq];exact physicalBounds
  have budgets := CurrentCallSharedReference.source_budget prepared {} raw s.out.borrowed s.facts.written
  rw [←s.extra] at budgets
  obtain ⟨_,_,afterRuntime,capacity,growth,reader,lookup,leaf,afterComplete,both,parentOwned,afterOrder,node,nodeAt,nodeTag,nodeParent,hidden,oldNodes,preserveActivity⟩ :=
    default_shared s.entry.allocation.extra s.out.borrowed.output.global (CurrentCallSharedReference.sourceCompletion s.out.borrowed)
      runtime complete order position root raw.child rootNode parentNode slot rootAt parentAt path s.room budgets.2.1 budgets.2.2
      (UInt64.ofNat call.sourceOffset) len (by intro zero;simp [zero] at positive) bounds owned
  simp only [parentTag] at afterRuntime capacity growth lookup leaf afterComplete both parentOwned afterOrder nodeAt nodeTag nodeParent hidden oldNodes preserveActivity
  obtain ⟨_,_,_,_,_,initialActive⟩ := CurrentCallEntryProtectionData.Facts.source_data s.facts positive
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin s.entry.allocation.extra raw.child .Write
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
    rw [s.extra]
    unfold CurrentCallSharedReference.sourceTree
    rw [←s.facts.extra]
    exact initialActive
  have capacityCurrent : s.tree.locations.size = s.entry.allocation.extra.locations.size := capacity
  refine ⟨reader,node,afterRuntime,afterComplete,afterOrder,nodeAt,nodeTag,nodeParent,hidden,?_,parentOwned,
    capacityCurrent.trans capacityBefore,?_,growth,oldNodes,preserveActivity raw.child sourceActive⟩
  · intro cursor valid positive start stop
    exact (both cursor valid positive start stop).2
  · rw [capacityCurrent];exact bounds

private theorem before_return_from_authority
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : Completes entry.allocation.extra completion) (order : ParentTagOrder entry.allocation.extra)
    (position : Nat) (root owner reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : entry.allocation.extra.roots[position]? = some root) (rootAt : entry.allocation.extra.nodes.get root = some rootNode)
    (sourcePath : Path entry.allocation.extra root owner) (readerAt : entry.allocation.extra.nodes.get reader = some readerNode)
    (readerPath : Path entry.allocation.extra root reader) (readerTag : readerNode.tag = exprTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295) (short : entry.allocation.extra.nodes.size < 65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability entry.allocation.extra location tracker.global.protectedTags reader .Read))
      offset (offset+len) entry.allocation.extra.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags owner)
      offset (offset+len) entry.allocation.extra.locations)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)))
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := finalTree entry.allocation.extra tracker exprTag offset len
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ) ∧ ReturnFacts options remaining span result finalMachine len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ RootCache frames finalMachine := by
  have treeBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [allocationSize];exact bounds
  have nonzeroLen : len ≠ 0 := by intro zero;subst len;exact (by decide : ¬((0 : UInt64)<0)) positive
  obtain ⟨output,actual,_,_,readDone,childDone,_⟩ := len_operation entry.allocation.extra tracker.global {} id completion runtime complete order
    position root owner reader rootNode readerNode rootSlot rootAt sourcePath readerAt readerPath fresh offset len nonzeroLen treeBounds nodeRoom short readable owned
  simp only [readerTag] at actual
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh
  let accessed := entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let expected : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩
  have literal : GeneralBorrowRawSharedFnEntry.operation entry.allocation.extra tracker.global {} id exprTag offset len .VisitChildrenOfAccessed = .ok expected := by
    simp only [GeneralBorrowRawSharedFnEntry.operation,TypedRetagEmpty.allocate_tag tracker.global fresh,Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = expected := Except.ok.inj (actual.symm.trans literal)
  rw [equal] at readDone childDone
  have readCompleted : (CurrentCallLenArgumentCopy.readOperation entry.allocation.extra tracker exprTag offset len).status = .Completed := by
    simpa only [expected,accessed,CurrentCallLenArgumentCopy.readOperation,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
      TypedBorrowSteps.registeredGlobal] using readDone
  have childCompleted : (CurrentCallLenArgumentCopy.childOperation entry.allocation.extra tracker exprTag offset len).outcome = .ok () := by
    simpa only [expected,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
      TypedBorrowSteps.registeredGlobal,NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState] using childDone
  exact CurrentCallLenArgumentCopy.before_return options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits
    frames caller machine tracker enabled defaultMode fresh readCompleted childCompleted bounds allocationSize
    valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame
    metadata cacheOrigins sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed

theorem SharedStage.budget {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat) :
    s.held.global.nextPointerTag.value < 18446744073709551615 ∧
    s.tree.nodes.size+1 ≤ 4294967295 ∧ s.tree.nodes.size < 65536 ∧ s.tree.nodes.size+1 < 65536 := by
  let prepared := CurrentCallPush.prepared_input input #[]
  let raw := s.out.source.base.raw
  obtain ⟨room,_,_⟩ := CurrentCallBoolProtection.return_budget prepared {} raw
  have boolEq : s.out.borrowed.output = CurrentCallTypedFnEntry.literal
      (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room
      raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1 :=
    Except.ok.inj (s.out.borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  have first : raw.output.global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom := by
    rw [raw.outputGlobal];rfl
  have second : s.out.borrowed.output.global.nextPointerTag = TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room := by rw [boolEq];rfl
  have step1 := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
  have step2 := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
  have step3 := GenericFunctionEntryNumerics.successor_value s.out.borrowed.output.global.nextPointerTag s.room
  have firstNat := congrArg (fun tag : BorTag => tag.value.toNat) first
  have secondNat := congrArg (fun tag : BorTag => tag.value.toNat) second
  have reserve := prepared.machine.resources.tagRoom
  have tagRoom : s.held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag s.out.borrowed.output.global.nextPointerTag s.room).value.toNat < 18446744073709551615
    omega
  have margin : raw.sourceAllocation.extra.nodes.size+16 < 65536 := by
    have present := raw.sourcePresent
    simp only [CandidateStableCallOwnership.Present,CandidateCurrentJointCall.ActualWorld,Array.toList_map] at present
    obtain ⟨⟨id,entry⟩,member,equal⟩ := List.mem_map.mp present
    have allocEq := (Prod.mk.inj equal).2
    change entry.allocation = raw.sourceAllocation at allocEq
    rw [←allocEq]
    exact prepared.machine.resources.nodeRoom (id,entry) member
  have beforeGrowth : s.entry.allocation.extra.nodes.size ≤ raw.sourceAllocation.extra.nodes.size+2 := by
    rw [s.extra]
    have sourceGrowth := raw.outputGrowth
    have boolGrowth := s.out.borrowed.metadata.growth
    dsimp only [raw] at sourceGrowth ⊢
    by_cases same : call.sourceId = call.returnId
    · simp only [CurrentCallBoolProtection.returnTree,same,ite_true] at boolGrowth
      simp only [CurrentCallSharedReference.sourceTree,same,ite_true,s.facts.written.nodes]
      omega
    · simp only [CurrentCallSharedReference.sourceTree,same,ite_false]
      omega
  have afterGrowth : s.tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+1 := by
    obtain ⟨reader,node,runtime,complete,order,nodeAt,tag,parent,hidden,readable,owned,capacity,bounds,result,_,_⟩ := SharedStage.logical s positive
    exact result
  exact ⟨tagRoom,by omega,by omega,by omega⟩

private theorem shared_storage {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    s.machine.memory.live.find? (fun row => row.1 == call.sourceId) =
      some (call.sourceId,{s.entry with allocation := s.entry.allocation.setExtra s.tree}) ∧
    s.machine.user.addresses.baseAddr.find? (fun row => row.allocId == call.sourceId) = some ⟨call.sourceId,s.base⟩ ∧
    s.machine.borrowTracker = some s.held ∧
    s.machine.user.payload.ghost = false ∧ s.machine.user.payload.validation = .Shallow ∧
    s.machine.dataRace = none ∧ s.machine.user.payload.payload.user.backend = .none := by
  have settings := s.out.settings count
  refine ⟨MemoryCopyBridge.live_lookup_replaced _ _ _,?_,rfl,?_,?_,settings.noDataRace,?_⟩
  · change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.addresses.baseAddr.find? _ = _
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact s.cached
  · change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.ghost = false
    rw [RootZeroCompleteState.tick_ghost];exact settings.ghostOff
  · change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.validation = .Shallow
    rw [RootZeroCompleteState.tick_shallow];exact settings.shallow
  · change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.payload.user.backend = .none
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact settings.noBackend

private theorem shared_actor {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (ready : CurrentCallPush.StackReadiness before #[]) :
    ∃ thread, s.machine.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0 := by
  obtain ⟨thread,active,_⟩ := ready
  refine ⟨{thread with topUserRelevantFrame := some 0},?_,rfl⟩
  have prepared : (CurrentCallPush.preparedMachine before #[]).threads.activeThread? =
      some {thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).threads.activeThread? = _
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact prepared

private theorem shared_geometry {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat) :
    s.base+UInt64.ofNat call.sourceOffset ≠ 0 ∧
    len.toNat < 9223372036854775808 ∧
    (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ s.entry.allocation.byteSize.bytes.toNat := by
  obtain ⟨entry,base,live,cached,storage,room,bounds,addressEq,nonnull,_⟩ := s.facts.sourceWindow
  have sameEntry : entry = s.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans s.live))).2
  have sameBase : base = s.base := (Miri.Memory.AllocAddresses.BaseAddressEntry.mk.inj (Option.some.inj (cached.symm.trans s.cached))).2
  subst entry
  subst base
  have offsetEq : (UInt64.ofNat call.sourceOffset).toNat = call.sourceOffset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  have sumEq : (s.base+UInt64.ofNat call.sourceOffset).toNat = s.base.toNat+call.sourceOffset := by
    simp only [UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : s.base.toNat+call.sourceOffset<2^64)]
  have bits : s.out.source.base.raw.sourcePointer.value.offset.bytes = s.base+UInt64.ofNat call.sourceOffset :=
    UInt64.toNat_inj.mp (addressEq.trans sumEq.symm)
  refine ⟨?_,?_,?_⟩
  · rw [←bits];exact nonnull
  · rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  · rw [offsetEq,←storage];exact bounds

private theorem shared_model {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    DuplicatePrefixCallModel.Model options remaining span s.machine := by
  have original := s.out.settings count
  have storage := shared_storage s
  have data : s.machine.user.payload.payload.user.types = (s.out.machine count).user.payload.payload.user.types := by
    change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.payload.user.types = _
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have flags := RootZeroCompleteState.tick_flags options remaining span (s.out.machine count)
  refine {original with
    ghostOff := storage.2.2.2.1
    shallow := storage.2.2.2.2.1
    defaultTracker := ⟨s.held,storage.2.2.1,rfl⟩
    noDataRace := storage.2.2.2.2.2.1
    noBackend := storage.2.2.2.2.2.2
    metadata := by rw [data];exact original.metadata
    fixedScheduler := original.fixedScheduler
    unchecked := flags.1.trans original.unchecked
    noGc := flags.2.trans original.noGc }


private def len_literal (tree : BorrowTree) (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (offset len : UInt64) : GeneralBorrowForestFnEntry.Output :=
  let registration := GeneralBorrowFnEntryRegistration.registered global {} id room
  ⟨registration.1,registration.2,global.nextPointerTag,
    CurrentCallLenArgumentCopy.readOperation tree ⟨global,.Default⟩ parentTag offset len,
    CurrentCallLenArgumentCopy.childOperation tree ⟨global,.Default⟩ parentTag offset len⟩

private theorem len_literal_operation (tree : BorrowTree) (global : GlobalState) (id : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (offset len : UInt64) :
    GeneralBorrowRawSharedFnEntry.operation tree global {} id parentTag offset len .VisitChildrenOfAccessed =
      .ok (len_literal tree global id room parentTag offset len) := by
  simp only [GeneralBorrowRawSharedFnEntry.operation,TypedRetagEmpty.allocate_tag global room,Except.bind,Except.pure,bind,pure]
  rfl

private theorem joined_before_return {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) :
    ∃ (s : SharedStage input count) (result : CompilerFrameContext.ActualFrame)
      (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count))
        (Storage.withCurrent #[cachedCaller s.frame (by
          have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
          change 11 < (CurrentCallLenSharedFrame.frame s.parent s.valid s.value).locals.size
          rw [shape.2.2.2.1];decide)] result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∃ argument, ReturnFacts options remaining span result finalMachine len argument) ∧ RootCache #[] finalMachine ∧
      ∃ (output : GeneralBorrowForestFnEntry.Output),
        GeneralBorrowRawSharedFnEntry.operation s.tree s.held.global {} call.sourceId
          s.out.borrowed.output.global.nextPointerTag (UInt64.ofNat call.sourceOffset) len .VisitChildrenOfAccessed = .ok output ∧
        finalMachine.memory = RetagEntry.updatedMemory s.machine.memory call.sourceId
          {s.entry with allocation := s.entry.allocation.setExtra s.tree} output.child.tree ∧
        finalMachine.borrowTracker = some ⟨output.global,.Default⟩ ∧
        result.extra.borrowTracker = some (({} : FrameState).addProtector call.sourceId output.tag) ∧
        result.extra.dataRace = none ∧ finalMachine.dataRace = none ∧
        finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
        result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 (cachedCaller s.frame (by
          have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
          change 11 < (CurrentCallLenSharedFrame.frame s.parent s.valid s.value).locals.size
          rw [shape.2.2.2.1];decide)) 11 RootCompilerFacts.usizeLayout ∧
        result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
        finalMachine.user.addresses = s.machine.user.addresses ∧
        finalMachine.user.payload.payload.user.types = s.machine.user.payload.payload.user.types ∧
        finalMachine.user.payload.payload.user.runtime.extras = s.machine.user.payload.payload.user.runtime.extras := by
  obtain ⟨s,initialTrace⟩ := shared_stage input stackReady memoryReady positive count nonzero
  have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
  change s.frame.body = _ ∧ s.frame.bodyIdentity = _ ∧ s.frame.functionInstance = _ ∧ s.frame.locals.size = _ ∧ _ at shape
  obtain ⟨reader,readerNode,runtime,complete,order,readerAt,readerTag,readerParent,readerHidden,readable,owned,capacity,bounds,growth,oldNodes,sourceActivity⟩ := SharedStage.logical s positive
  have budgets := SharedStage.budget s positive
  have storage := shared_storage s
  have geometry := shared_geometry s positive
  have model := shared_model s
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨thread,active,topZero⟩ := shared_actor s stackReady
  let current := PtrMetadataReturn.accountedMachine options remaining span s.machine
  let entry := {s.entry with allocation := s.entry.allocation.setExtra s.tree}
  have currentData : current.user.payload.payload.user.types = s.machine.user.payload.payload.user.types ∧
      current.user.addresses = s.machine.user.addresses := by
    unfold current PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl⟩
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨sourceNode,sourceAt,_⟩ := depth.parent reader readerNode readerAt s.out.source.base.raw.child readerParent
  obtain ⟨position,root,rootNode,slot,rootAt,sourcePath⟩ := CandidateCurrentWindowAuthority.root_path s.tree runtime.formed.toGraphState
    s.out.source.base.raw.child sourceNode sourceAt
  have readerPath : Path s.tree root reader := .step sourcePath readerNode readerAt readerParent
  have valid : 11 < s.frame.locals.size := by rw [shape.2.2.2.1];decide
  have valid12 : 12 < s.frame.locals.size := by rw [shape.2.2.2.1];decide
  have slot11 := Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans shape.2.2.2.2.2.2.1)
  have slot12 := Option.some.inj ((Array.getElem?_eq_getElem valid12).symm.trans shape.2.2.2.2.2.2.2.1)
  let rootFrame := cachedCaller s.frame valid
  let destination := (LocalPlaces.localRuntimePlace 0 rootFrame 11 RootCompilerFacts.usizeLayout).stackView
  let pushed := LenPush.pushed options.userRelevantCrates (Storage.withCurrent #[] rootFrame current) destination
  have top : FrameRelevance.top pushed.stack thread.topUserRelevantFrame = some 0 := by rw [topZero];rfl
  have presentFrame : pushed.stack.frames[0]? = some rootFrame := by
    simp only [pushed,LenPush.pushed,Storage.withCurrent,Array.push_empty,Array.getElem?_push]
    rfl
  have worldEq : EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootFrame current) destination rootFrame) = current.user.payload.payload.user.types := by
    unfold LenPush.completed GenericPushRelevance.afterPush
    dsimp only [EvalProjectionMachine.arrays,Storage.withCurrent]
    split <;> rfl
  have currentShallow : current.user.payload.validation = .Shallow := by
    unfold current PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.shallow
  have currentBackend : current.user.payload.payload.user.backend = .none := by
    unfold current PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.noBackend
  have metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootFrame current) destination rootFrame)).metadata = PreparedReflection.actual.runtime := by
    rw [worldEq]
    rw [currentData.1];exact model.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] rootFrame current) destination rootFrame)) := by
    rw [worldEq]
    rw [currentData.1]
    change DuplicatePrefixTypeCacheOrigins.Origins (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.payload.user.types
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact s.out.cacheOrigins count
  let dynamicFuel := options.place.dynamicFuel-1
  let validityFuel := options.limits.validation-1
  let budget := limits.callDispatch-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have fuelEq : options.place.dynamicFuel = dynamicFuel+1 := by
    have margin := input.machine.resources.dynamicFuel
    dsimp only [dynamicFuel];omega
  have validationEq : options.limits.validation = validityFuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [validityFuel];omega
  have dispatchEq : limits.callDispatch = budget+1 := by
    have margin := input.machine.resources.executionFuel.1
    dsimp only [budget];omega
  have called := before_return_from_authority options limits remaining budget dispatchEq span ctx model.debugOff model.nullComparator
    dynamicFuel validityFuel fuelEq validationEq call.sourceId entry s.base (UInt64.ofNat call.sourceOffset) len
    s.out.borrowed.output.global.nextPointerTag (by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive)
    geometry.1 geometry.2.1 #[] s.frame current s.held storage.2.2.1 rfl budgets.1
    (s.completion reader) runtime complete order position root s.out.source.base.raw.child reader rootNode readerNode slot rootAt sourcePath readerAt readerPath readerTag
    budgets.2.1 budgets.2.2.1 readable owned geometry.2.2 capacity valid (congrArg LocalState.value slot11)
    (congrArg LocalState.layout slot11) shape.2.2.2.2.2.1
    ((PtrMetadataReturn.accounted_ghost options remaining span s.machine).trans model.ghostOff)
    currentShallow
    (currentData.2 ▸ storage.2.1) storage.1 model.noDataRace thread 0 rootFrame active top presentFrame metadata origins
    shape.1 shape.2.1 shape.2.2.1 shape.2.2.2.2.1
    (DuplicatePrefixCallModel.sourceComparator options remaining span s.machine model) valid12
    (congrArg LocalState.value slot12) (congrArg LocalState.layout slot12) currentBackend s.machine rfl model.unchecked model.noGc model.fixedScheduler
  obtain ⟨result,finalMachine,details,returnFacts,cache⟩ := called
  rcases details with ⟨trace,located,returned,held,clocks,destinationEq,continuation,vaList,memory,tracked,ghost,shallow,race,addresses,types,extras⟩
  let literal := len_literal s.tree s.held.global call.sourceId budgets.1 s.out.borrowed.output.global.nextPointerTag (UInt64.ofNat call.sourceOffset) len
  exact ⟨s,result,finalMachine,SuccessfulTrace.append initialTrace trace,located,returned,⟨_,returnFacts⟩,cache,
    literal,len_literal_operation _ _ _ budgets.1 _ _ _,memory,tracked,held,clocks,race,ghost,shallow,destinationEq,continuation,vaList,addresses,types,extras⟩

private theorem shared_held_tree (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (first second : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen first).tree =
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen second).tree := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildShared.result input = GeneralBorrowFreshMetadataChildShared.result {input with isProtected := second}
    rw [GeneralBorrowFreshMetadataChildShared.tree_eq,GeneralBorrowFreshMetadataChildShared.tree_eq]
    rfl
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildSharedReuse.result input = GeneralBorrowFreshMetadataChildSharedReuse.result {input with isProtected := second}
    rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq,GeneralBorrowFreshMetadataChildSharedReuse.tree_eq]
    rfl

/-- A virtual protector view for a tag absent from this tree. This is only a
representation lemma; the actual release access still uses its original table. -/
private theorem absent_tag_view (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag)
    (absent : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall (({} : FrameState).addProtector allocation tag)) := by
  have protectorEq : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags = global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
  · intro position valid
    rw [protectorEq]
    exact GeneralBorrowHiddenProtectorDropRuntime.profile tree _ _ _ (GeneralBorrowRelease.remove_weakens global.protectedTags tag)
      (runtime.formed.profile position valid)
  · intro position valid
    rw [protectorEq]
    apply GeneralBorrowProtectorCacheMap.remove_hidden tree _ global.protectedTags tag (runtime.coherent position valid)
    intro index node present tagged
    exact False.elim (absent index node present tagged)
  · refine ⟨runtime.below.mapping,?_⟩
    intro row member
    rw [protectorEq] at member
    exact runtime.below.protectors row (Array.mem_filter.mp member).1

/-- Actual protected Frozen construction retains old-source authority in the
computed post-removal view. No such authority is asserted under the live child
protector. Constructor trees coincide by their exact source equations. -/
private theorem protected_old_future (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (allocation : AllocId) (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nodeFresh : GeneralBorrowProtector.Fresh tree newTag)
    (room : tree.nodes.size+1 ≤ 4294967295) (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion
      (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
      offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (extend completion child parent)
        (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
        offset (offset+len) actual.tree.locations := by
  let future := global.endCall (({} : FrameState).addProtector allocation newTag)
  have futureRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree future := by
    apply absent_tag_view tree global runtime allocation newTag
    intro index node found
    exact nodeFresh (index,node) (Array.mem_toList_iff.mp
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr found))
  have unheld : future.protectedTags.contains newTag = false := by
    change (global.protectedTags.remove newTag).contains newTag = false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  obtain ⟨_,_,_,_,child,lookup,authority⟩ := S05UnprotectedSharedOldAuthority.construct tree future completion
    futureRuntime complete parentTag newTag parent parentNode tagged present fresh room tagBound unheld source sourceLive
    offset len nonzero bounds owned
  have same := shared_held_tree tree global runtime parentTag newTag parent parentNode tagged present fresh room true false offset len nonzero bounds
  refine ⟨child,?_,?_⟩
  · rw [same];exact lookup
  · rw [same];exact authority

private theorem end_call_unheld_flags (global : GlobalState) (id : AllocId) (tag : BorTag)
    (unheld : global.protectedTags.contains tag = false) (query : BorTag) :
    (global.endCall (({} : FrameState).addProtector id tag)).protectedTags.contains query = global.protectedTags.contains query := by
  change (global.protectedTags.remove tag).contains query = _
  by_cases same : query = tag
  · subst query
    simpa only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none] using unheld.symm
  · unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other global.protectedTags tag query same]

theorem SharedStage.reader_unheld {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    s.held.global.protectedTags.contains s.out.borrowed.output.global.nextPointerTag = false := by
  let prepared := CurrentCallPush.prepared_input input #[]
  obtain ⟨runtime,_,_,_⟩ := CurrentCallSharedReference.source_ready prepared {} s.out.source.base.raw s.out.borrowed s.facts.written
  have high := GeneralBorrowForestTagHighWater.complete _ _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unheld⟩ := GenericFunctionTagFormation.fresh_above _ _ _ s.out.borrowed.output.global.nextPointerTag high (Nat.le_refl _)
  exact unheld

private theorem release_helper (tree : BorrowTree) (global : GlobalState) (completion : Completion)
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
    (short : tree.nodes.size < 65536)
    (temporaryUnheld : global.protectedTags.contains temporaryNode.tag = false) :
    let result := tree.releaseProtector readerNode.tag global.protectedTags
    let after := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts result.tree after ∧ Completes result.tree completion ∧
    result.tree.locations.size = tree.locations.size ∧
    OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree completion after.protectedTags source)
      offset (offset+len) result.tree.locations := by
  obtain ⟨done,frame,releasedRuntime,releasedComplete,capacity,authority⟩ := S05CurrentReadProtectorRelease.release_observer
    tree global completion runtime complete order selectedPosition selected source reader selectedNode readerNode
    selectedSlot selectedPresent sourcePath readerPresent readerPath allocation temporary temporaryNode readerEdge
    temporaryPresent temporaryEdge hidden temporaryHidden offset len positive active owned short
  let result := tree.releaseProtector readerNode.tag global.protectedTags
  let after := global.endCall (({} : FrameState).addProtector allocation readerNode.tag)
  have presentAfter : result.tree.nodeAt reader = some readerNode := by
    change result.tree.nodes.get reader = _
    rw [congrArg BorrowTree.nodes frame]
    exact readerPresent
  obtain ⟨afterRuntime,_,_⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call result.tree global releasedRuntime
    allocation readerNode.tag reader readerNode presentAfter rfl hidden
  have stillUnheld : after.protectedTags.contains temporaryNode.tag = false := by
    cases found : after.protectedTags.contains temporaryNode.tag with
    | false => rfl
    | true =>
      have before := GeneralBorrowRelease.end_call_weakens global (({} : FrameState).addProtector allocation readerNode.tag) temporaryNode.tag found
      rw [temporaryUnheld] at before
      cases before
  have transform : ∀ location,
      S05CompletedAncestryReadMutable.Authority tree completion
        (after.endCall (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location →
      S05CompletedAncestryReadMutable.Authority result.tree completion after.protectedTags source location := by
    intro location old index node present
    have presentBefore : tree.nodes.get index = some node := by
      rw [congrArg BorrowTree.nodes frame] at present
      exact present
    have original := old index node presentBefore
    rw [end_call_unheld_flags after allocation temporaryNode.tag stillUnheld node.tag] at original
    exact original
  refine ⟨done,frame,afterRuntime,releasedComplete,capacity,?_⟩
  intro cursor valid positive start stop
  exact transform _ (authority cursor valid positive start stop)

private theorem len_release (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source) (readerAt : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree root reader) (readerEdge : readerNode.parent = some source)
    (hidden : readerNode.isExposed = false) (readerUnheld : global.protectedTags.contains readerNode.tag = false)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size+1 < 65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations) :
    let output := len_literal tree global allocation room readerNode.tag offset len
    let result := output.child.tree.releaseProtector output.tag output.global.protectedTags
    ∃ helper,
      result.status = .Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree (output.global.endCall output.frame) ∧
      Completes result.tree (extend completion helper reader) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree (extend completion helper reader)
        (output.global.endCall output.frame).protectedTags source) offset (offset+len) result.tree.locations ∧
      result.tree.locations.size = tree.locations.size ∧ result.tree.nodes.size ≤ tree.nodes.size+1 ∧ old_core tree result.tree ∧ ParentTagOrder result.tree ∧
      (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write offset (offset+len)) ∧
      output.child.tree.indexOfTag output.tag = some helper ∧ tree.nodes.get helper = none := by
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,readRuntime,readComplete,nodes,roots,tags,capacity,readOwned⟩ := S05CurrentLenAssociatedRead.prepare
    tree global allocation completion runtime complete order position root source reader rootNode readerNode rootSlot rootAt sourcePath
    readerAt readerPath readerEdge hidden readerUnheld room offset len bounds (by omega) readable owned
  obtain ⟨_,held,_,_,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  have present : accessed.tree.nodeAt reader = some readerNode := by change accessed.tree.nodes.get reader = _;rw [nodes];exact readerAt
  have tagged : accessed.tree.indexOfTag readerNode.tag = some reader := (readComplete.2.2.2.2.1 reader readerNode present).1
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have nodeFreshAfter : GeneralBorrowProtector.Fresh accessed.tree global.nextPointerTag := by
    intro row member
    have found := (GeneralBorrowFreshReuseProtection.entries_get accessed.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    rw [nodes] at found
    exact nodeFresh row (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mpr found))
  have nodeRoomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have step := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,childRuntime,childCapacity,growth,helper,lookup,leaf,childComplete,_⟩ := shared_completion accessed.tree registration.1 completion
    readRuntime readComplete readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag
    offset len nonzero boundsAfter
  have normalRead : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read))
      offset (offset+len) accessed.tree.locations := fun cursor valid positive start stop => (readOwned cursor valid positive start stop).1
  obtain ⟨_,_,_,_,capHelper,capLookup,capabilities⟩ := GeneralBorrowSharedReadConstructor.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter normalRead
  have capEq : capHelper = helper := Option.some.inj (capLookup.symm.trans lookup)
  subst capHelper
  obtain ⟨depth⟩ := readRuntime.formed.depth
  obtain ⟨sourceNode,sourceAt,_⟩ := depth.parent reader readerNode present source readerEdge
  obtain ⟨futureHelper,futureLookup,futureOwned⟩ := protected_old_future accessed.tree registration.1 completion readRuntime readComplete allocation
    readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeFreshAfter nodeRoomAfter tagBound source ⟨sourceNode,sourceAt⟩
    offset len nonzero boundsAfter (fun cursor valid positive start stop => (readOwned cursor valid positive start stop).2)
  have futureEq : futureHelper = helper := Option.some.inj (futureLookup.symm.trans lookup)
  subst futureHelper
  have activeLookup := (S05SharedChildActivity.construct accessed.tree registration.1 readRuntime readerNode.tag global.nextPointerTag
    reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter).2
  obtain ⟨activeIndex,activeAt,activeWithin⟩ := activeLookup
  have activeEq : activeIndex = helper := Option.some.inj (activeAt.symm.trans lookup)
  subst activeIndex
  obtain ⟨graphHelper,graphLookup,⟨helperNode,helperAt,helperTag,helperEdge,helperHidden⟩,old⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter true offset len nonzero boundsAfter
  have graphEq : graphHelper = helper := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphHelper
  obtain ⟨temporaryNode,temporaryAt,temporaryTag,temporaryEdge,temporaryHidden⟩ := old reader readerNode present
  obtain ⟨currentSource,currentSourceAt,_,_,_⟩ := old source sourceNode sourceAt
  let afterTree := (accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree
  have orderRead : ParentTagOrder accessed.tree := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree nodes order
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime reader readerNode readerAt
  have afterOrder := GeneralBorrowSharedChildParentTagOrder.construct accessed.tree registration.1 readRuntime readerNode.tag global.nextPointerTag
    reader readerNode tagged present freshAfter nodeRoomAfter true offset len nonzero boundsAfter orderRead
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older)))
  obtain ⟨currentPosition,currentRoot,currentRootNode,currentSlot,currentRootAt,currentSourcePath⟩ := CandidateCurrentWindowAuthority.root_path afterTree
    childRuntime.formed.toGraphState source currentSource currentSourceAt
  have temporaryPath : Path afterTree currentRoot reader := .step currentSourcePath temporaryNode temporaryAt (temporaryEdge.trans readerEdge)
  have helperPath : Path afterTree currentRoot helper := .step temporaryPath helperNode helperAt helperEdge
  have different := nodeFresh (reader,readerNode) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes reader readerNode).mpr readerAt))
  have temporaryUnheld : registration.1.protectedTags.contains temporaryNode.tag = false := by
    rw [temporaryTag]
    exact (ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag readerNode.tag .StrongProtector different).trans readerUnheld
  let after := registration.1.endCall (({} : FrameState).addProtector allocation helperNode.tag)
  have laterUnheld : after.protectedTags.contains temporaryNode.tag = false := by
    cases found : after.protectedTags.contains temporaryNode.tag with
    | false => rfl
    | true =>
      have previous := GeneralBorrowRelease.end_call_weakens registration.1 (({} : FrameState).addProtector allocation helperNode.tag) temporaryNode.tag found
      rw [temporaryUnheld] at previous
      cases previous
  have afterOwned : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability afterTree location registration.1.protectedTags helper .Read) ∧
      S05CompletedAncestryReadMutable.Authority afterTree (extend completion helper reader)
        (after.endCall (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags source location)
      offset (offset+len) afterTree.locations := by
    intro cursor valid positive start stop
    refine ⟨(capabilities cursor valid positive start stop).2,?_⟩
    have original := futureOwned cursor valid positive start stop
    intro index node found
    have scalar := original index node found
    have sameFuture : after.protectedTags.contains node.tag =
        (registration.1.endCall (({} : FrameState).addProtector allocation global.nextPointerTag)).protectedTags.contains node.tag := by
      dsimp only [after]
      rw [helperTag]
    rw [end_call_unheld_flags after allocation temporaryNode.tag laterUnheld node.tag]
    simpa only [sameFuture] using scalar
  have finalShort : afterTree.nodes.size < 65536 := by
    have bound : afterTree.nodes.size ≤ tree.nodes.size+1 := by
      calc afterTree.nodes.size ≤ accessed.tree.nodes.size+1 := growth
           _ = tree.nodes.size+1 := congrArg (fun value : UniValMap TreeNode => value.size+1) nodes
    omega
  have positive : offset.toNat < (offset+len).toNat := by
    have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    have length : 0 < len.toNat := Nat.pos_of_ne_zero (by intro zero;exact nonzero (UInt64.toNat_inj.mp zero))
    omega
  obtain ⟨released,releaseFrame,releasedRuntime,releasedComplete,releasedCapacity,releasedOwned⟩ := release_helper afterTree registration.1 (extend completion helper reader)
    childRuntime childComplete afterOrder currentPosition currentRoot source helper currentRootNode helperNode currentSlot currentRootAt currentSourcePath
    helperAt helperPath allocation reader temporaryNode helperEdge temporaryAt (temporaryEdge.trans readerEdge) helperHidden
    (temporaryHidden.trans hidden) offset len positive activeWithin afterOwned finalShort temporaryUnheld
  have finalCapacity := releasedCapacity.trans (childCapacity.trans capacity)
  have finalGrowth : (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree.nodes.size ≤ tree.nodes.size+1 := by
    have nodesAfter := congrArg BorrowTree.nodes releaseFrame
    change (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree.nodes = afterTree.nodes at nodesAfter
    rw [nodesAfter]
    calc afterTree.nodes.size ≤ accessed.tree.nodes.size+1 := growth
         _ = tree.nodes.size+1 := congrArg (fun value : UniValMap TreeNode => value.size+1) nodes
  have oldFrame : old_core tree (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree := by
    intro query node nodeAt
    obtain ⟨next,nextAt,nextTag,nextParent,nextHidden⟩ := old query node (by
      change accessed.tree.nodes.get query = _;rw [nodes];exact nodeAt)
    refine ⟨next,?_,nextTag,nextParent,nextHidden⟩
    have nodesAfter := congrArg BorrowTree.nodes releaseFrame
    change (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree.nodes = afterTree.nodes at nodesAfter
    change (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree.nodes.get query = _
    rw [nodesAfter];exact nextAt
  have finalOrder : ParentTagOrder (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree := by
    have nodesAfter := congrArg BorrowTree.nodes releaseFrame
    change (afterTree.releaseProtector helperNode.tag registration.1.protectedTags).tree.nodes = afterTree.nodes at nodesAfter
    exact GeneralBorrowParentTagInvariant.nodes_frame afterTree _ nodesAfter afterOrder
  refine ⟨helper,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using released
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using releasedRuntime
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using releasedComplete
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using releasedOwned
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using finalCapacity
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using finalGrowth
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using oldFrame
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using finalOrder
  · intro target active
    have readActive := GeneralBorrowFreshActiveWithinAccess.normal tree readerNode.tag (Size.ofBytes offset) (Size.ofBytes len) .Read
      registration.1.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
    have childActive := GeneralBorrowRawTargetActivity.shared accessed.tree registration.1 readRuntime readerNode.tag global.nextPointerTag
      reader readerNode tagged present freshAfter nodeRoomAfter true offset len nonzero boundsAfter target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) readActive
    have helperWrite := GeneralBorrowFreshActiveWithin.to_write afterTree helper offset (offset+len) activeWithin
    have finalActive := GeneralBorrowActiveWithinRelease.release afterTree registration.1.protectedTags helperNode.tag helper target helperNode
      (by rw [helperTag];exact lookup) helperAt helperHidden offset (offset+len) helperWrite childActive
    simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,helperTag,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using finalActive
  · simpa only [len_literal,afterTree,accessed,CurrentCallLenArgumentCopy.childOperation,CurrentCallLenArgumentCopy.readOperation,
      NestedConstruction.frozenRead,GeneralBorrowFreshAnchor.sharedState,registration,
      GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,TypedBorrowSteps.registeredGlobal,GlobalState.addProtector,FrameState.addProtector] using lookup

  · rw [←nodes];exact leaf.vacant


/-- Exact root frame produced by the actual Len scalar return. -/
def SharedStage.lenFrame {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) : CompilerFrameContext.ActualFrame :=
  let valid : 11 < s.frame.locals.size := by
    have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
    change 11 < (CurrentCallLenSharedFrame.frame s.parent s.valid s.value).locals.size
    rw [shape.2.2.2.1];decide
  let caller := cachedCaller s.frame valid
  let callerValid : 11 < caller.locals.size := by
    simpa only [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using valid
  {PtrMetadataExecution.writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid with location := .mir ⟨3,0⟩}

/-- The actual positive, nonzero-count prefix through the shared Ref, Len call,
body, protector release, pop and scalar return. The original mutable source's
full buffer authority is restored under the actual post-pop global. This is a
conditional execution theorem; ordinary admission and the empty branch remain
separate coverage obligations. -/
theorem invoke_after_shared {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) :
    ∃ (s : SharedStage input count) (root : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (held : MachineHooks.BorrowState) (completion : Completion),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] root post) ∧
      root = s.lenFrame ∧
      root.location = .mir ⟨3,0⟩ ∧
      root.locals[11]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      root.returnPlace = (s.out.frame count).returnPlace ∧
      post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global ∧
      Completes entry.allocation.extra completion ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion held.global.protectedTags s.out.source.base.raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations ∧
      entry.allocation = s.entry.allocation.setExtra entry.allocation.extra ∧
      post.memory = RetagEntry.updatedMemory s.machine.memory call.sourceId
        {s.entry with allocation := s.entry.allocation.setExtra s.tree} entry.allocation.extra ∧
      post.user.addresses = s.machine.user.addresses ∧
      post.user.payload.payload.user.types = s.machine.user.payload.payload.user.types ∧
      DuplicatePrefixCallModel.Model options remaining span post ∧
      DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness post call ∧
      (∃ thread, post.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0) ∧
      held.global.nextPointerTag.value.toNat = s.held.global.nextPointerTag.value.toNat+1 ∧
      entry.allocation.extra.nodes.size ≤ s.entry.allocation.extra.nodes.size+2 ∧
      (∀ index node, s.entry.allocation.extra.nodes.get index = some node →
        ∃ next, entry.allocation.extra.nodes.get index = some next ∧ next.tag = node.tag ∧
          next.parent = node.parent ∧ next.isExposed = node.isExposed) ∧
      ParentTagOrder entry.allocation.extra ∧ entry.allocation.extra.locations.size = entry.allocation.byteSize ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) ∧
      (∀ query, held.global.protectedTags.get query = s.out.borrowed.output.global.protectedTags.get query) ∧
      (∀ id otherEntry, id≠call.sourceId →
        (s.out.machine count).memory.live.find? (fun row => row.1 == id) = some (id,otherEntry) →
        post.memory.live.find? (fun row => row.1 == id) = some (id,otherEntry)) ∧
      (∃ (reader helper : UniIndex) (output : GeneralBorrowForestFnEntry.Output),
        s.tree.indexOfTag s.out.borrowed.output.global.nextPointerTag = some reader ∧
        output.child.tree.indexOfTag output.tag = some helper ∧
        s.tree.nodes.get helper = none ∧
        completion = extend (s.completion reader) helper reader ∧
        GeneralBorrowRawSharedFnEntry.operation s.tree s.held.global {} call.sourceId s.out.borrowed.output.global.nextPointerTag
          (UInt64.ofNat call.sourceOffset) len .VisitChildrenOfAccessed = .ok output ∧
        entry.allocation.extra = (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree ∧
        held.global = output.global.endCall output.frame) := by
  obtain ⟨s,helper,machine,trace,helperLocation,retval,⟨returnArgument,returnFacts⟩,cache,output,actual,memory,tracked,frameTracked,helperRace,race,ghost,shallow,destination,continuation,varargs,bodyAddresses,bodyTypes,bodyExtras⟩ :=
    joined_before_return input stackReady memoryReady positive count nonzero
  have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
  change s.frame.body = _ ∧ s.frame.bodyIdentity = _ ∧ s.frame.functionInstance = _ ∧ s.frame.locals.size = _ ∧ _ at shape
  have valid : 11 < s.frame.locals.size := by rw [shape.2.2.2.1];decide
  let caller := cachedCaller s.frame valid
  have callerValid : 11 < caller.locals.size := by simpa only [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using valid
  have slot11 := Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans shape.2.2.2.2.2.2.1)
  have callerLive : caller.locals[11].value = .live (.immediate .uninit) := by
    simp only [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
    exact congrArg LocalState.value slot11
  have callerCached : caller.locals[11].layout = some RootCompilerFacts.usizeLayout := by
    simp only [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have callerRace : caller.extra.dataRace = none := shape.2.2.2.2.2.1
  obtain ⟨reader,readerNode,runtime,complete,order,readerAt,readerTag,readerParent,readerHidden,readable,owned,capacity,bounds,growth,oldNodes,sourceActivity⟩ := SharedStage.logical s positive
  have budgets := SharedStage.budget s positive
  have unheld := SharedStage.reader_unheld s
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨sourceNode,sourceAt,_⟩ := depth.parent reader readerNode readerAt s.out.source.base.raw.child readerParent
  obtain ⟨position,selected,selectedNode,slot,selectedAt,sourcePath⟩ := CandidateCurrentWindowAuthority.root_path s.tree runtime.formed.toGraphState
    s.out.source.base.raw.child sourceNode sourceAt
  have readerPath : Path s.tree selected reader := .step sourcePath readerNode readerAt readerParent
  have nonzeroLen : len ≠ 0 := by intro zero;simp [zero] at positive
  obtain ⟨anchor,released,afterRuntime,afterComplete,afterOwned,afterCapacity,afterGrowth,afterOld,afterOrder,preserveActivity,helperLookup,helperVacant⟩ := len_release s.tree s.held.global call.sourceId (s.completion reader)
    runtime complete order position selected s.out.source.base.raw.child reader selectedNode readerNode slot selectedAt sourcePath readerAt readerPath
    readerParent readerHidden (by rw [readerTag];exact unheld) budgets.1 (UInt64.ofNat call.sourceOffset) len nonzeroLen bounds budgets.2.1 budgets.2.2.2 readable owned
  rw [readerTag] at released afterRuntime afterComplete afterOwned afterCapacity afterGrowth afterOld afterOrder preserveActivity helperLookup
  have outputEq : len_literal s.tree s.held.global call.sourceId budgets.1 s.out.borrowed.output.global.nextPointerTag (UInt64.ofNat call.sourceOffset) len = output :=
    Except.ok.inj ((len_literal_operation s.tree s.held.global call.sourceId budgets.1 s.out.borrowed.output.global.nextPointerTag (UInt64.ofNat call.sourceOffset) len).symm.trans actual)
  rw [outputEq] at released afterRuntime afterComplete afterOwned afterCapacity afterGrowth afterOld afterOrder preserveActivity helperLookup
  let releasedTree := (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree
  have releaseActual : output.child.tree.releaseProtector output.tag output.global.protectedTags = ⟨releasedTree,.Released⟩ := by
    cases equation : output.child.tree.releaseProtector output.tag output.global.protectedTags with
    | mk tree status =>
      have statusEq : status = .Released := by simpa only [equation] using released
      simp only [releasedTree,equation,statusEq]
  have borrowFrameEq : output.frame = ({} : FrameState).addProtector call.sourceId output.tag := by rw [←outputEq];rfl
  have helperTracked : helper.extra.borrowTracker = some output.frame := by rw [borrowFrameEq];exact frameTracked
  have frameOwned : output.frame.protectedTags = #[(call.sourceId,output.tag)] := by rw [borrowFrameEq];rfl
  let validityFuel := options.limits.validation-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have validityEq : options.limits.validation = validityFuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [validityFuel];omega
  let sourceEntry := {s.entry with allocation := s.entry.allocation.setExtra s.tree}
  obtain ⟨root,post,step,rootEq,postMemory,postTracked,postRuntime,postCache⟩ := LenReturnFromReleaseRuntime.step options limits remaining span
    input.machine.settings.debugOff validityFuel validityEq #[] caller helper machine len returnArgument returnFacts helperLocation retval helperRace
    destination continuation varargs callerValid callerLive callerCached callerRace call.sourceId output.tag sourceEntry output.child.tree releasedTree s.machine.memory
    memory ⟨output.global,.Default⟩ output.frame tracked helperTracked frameOwned releaseActual cache race ghost shallow
  let finalEntry := {sourceEntry with allocation := sourceEntry.allocation.setExtra releasedTree}
  let finalHeld : MachineHooks.BorrowState := { (⟨output.global,.Default⟩ : MachineHooks.BorrowState) with global := output.global.endCall output.frame }
  have postAddresses := postRuntime.addresses.trans bodyAddresses
  have postTypes := postRuntime.types.trans bodyTypes
  have postExtras := postRuntime.extras.trans bodyExtras
  have model := shared_model s
  have postModel : DuplicatePrefixCallModel.Model options remaining span post := { model with
    ghostOff := postRuntime.ghost
    shallow := postRuntime.shallow
    defaultTracker := ⟨finalHeld,postTracked,rfl⟩
    noDataRace := postRuntime.race
    noBackend := postRuntime.backend
    metadata := by rw [postTypes];exact model.metadata
    fixedScheduler := postRuntime.fixed
    unchecked := postRuntime.unchecked
    noGc := postRuntime.noGc }
  have sharedData : s.machine.user.payload.payload.user.types = (s.out.machine count).user.payload.payload.user.types ∧
      s.machine.user.payload.payload.user.runtime.extras = (s.out.machine count).user.payload.payload.user.runtime.extras := by
    change (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.payload.user.types = _ ∧
      (RootZeroCompleteState.tick options remaining span (s.out.machine count)).user.payload.payload.user.runtime.extras = _
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl⟩
  have origins : DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types := by
    rw [postTypes,sharedData.1]
    exact s.out.cacheOrigins count
  have ready := s.facts.memoryReady.transport (postExtras.trans sharedData.2)
  have counter : finalHeld.global.nextPointerTag.value.toNat = s.held.global.nextPointerTag.value.toNat+1 := by
    dsimp only [finalHeld]
    rw [←outputEq]
    exact GenericFunctionEntryNumerics.successor_value s.held.global.nextPointerTag budgets.1
  have nodeGrowth : finalEntry.allocation.extra.nodes.size ≤ s.entry.allocation.extra.nodes.size+2 := by
    change releasedTree.nodes.size ≤ s.entry.allocation.extra.nodes.size+2
    have finalBound : releasedTree.nodes.size ≤ s.tree.nodes.size+1 := afterGrowth
    omega
  have oldHigh := GeneralBorrowForestTagHighWater.complete s.tree _ _ runtime.below runtime.formed.allocator.nodeTags
  have newUnheld := (GenericFunctionTagFormation.fresh_above s.tree _ _ s.held.global.nextPointerTag oldHigh (Nat.le_refl _)).2.2
  have sameFlags : ∀ query, finalHeld.global.protectedTags.get query = s.out.borrowed.output.global.protectedTags.get query := by
    intro query
    change finalHeld.global.protectedTags.get query = s.held.global.protectedTags.get query
    by_cases same : query = s.held.global.nextPointerTag
    · subst query
      have tagEq : output.tag = s.held.global.nextPointerTag := by rw [←outputEq];rfl
      have afterUnheld : finalHeld.global.protectedTags.contains s.held.global.nextPointerTag = false := by
        change (output.global.endCall output.frame).protectedTags.contains s.held.global.nextPointerTag = false
        rw [←tagEq]
        simp [StackPopRelease.end_call_contains,frameOwned]
      rw [get_none _ _ afterUnheld,get_none _ _ newUnheld]
    · dsimp only [finalHeld]
      rw [←outputEq]
      exact ProtectorRoundTrip.singleton_get (GeneralBorrowFnEntryRegistration.advanced s.held.global budgets.1)
        call.sourceId s.held.global.nextPointerTag query .StrongProtector same
  have otherLive : ∀ id otherEntry, id≠call.sourceId →
      (s.out.machine count).memory.live.find? (fun row => row.1 == id) = some (id,otherEntry) →
      post.memory.live.find? (fun row => row.1 == id) = some (id,otherEntry) := by
    intro id otherEntry different original
    have clockMemory : (RootZeroCompleteState.tick options remaining span (s.out.machine count)).memory = (s.out.machine count).memory := by
      unfold RootZeroCompleteState.tick SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    have first : s.machine.memory.live.find? (fun row => row.1 == id) = some (id,otherEntry) := by
      change (StackPopRelease.commitTree (RootZeroCompleteState.tick options remaining span (s.out.machine count)).memory call.sourceId s.entry s.tree).live.find? _ = _
      exact StackPopRelease.lookup_commit_other _ call.sourceId id s.entry otherEntry s.tree different (by rw [clockMemory];exact original)
    rw [postMemory]
    exact StackPopRelease.lookup_commit_other s.machine.memory call.sourceId id sourceEntry otherEntry releasedTree different first
  have readerLookup : s.tree.indexOfTag s.out.borrowed.output.global.nextPointerTag = some reader := by
    rw [←readerTag]
    exact (complete.2.2.2.2.1 reader readerNode readerAt).1
  refine ⟨s,root,post,finalEntry,finalHeld,extend (s.completion reader) anchor reader,
    SuccessfulTrace.append trace (.next step (.refl _)),rootEq,?_,?_,?_,?_,postTracked,afterRuntime,afterComplete,afterOwned,
    ?_,postMemory,postAddresses,postTypes,postModel,origins,ready,postCache rfl,counter,nodeGrowth,?_,afterOrder,afterCapacity.trans capacity,preserveActivity s.out.source.base.raw.child sourceActivity,sameFlags,otherLive,
    ⟨reader,anchor,output,readerLookup,helperLookup,helperVacant,rfl,actual,rfl,rfl⟩⟩
  · rw [rootEq]
  · rw [rootEq]
    simp only [PtrMetadataExecution.writeFrame,Array.getElem?_set,Array.getElem?_eq_getElem callerValid,ite_true,callerCached]
  · rw [rootEq]
    exact shape.2.2.2.2.2.2.2.2.1
  · rw [postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · rfl
  · intro index node nodeAt
    obtain ⟨middle,middleAt,middleTag,middleParent,middleHidden⟩ := oldNodes index node nodeAt
    obtain ⟨next,nextAt,nextTag,nextParent,nextHidden⟩ := afterOld index middle middleAt
    exact ⟨next,nextAt,nextTag.trans middleTag,nextParent.trans middleParent,nextHidden.trans middleHidden⟩

end
end DuplicatePrefix.CurrentCallLen
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallLen.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual current Len dependency {dependency}"
