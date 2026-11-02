import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroChildMetadata
import duplicate_prefix.S05ConcreteProtectedChildAuthority
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.ChildBorrow

namespace DuplicatePrefix.CurrentCallEmptyEntryConcreteZero
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshGraph GeneralBorrowFreshOwnership GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] UniValMap.insert
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
private theorem frame_of_stage (tree after : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts after global)
    (child parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshChild.child newTag parent) mapping locations))
    (size : after.nodes.data.size = max tree.nodes.data.size (child.toNat+1))
    (roots : after.roots = tree.roots) : LeafFrame tree after child parent := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) mapping locations
  have different : parent ≠ child := by
    intro same; rw [same,vacant] at parentAt; cases parentAt
  have parentStage : stage.nodes.get parent = some (updatedParent parentNode child) := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes,updatedParent]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have childStage : stage.nodes.get child = some (GeneralBorrowFreshChild.child newTag parent) := by
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

private theorem lookup_shape (first second : LocationTree) (same : locationShape second = locationShape first)
    (index : UniIndex) : (second.perms.get index).map stateShape = (first.perms.get index).map stateShape := by
  have cell := congrArg (fun rows => rows[index.toNat]?) same
  simp only [locationShape,Array.getElem?_map] at cell
  have flat := congrArg (fun value : Option (Option StateShape) => value.getD none) cell
  unfold UniValMap.get
  cases firstAt : first.perms.data[index.toNat]? <;> cases secondAt : second.perms.data[index.toNat]? <;> simp_all

private theorem effective_shape (first second : LocationTree) (old next : TreeNode)
    (same : locationShape second = locationShape first)
    (permission : next.defaultInitialPermission = old.defaultInitialPermission) (index : UniIndex) :
    stateShape (RawState second index next) = stateShape (RawState first index old) := by
  have cell := lookup_shape first second same index
  unfold RawState
  cases oldAt : first.perms.get index <;> cases nextAt : second.perms.get index <;>
    simp_all [stateShape,TreeNode.defaultLocationState]

private theorem authority_state (old next : LocationState) (same : stateShape next = stateShape old)
    (held : Bool) :
    (LocalWrite next held ↔ LocalWrite old held) ∧ (ForeignWrite next held ↔ ForeignWrite old held) := by
  have permission := congrArg Prod.fst same
  have accessed := congrArg Prod.snd same
  simp only [stateShape] at permission accessed
  simp [LocalWrite,ForeignWrite,LocationState.possible,permission,accessed]


private theorem shape_authority (before after : BorrowTree) (completion : Completion)
    (held : ProtectedTags) (source : UniIndex) (first second : LocationTree)
    (nodes : treeShape after = treeShape before) (locations : locationShape second = locationShape first)
    (authority : Authority before completion held source first) :
    Authority after completion held source second := by
  intro index node present
  obtain ⟨old,oldAt,tag,parent,children,permission⟩ :=
    GeneralBorrowFreshMetadata.node_fields after before nodes.symm index node present
  have scalar := authority_state (RawState first index old) (RawState second index node)
    (effective_shape first second old node locations permission.symm index) (held.contains node.tag)
  have original := authority index old oldAt
  rw [tag] at original
  exact ⟨fun below => scalar.1.mpr (original.1 below),fun outside => scalar.2.mpr (original.2 outside)⟩

private theorem shape_owned (before after : BorrowTree) (completion : Completion)
    (held : ProtectedTags) (source : UniIndex) (lower upper : UInt64)
    (same : treeShape after = treeShape before)
    (owned : OwnedOn (Authority before completion held source) lower upper before.locations) :
    OwnedOn (Authority after completion held source) lower upper after.locations := by
  have entries := congrArg (fun shape => shape.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid positive lowerBound upperBound
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  have original := owned position oldValid positive (by simpa only [←cell.1] using lowerBound)
    (by simpa only [←cell.1] using upperBound)
  exact shape_authority before after completion held source _ _ same cell.2 original


private theorem stage_owned (tree : BorrowTree) (parentTag tag : BorTag)
    (input : ConcreteEmptyPoolEntry.Input tree parentTag tag) (completion : Completion)
    (complete : Completes tree completion) (held : ProtectedTags)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : tree.nodes.get target = some targetNode)
    (lower upper : UInt64)
    (owned : OwnedOn (Authority tree completion held target) lower upper tree.locations) :
    OwnedOn (Authority input.stage (extend completion input.index input.parent) held target)
      lower upper input.stage.locations := by
  intro position valid positive lowerBound upperBound
  have old := owned position valid positive lowerBound upperBound
  intro query node present
  have ancestry := S05ConcreteProtectedChildCompletion.old_ancestry_iff tree completion complete input.index input.parent
    input.vacant ⟨targetNode,targetAt⟩ (ancestor := query) (target := target)
  by_cases fresh : query = input.index
  · subst query
    have eq : node = GeneralBorrowFreshChild.child tag input.parent :=
      Option.some.inj (present.symm.trans input.stage_new)
    subst node
    have clean := input.clean position valid
    change (input.stage.locations.entries[position]'valid).data.perms.get input.index = none at clean
    simp only [RawState,clean,Option.getD_none]
    constructor
    · intro _
      simp [LocalWrite,GeneralBorrowFreshChild.child,TreeNode.defaultLocationState,LocationState.possible,Permission.isUnique]
    · intro _
      simp [ForeignWrite,GeneralBorrowFreshChild.child,TreeNode.defaultLocationState,LocationState.possible,Permission.isUnique]
  · let lifted := S04ZeroLeafCallbackAttach.liftNode input.parent input.index query
    have oldNode : ∃ oldNode, tree.nodes.get query = some oldNode ∧ node.tag = oldNode.tag ∧
        node.defaultInitialPermission = oldNode.defaultInitialPermission := by
      by_cases parent : query = input.parent
      · subst query
        have oldAt := GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree input.index input.parent input.parentNode
          (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present
        change input.stage.nodes.get input.parent = some (GeneralBorrowFreshGraph.updatedParent input.parentNode input.index) at oldAt
        have eq := Option.some.inj (present.symm.trans oldAt)
        exact ⟨input.parentNode,input.present,by rw [eq];rfl,by rw [eq];rfl⟩
      · have same := GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree input.index input.parent query input.parentNode
          (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present parent fresh
        change input.stage.nodes.get query = tree.nodes.get query at same
        exact ⟨node,same.symm.trans present,rfl,rfl⟩
    obtain ⟨oldNode,oldAt,tagEq,permissionEq⟩ := oldNode
    have raw : stateShape (RawState (tree.locations.entries[position]'valid).data query node) =
        stateShape (RawState (tree.locations.entries[position]'valid).data query oldNode) := by
      unfold RawState
      cases (tree.locations.entries[position]'valid).data.perms.get query <;>
        simp [stateShape,TreeNode.defaultLocationState,permissionEq]
    have scalar := authority_state _ _ raw (held.contains node.tag)
    have initial := old query oldNode oldAt
    rw [←tagEq] at initial
    exact ⟨fun below => scalar.1.mpr (initial.1 (ancestry.mp below)),
      fun outside => scalar.2.mpr (initial.2 (fun below => outside (ancestry.mpr below)))⟩

/-- The actual empty concrete source constructor retains the original Bool
window under the same completion extended by its actual physical parent. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag = true) (parentOlder : parentNode.tag.value ≤ newTag.value)
    (offset : UInt64) (boolGrant : UniIndex) (boolNode : TreeNode) (boolPresent : tree.nodes.get boolGrant = some boolNode)
    (lower upper : UInt64)
    (owned : OwnedOn (Authority tree completion global.protectedTags boolGrant) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        Completes actual.tree (extend completion child parent) ∧ ParentTagOrder actual.tree ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags boolGrant)
          lower upper actual.tree.locations ∧
        ∃ nextBoolNode, actual.tree.nodeAt boolGrant = some nextBoolNode ∧
          nextBoolNode.tag = boolNode.tag ∧ nextBoolNode.isExposed = boolNode.isExposed := by
  have output := S04ZeroConcreteRuntime.construct tree global runtime parentTag parent parentNode tagged present newTag fresh room tagBound held offset
  have accounting := runtime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let input := ConcreteEmptyPoolEntry.factory tree parentTag newTag parent parentNode
    (Classical.choice runtime.formed.depth) tagged present fresh runtime.formed.allocator.pool accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean runtime)
  rw [input.child offset] at output
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts input.after global := by
    simpa only [input.child offset] using output.2.1
  have shape := GeneralBorrowSifaView.preserves input.stage input.parent .None
  have exposure := GeneralBorrowFreshMetadataChildSifa.sifa_exposure input.stage input.parent .None
  have nodeSize : input.after.nodes.data.size = max tree.nodes.data.size (input.index.toNat+1) := by
    have known := ConcreteEmptyPoolEntryNext.node_size input
    change input.after.nodes.data.size = tree.nodes.data.size + ConcreteEmptyPoolEntryNext.growth input at known
    rw [known]
    cases selected : input.slot with
    | append noFree aligned fit =>
      have endEq : input.index.toNat = tree.nodes.data.size := by
        simp only [ConcreteEmptyPoolEntry.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,
          UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
        exact aligned
      simp only [ConcreteEmptyPoolEntryNext.growth,selected]
      omega
    | reuse index available bounded missing slack =>
      have same : input.index = index := by
        simp only [ConcreteEmptyPoolEntry.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index]
      simp only [ConcreteEmptyPoolEntryNext.growth,selected]
      rw [same]
      change _ = max _ (index.toNat+1)
      change index.toNat < tree.nodes.data.size at bounded
      omega
  have frame := frame_of_stage tree input.after global afterRuntime input.index input.parent input.parentNode newTag
    input.vacant input.present input.mapping tree.locations shape exposure nodeSize (S04ZeroChildMetadata.roots tree parentTag newTag input)
  have completed := S05ConcreteProtectedChildCompletion.completes_of_leaf tree input.after completion complete input.index input.parent frame
  have nextOrder := GeneralBorrowFreshParentTagOrder.staged_order tree input.depth order input.index input.parent input.parentNode
    (GeneralBorrowFreshChild.child newTag input.parent) input.vacant input.present rfl parentOlder input.mapping tree.locations input.after shape
  have staged := stage_owned tree parentTag newTag input completion complete global.protectedTags boolGrant boolNode boolPresent lower upper owned
  have retained := shape_owned input.stage input.after (extend completion input.index input.parent) global.protectedTags boolGrant lower upper shape staged
  have lookup : input.after.indexOfTag newTag = some input.index := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping newTag fresh input.index input.free
  obtain ⟨nextBoolNode,nextAt,nextTag,nextParent,nextExposed⟩ := frame.old boolGrant boolNode boolPresent
  dsimp only
  rw [show ChildBorrow.fnEntryLocation = GeneralBorrowFreshChild.inside from rfl, input.child offset]
  exact ⟨output.1,afterRuntime,output.2.2.1,output.2.2.2,input.index,lookup,completed,nextOrder,retained,
    nextBoolNode,nextAt,nextTag,nextExposed⟩
end DuplicatePrefix.CurrentCallEmptyEntryConcreteZero
