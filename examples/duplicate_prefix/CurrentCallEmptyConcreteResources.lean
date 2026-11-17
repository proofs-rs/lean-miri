import duplicate_prefix.CurrentCallEmptyEntryConcreteZero
import duplicate_prefix.CurrentCallResourceChild
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime

/-! Empty concrete FnEntry preserves an existing current byte resource. The
new dormant node retains its actual physical parent; no source ownership or
completed assignment of unrelated roots is required. -/
namespace DuplicatePrefix.CurrentCallEmptyConcreteResources
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshGraph GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert
noncomputable section
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


private def Row (tree : BorrowTree) (C : Completion) (held : ProtectedTags)
    (grant : UniIndex) (location : LocationTree) (demand : Demand) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    (Below C index grant → demand ∈ tokens (denote (RawState location index node) (held.contains node.tag))) ∧
    (Clash (CandidateCurrentGrantResources.guard (denote (RawState location index node) (held.contains node.tag))) demand →
      Below C index grant)

private theorem denote_shape (old next : LocationState) (same : stateShape next = stateShape old)
    (held : Bool) : denote next held = denote old held := by
  have permission := congrArg Prod.fst same
  have accessed := congrArg Prod.snd same
  simp only [stateShape] at permission accessed
  simp only [denote,permission,accessed]

private theorem shape_row (before after : BorrowTree) (C : Completion) (held : ProtectedTags)
    (grant : UniIndex) (first second : LocationTree) (demand : Demand)
    (nodes : treeShape after = treeShape before) (locations : locationShape second = locationShape first)
    (owned : Row before C held grant first demand) : Row after C held grant second demand := by
  intro index node present
  obtain ⟨old,oldAt,tag,_,_,permission⟩ := GeneralBorrowFreshMetadata.node_fields after before nodes.symm index node present
  have scalar := denote_shape (RawState first index old) (RawState second index node)
    (effective_shape first second old node locations permission.symm index) (held.contains node.tag)
  have initial := owned index old oldAt
  rw [tag] at initial
  rw [scalar]
  exact initial

private theorem stage_row (tree : BorrowTree) (parentTag tag : BorTag)
    (input : ConcreteEmptyPoolEntry.Input tree parentTag tag) (C : Completion)
    (model : ParentInterpretation tree C) (held : ProtectedTags)
    (grant : UniIndex) (grantNode : TreeNode) (grantAt : tree.nodes.get grant = some grantNode)
    (location : LocationTree) (clean : location.perms.get input.index = none) (demand : Demand)
    (owned : Row tree C held grant location demand) :
    Row input.stage (extend C input.index input.parent) held grant location demand := by
  intro query node present
  have ancestry := CurrentCallResourceChild.old_ancestry_iff tree C model input.index input.parent
    input.vacant ⟨grantNode,grantAt⟩ (ancestor := query) (target := grant)
  by_cases fresh : query = input.index
  · subst query
    have same : node = GeneralBorrowFreshChild.child tag input.parent := Option.some.inj (present.symm.trans input.stage_new)
    subst node
    constructor
    · intro _
      cases flag : held.contains tag <;> cases demand <;>
        simp [RawState,clean,GeneralBorrowFreshChild.child,TreeNode.defaultLocationState,tokens,denote,flag]
    · intro clash
      cases flag : held.contains tag <;> cases demand <;>
        simp [RawState,clean,GeneralBorrowFreshChild.child,TreeNode.defaultLocationState,
          denote,CandidateCurrentGrantResources.guard,Clash,flag] at clash
  · have previous : ∃ oldNode, tree.nodes.get query = some oldNode ∧ node.tag = oldNode.tag ∧
        node.defaultInitialPermission = oldNode.defaultInitialPermission := by
      by_cases parent : query = input.parent
      · subst query
        have oldAt := GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree input.index input.parent input.parentNode
          (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present
        change input.stage.nodes.get input.parent = some (updatedParent input.parentNode input.index) at oldAt
        have eq := Option.some.inj (present.symm.trans oldAt)
        exact ⟨input.parentNode,input.present,by rw [eq];rfl,by rw [eq];rfl⟩
      · have same := GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree input.index input.parent query input.parentNode
          (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present parent fresh
        change input.stage.nodes.get query = tree.nodes.get query at same
        exact ⟨node,same.symm.trans present,rfl,rfl⟩
    obtain ⟨oldNode,oldAt,tagEq,permissionEq⟩ := previous
    have raw : stateShape (RawState location query node) = stateShape (RawState location query oldNode) := by
      unfold RawState
      cases location.perms.get query <;> simp [stateShape,TreeNode.defaultLocationState,permissionEq]
    have scalar := denote_shape _ _ raw (held.contains node.tag)
    have initial := owned query oldNode oldAt
    rw [←tagEq] at initial
    rw [scalar]
    exact ⟨fun below => initial.1 (ancestry.mp below),fun clash => ancestry.mpr (initial.2 clash)⟩

/-- SIFA may change its cache. Permission/accessed observations and every
actual protector guard remain framed, including the reused dormant slot. -/
theorem embeds (allocation : Allocation Provenance BorrowTree) (global : GlobalState) (C : Completion)
    (model : ParentInterpretation allocation.extra C) (parentTag tag : BorTag)
    (input : ConcreteEmptyPoolEntry.Input allocation.extra parentTag tag)
    (grant : UniIndex) (grantNode : TreeNode) (grantAt : allocation.extra.nodes.get grant = some grantNode)
    (byte : Nat) (demand : Demand) (owned : Embeds allocation global.protectedTags C grant byte demand) :
    Embeds (allocation.setExtra input.after) global.protectedTags (extend C input.index input.parent) grant byte demand := by
  intro segment member lower upper
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  change position < input.after.locations.entries.size at valid
  change input.after.locations.entries[position] = segment at same
  have oldValid : position < allocation.extra.locations.entries.size := by
    rw [S04ZeroChildMetadata.length _ _ _ input] at valid
    exact valid
  have rows := congrArg (fun shape => shape.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .None)
  change input.after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    allocation.extra.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  have cell := congrArg (fun entries => entries[position]?) rows
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  change (input.after.locations.entries[position]'valid).range =
    (allocation.extra.locations.entries[position]'oldValid).range ∧
    locationShape (input.after.locations.entries[position]'valid).data =
      locationShape (allocation.extra.locations.entries[position]'oldValid).data at cell
  have previous : Row allocation.extra C global.protectedTags grant
      (allocation.extra.locations.entries[position]'oldValid).data demand := by
    apply owned _ (Array.mem_toList_iff.mpr (Array.getElem_mem oldValid))
    · rw [←cell.1,same]; exact lower
    · rw [←cell.1,same]; exact upper
  have staged := stage_row allocation.extra parentTag tag input C model global.protectedTags grant grantNode grantAt
    _ (input.clean position oldValid) demand previous
  have final := shape_row input.stage input.after (extend C input.index input.parent) global.protectedTags
    grant _ _ demand (GeneralBorrowSifaView.preserves input.stage input.parent .None) cell.2 staged
  rw [same] at final
  exact final

/-- Spatial metadata survives actual parent/SIFA updates. -/
theorem metadata (tree : BorrowTree) (parentTag tag : BorTag)
    (input : ConcreteEmptyPoolEntry.Input tree parentTag tag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :
    ∃ next,input.after.nodes.get query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission := by
  let staged := S04ZeroLeafCallbackAttach.liftNode input.parent input.index query node
  have found : input.stage.nodeAt query = some staged :=
    S04ZeroLeafCallbackAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present query node present
  obtain ⟨next,nextAt,tagEq,parentEq,_,permissionEq,exposedEq⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .None query staged found
  have fields : staged.tag = node.tag ∧ staged.parent = node.parent ∧
      staged.isExposed = node.isExposed ∧ staged.defaultInitialPermission = node.defaultInitialPermission := by
    by_cases same : query = input.parent <;>
      simp [staged,S04ZeroLeafCallbackAttach.liftNode,same]
  exact ⟨next,nextAt,tagEq.trans fields.1,parentEq.trans fields.2.1,
    exposedEq.trans fields.2.2.1,permissionEq.trans fields.2.2.2⟩

/-- The actual zero constructor requires no ownership of its source parent. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (order : ParentTagOrder tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag = true) (parentOlder : parentNode.tag.value ≤ newTag.value)
    (offset : UInt64) (boolGrant : UniIndex) (boolNode : TreeNode) (boolPresent : tree.nodes.get boolGrant = some boolNode)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        ParentInterpretation actual.tree (extend completion child parent) ∧ ParentTagOrder actual.tree ∧
        LeafFrame tree actual.tree child parent ∧
        (∀ query node,tree.nodes.get query = some node →
          ∃ next,actual.tree.nodes.get query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
            next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission) ∧
        (∀ (allocation : Allocation Provenance BorrowTree) grant grantNode,
          tree.nodes.get grant = some grantNode → ∀ byte demand,
          Embeds (allocation.setExtra tree) global.protectedTags completion grant byte demand →
          Embeds (allocation.setExtra actual.tree) global.protectedTags (extend completion child parent) grant byte demand) ∧
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
  have completed := CurrentCallParentInsertion.of_leaf tree input.after completion complete input.index input.parent frame primaryLive afterRuntime.formed.toGraphState (GeneralBorrowFreshParentTagOrder.staged_order tree input.depth order input.index input.parent input.parentNode
    (GeneralBorrowFreshChild.child newTag input.parent) input.vacant input.present rfl parentOlder input.mapping tree.locations input.after shape)
  have nextOrder := GeneralBorrowFreshParentTagOrder.staged_order tree input.depth order input.index input.parent input.parentNode
    (GeneralBorrowFreshChild.child newTag input.parent) input.vacant input.present rfl parentOlder input.mapping tree.locations input.after shape
  have lookup : input.after.indexOfTag newTag = some input.index := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping newTag fresh input.index input.free
  obtain ⟨nextBoolNode,nextAt,nextTag,nextParent,nextExposed⟩ := frame.old boolGrant boolNode boolPresent
  dsimp only
  rw [show ChildBorrow.fnEntryLocation = GeneralBorrowFreshChild.inside from rfl, input.child offset]
  refine ⟨output.1,afterRuntime,output.2.2.1,output.2.2.2,input.index,lookup,completed,nextOrder,frame,
    metadata tree parentTag newTag input,?_,nextBoolNode,nextAt,nextTag,nextExposed⟩
  intro allocation grant grantNode grantAt byte demand owned
  exact embeds (allocation.setExtra tree) global completion complete parentTag newTag input grant grantNode grantAt byte demand owned

/-- Real fresh Strong registration observes every old node identically. -/
theorem registered_embeds (allocation : Allocation Provenance BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra global)
    (frame : FrameState) (id : AllocId) (room : global.nextPointerTag.value < 18446744073709551615)
    (C : Completion) (grant : UniIndex) (byte : Nat) (demand : Demand)
    (owned : Embeds allocation global.protectedTags C grant byte demand) :
    Embeds allocation (GeneralBorrowFnEntryRegistration.registered global frame id room).1.protectedTags
      C grant byte demand := by
  obtain ⟨_,_,_,_,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare allocation.extra global frame id room runtime
  intro segment member lower upper index node present
  have same := ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
    (nodeFresh (index,node) (Array.mem_toList_iff.mp
      ((GeneralBorrowFreshReuseProtection.entries_get allocation.extra.nodes index node).mpr present)))
  change ((GeneralBorrowFnEntryRegistration.registered global frame id room).1.protectedTags).contains node.tag =
    global.protectedTags.contains node.tag at same
  rw [same]
  exact owned segment member lower upper index node present

/-- Actual registration and the actual zero-byte concrete constructor retain
one existing Bool grant, in the SAME allocation even when its parent is the
empty argument's parent. No source family, contents or issuance is required. -/
theorem installed {before : Before} {tracker : MachineHooks.BorrowState} {data : CandidateCurrentJointCall.Identities}
    {owner : Nat} {id : AllocId} {offset : Nat}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : B.allocation.extra.indexOfTag parentTag = some parent)
    (parentAt : B.allocation.extra.nodeAt parent = some parentNode)
    (frame : FrameState) (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1 ≤ 4294967295) (sourceOffset : UInt64)
    (post : Before)
    (postPresent : Present (ActualWorld post) id (B.allocation.setExtra
      (B.allocation.extra.newChild (Size.ofBytes sourceOffset) (.concrete parentTag) tracker.global.nextPointerTag
        (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true).tree)) :
    let registered := GeneralBorrowFnEntryRegistration.registered tracker.global frame id tagRoom
    let next := {tracker with global := registered.1}
    let actual := B.allocation.extra.newChild (Size.ofBytes sourceOffset) (.concrete parentTag) tracker.global.nextPointerTag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree next.global ∧
    actual.tree.nodes.size ≤ B.allocation.extra.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
      (extend B.precise.completion child parent).parents[child.toNat]? = some (some parent) ∧
      ParentInterpretation actual.tree (extend B.precise.completion child parent) ∧
      PointerBinds (B.allocation.setExtra actual.tree) B.pointer ∧
      SpatialDelegation post next id (B.allocation.setExtra actual.tree) (extend B.precise.completion child parent) B.pointer.grant ∧
      (∀ byte,Window id offset 1 byte → byte.2 < (B.allocation.setExtra actual.tree).len ∧
        Embeds (B.allocation.setExtra actual.tree) next.global.protectedTags
          (extend B.precise.completion child parent) B.pointer.grant byte.2 (demandOf .ret)) := by
  let registered := GeneralBorrowFnEntryRegistration.registered tracker.global frame id tagRoom
  let next := {tracker with global := registered.1}
  let actual := B.allocation.extra.newChild (Size.ofBytes sourceOffset) (.concrete parentTag) tracker.global.nextPointerTag
    (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  obtain ⟨_,held,_,advanced,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare B.allocation.extra tracker.global frame id tagRoom runtime
  have tagBound : tracker.global.nextPointerTag.value.toNat < registered.1.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag tagRoom).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have heldBool : registered.1.protectedTags.contains tracker.global.nextPointerTag = true := by
    simp only [ProtectedTags.contains,registered,held,Option.isSome_some]
  have parentOlder : parentNode.tag.value ≤ tracker.global.nextPointerTag.value := by
    have less := GeneralBorrowForestTagHighWater.mapped B.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag
      parentNode.tag runtime.below parent (runtime.formed.allocator.nodeTags parent parentNode parentAt)
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt less)
  obtain ⟨boolNode,boolAt,_,_⟩ := B.binding
  obtain ⟨root,rootAt,_,_,_⟩ := B.issued.capability.rootNode
  have built := construct B.allocation.extra registered.1 B.precise.completion advanced B.parents B.parents.order
    parentTag tracker.global.nextPointerTag parent parentNode tagged parentAt fresh nodeRoom tagBound heldBool
    parentOlder sourceOffset B.pointer.grant boolNode boolAt ⟨root,rootAt⟩
  change actual.outcome = .ok () ∧ _ at built
  obtain ⟨done,current,capacity,growth,child,childAt,parents,_,leaf,old,embedding,_⟩ := built
  have binding : PointerBinds (B.allocation.setExtra actual.tree) B.pointer := by
    obtain ⟨oldNode,oldAt,_,oldValue⟩ := B.binding
    obtain ⟨node,nodeAt,tag,_,exposed,_⟩ := old B.pointer.grant oldNode oldAt
    refine ⟨node,nodeAt,current.formed.allocator.nodeTags B.pointer.grant node nodeAt,?_⟩
    cases provenance : B.pointer.value.provenance with
    | concrete pointerId pointerTag => simpa only [provenance,tag] using oldValue
    | wildcard => simpa only [provenance,exposed] using oldValue
  have roots : actual.tree.roots = B.allocation.extra.roots := leaf.roots
  have issued := CurrentCallResourceInstallation.spatial B.issued B.parents post next actual.tree postPresent
    (by rfl) capacity (by intro position root slot;rw [roots];exact slot) old child parent leaf.vacant
  refine ⟨done,current,growth,child,childAt,child_edge _ _ _,parents,binding,issued,?_⟩
  intro byte inside
  obtain ⟨bound,owned⟩ := B.window byte inside
  refine ⟨bound,?_⟩
  have registeredOwned := registered_embeds B.allocation tracker.global runtime frame id tagRoom
    B.precise.completion B.pointer.grant byte.2 (demandOf .ret) owned
  exact embedding B.allocation B.pointer.grant boolNode boolAt byte.2 (demandOf .ret) registeredOwned

end
end DuplicatePrefix.CurrentCallEmptyConcreteResources
