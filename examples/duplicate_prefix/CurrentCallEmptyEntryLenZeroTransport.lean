import duplicate_prefix.S03EmptyPositiveTreeFacts
import duplicate_prefix.S05ConcreteProtectedChildCompletion
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroTransport
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapState GeneralBorrowView
open S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
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
private theorem frame_of_stage (tree after : BorrowTree) (global : GlobalState)
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


/-- The REAL zero Shared child extends the same completion at its actual
allocator slot, retaining every old virtual origin and parent edge. -/
theorem leaf_frame (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat) :
    LeafFrame tree input.after input.index input.parent := by
  have afterRuntime := S03EmptySharedRuntime.construct tree global runtime parentTag tag input room tagBound
  have size : input.after.nodes.data.size=max tree.nodes.data.size (input.index.toNat+1) := by
    have nodes := EmptyForestSharedPoolNext.node_size input
    change input.after.nodes.data.size=tree.nodes.data.size+EmptyForestSharedPoolNext.growth input at nodes
    rw [nodes]
    cases selected : input.slot with
    | append noFree aligned fits =>
      have endEq : input.index.toNat=tree.nodes.data.size := by
        simp only [EmptyForestSharedPool.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,UniIndex.toNat,
          UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size<2^32)]
        exact aligned
      simp only [EmptyForestSharedPoolNext.growth,selected,endEq]
      omega
    | reuse child available bounded missing slack =>
      have inside : input.index.toNat<tree.nodes.data.size := by
        simpa only [EmptyForestSharedPool.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index] using bounded
      simp only [EmptyForestSharedPoolNext.growth,selected,Nat.add_zero]
      omega
  have frame := frame_of_stage tree input.after global afterRuntime input.index input.parent input.parentNode tag
    input.vacant input.present input.mapping tree.locations (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
    (GeneralBorrowFreshMetadataChildSifa.sifa_exposure input.stage input.parent .Read) size
    (GeneralBorrowFreshMetadata.roots input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .Read))
  exact frame

theorem completes (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat) :
    Completes input.after (extend completion input.index input.parent) :=
  completes_of_leaf tree input.after completion complete input.index input.parent
    (leaf_frame tree global runtime parentTag tag input room tagBound)

private theorem lookup_shape (location : LocationTree) (index : UniIndex) :
    (⟨locationShape location⟩ : UniValMap StateShape).get index = (location.perms.get index).map stateShape := by
  unfold locationShape UniValMap.get
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

private theorem raw_shape (before after : LocationTree) (index : UniIndex) (old next : TreeNode)
    (shape : locationShape after=locationShape before) (permission : next.defaultInitialPermission=old.defaultInitialPermission) :
    stateShape (RawState after index next)=stateShape (RawState before index old) := by
  have same := congrArg (fun states => (⟨states⟩ : UniValMap StateShape).get index) shape
  rw [lookup_shape,lookup_shape] at same
  have defaults : stateShape next.defaultLocationState=stateShape old.defaultLocationState := by
    simp only [stateShape,TreeNode.defaultLocationState,permission]
  cases first : before.perms.get index <;> cases second : after.perms.get index <;>
    simp only [first,second,Option.map_none,Option.map_some,Option.some.injEq] at same
  · simpa only [RawState,first,second,Option.getD_none] using defaults
  · cases same
  · cases same
  · simpa only [RawState,first,second,Option.getD_some] using same

private theorem local_shape (before after : LocationState) (held : Bool) (shape : stateShape after=stateShape before) :
    OrdinaryBorrowAuthority.LocalWrite after held ↔ OrdinaryBorrowAuthority.LocalWrite before held := by
  have permission := congrArg Prod.fst shape
  have accessed := congrArg Prod.snd shape
  simp only [stateShape] at permission accessed
  simp only [OrdinaryBorrowAuthority.LocalWrite,LocationState.possible,permission,accessed]

private theorem foreign_shape (before after : LocationState) (held : Bool) (shape : stateShape after=stateShape before) :
    OrdinaryBorrowAuthority.ForeignWrite after held ↔ OrdinaryBorrowAuthority.ForeignWrite before held := by
  have permission := congrArg Prod.fst shape
  have accessed := congrArg Prod.snd shape
  simp only [stateShape] at permission accessed
  simp only [OrdinaryBorrowAuthority.ForeignWrite,LocationState.possible,permission,accessed]

private theorem old_fields {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index=some node) :
    ∃ next,input.after.nodes.get index=some next ∧ next.tag=node.tag ∧ next.defaultInitialPermission=node.defaultInitialPermission := by
  let staged := S04ZeroReadSharedAttach.liftNode input.parent input.index index node
  have atStage : input.stage.nodeAt index=some staged :=
    S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
  obtain ⟨next,found,tagEq,_,_,permission,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read index staged atStage
  have fields : staged.tag=node.tag ∧ staged.defaultInitialPermission=node.defaultInitialPermission := by
    by_cases same : index=input.parent <;>
      simp only [staged,S04ZeroReadSharedAttach.liftNode,same,ite_true,ite_false,and_self]
  exact ⟨next,found,tagEq.trans fields.1,permission.trans fields.2⟩

private theorem location_shape {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (position : Nat)
    (oldValid : position<tree.locations.entries.size) (newValid : position<input.after.locations.entries.size) :
    locationShape input.after.locations.entries[position].data=locationShape tree.locations.entries[position].data := by
  have shape := congrArg (fun value => value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  change input.after.locations.entries.map (fun row => (row.range,locationShape row.data))=
    tree.locations.entries.map (fun row => (row.range,locationShape row.data)) at shape
  have same := congrArg (fun rows => rows[position]?) shape
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem oldValid,Array.getElem?_eq_getElem newValid,Option.map_some] at same
  exact congrArg Prod.snd (Option.some.inj same)

private theorem rows_length {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) : input.after.locations.entries.size=tree.locations.entries.size := by
  have shape := congrArg (fun value => value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  change input.after.locations.entries.map (fun row => (row.range,locationShape row.data))=
    tree.locations.entries.map (fun row => (row.range,locationShape row.data)) at shape
  have sizes := congrArg Array.size shape
  simpa only [Array.size_map] using sizes

private theorem row_range {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (position : Nat)
    (oldValid : position<tree.locations.entries.size) (newValid : position<input.after.locations.entries.size) :
    input.after.locations.entries[position].range=tree.locations.entries[position].range := by
  have shape := congrArg (fun value => value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  change input.after.locations.entries.map (fun row => (row.range,locationShape row.data))=
    tree.locations.entries.map (fun row => (row.range,locationShape row.data)) at shape
  have same := congrArg (fun rows => rows[position]?) shape
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem oldValid,Array.getElem?_eq_getElem newValid,Option.map_some] at same
  exact congrArg Prod.fst (Option.some.inj same)

private theorem old_edge (completion : Completion) (child parent target predecessor : UniIndex)
    (different : target ≠ child)
    (edge : (extend completion child parent).parents[target.toNat]? = some (some predecessor)) :
    completion.parents[target.toNat]? = some (some predecessor) := by
  have extendedBound := (Array.getElem?_eq_some_iff.mp edge).1
  simp only [extend,Array.size_ofFn] at extendedBound
  by_cases bound : target.toNat < completion.parents.size
  · exact (old_parent completion child parent target different bound).symm.trans edge
  · have missing : completion.parents[target.toNat]? = none := Array.getElem?_eq_none (by omega)
    have unequal : target.toNat ≠ child.toNat := fun equal => different (GeneralBorrowNodeUpdate.index_injective _ _ equal)
    simp [extend,extendedBound,unequal,missing] at edge

/-- A partial completion need only avoid old edges pointing into the REAL
vacant allocator slot. No whole-tree Completes certificate is required. -/
private theorem old_below_iff (completion : Completion) (child parent : UniIndex)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠child)
    (target : UniIndex) (different : target≠child) (ancestor : UniIndex) :
    Below (extend completion child parent) ancestor target ↔ Below completion ancestor target := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _
    | @step predecessor target edge path induction =>
      have original := old_edge completion child parent target predecessor different edge
      exact .step original (induction (noIncoming target predecessor original))
  · intro path
    induction path with
    | refl => exact .refl _
    | @step predecessor target edge path induction =>
      have bound := (Array.getElem?_eq_some_iff.mp edge).1
      exact .step ((old_parent completion child parent target different bound).trans edge)
        (induction (noIncoming target predecessor edge))

private theorem not_below_vacant (completion : Completion) (child target : UniIndex)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠child)
    (different : target≠child) : ¬ Below completion child target := by
  intro path
  have same : target=child := by
    clear different
    induction path with
    | refl => rfl
    | @step predecessor target edge path induction =>
      exact False.elim ((noIncoming target predecessor edge) induction)
  exact different same

/-- A real vacant helper slot cannot be the parent of an existing partial
completion edge when every such parent is an actual old live node. -/
theorem no_incoming (tree : BorrowTree) (completion : Completion)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (parentLive : ∀ (query parent : UniIndex),completion.parents[query.toNat]?=some (some parent) →
      ∃ node,tree.nodes.get parent=some node) :
    ∀ (query parent : UniIndex),completion.parents[query.toNat]?=some (some parent) → parent≠input.index := by
  intro query parent edge same
  obtain ⟨node,present⟩ := parentLive query parent edge
  rw [same,input.vacant] at present
  cases present

/-- Actual old live parents remain live after SIFA; the new completion edge
uses the REAL constructor parent. No full Completes certificate is needed. -/
theorem parent_live (tree : BorrowTree) (completion : Completion)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (parentLive : ∀ (query parent : UniIndex),completion.parents[query.toNat]?=some (some parent) →
      ∃ node,tree.nodes.get parent=some node) :
    ∀ (query parent : UniIndex),(extend completion input.index input.parent).parents[query.toNat]?=some (some parent) →
      ∃ node,input.after.nodes.get parent=some node := by
  intro query parent edge
  by_cases fresh : query=input.index
  · subst query
    have same : parent=input.parent := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge completion input.index input.parent)))
    subst parent
    obtain ⟨node,present,_,_⟩ := old_fields input input.parent input.parentNode input.present
    exact ⟨node,present⟩
  · obtain ⟨old,present⟩ := parentLive query parent (old_edge completion input.index input.parent query parent fresh edge)
    obtain ⟨node,found,_,_⟩ := old_fields input parent old present
    exact ⟨node,found⟩

/-- Actual fresh-slot extension preserves EVERY ancestor relation to an
old live target, even when the supplied completion is only partial. -/
theorem ancestry_iff (tree : BorrowTree) (completion : Completion)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : tree.nodes.get target=some targetNode)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠input.index)
    (ancestor : UniIndex) :
    Below (extend completion input.index input.parent) ancestor target ↔ Below completion ancestor target := by
  have different : target≠input.index := by intro same;rw [same,input.vacant] at targetAt;cases targetAt
  exact old_below_iff completion input.index input.parent noIncoming target different ancestor

/-- Restrict authority from the actual helper extension back to old nodes on
an ARBITRARY SAME current row. Stored helper states may already materialize;
no old-row profile or vacant-permission hypothesis is transported backwards. -/
theorem authority_back (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : tree.nodes.get target=some targetNode)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠input.index)
    (location : LocationTree)
    (authority : S05CompletedAncestryReadMutable.Authority input.after (extend completion input.index input.parent) protections target location) :
    S05CompletedAncestryReadMutable.Authority tree completion protections target location := by
  intro index node present
  obtain ⟨next,nextAt,tagEq,permission⟩ := old_fields input index node present
  have shape := raw_shape location location index node next rfl permission
  obtain ⟨localRights,foreignRights⟩ := authority index next nextAt
  rw [tagEq] at localRights foreignRights
  have ancestry := ancestry_iff tree completion parentTag tag input target targetNode targetAt noIncoming index
  exact ⟨fun below => (local_shape _ _ _ shape).mp (localRights (ancestry.mpr below)),
    fun outside => (foreign_shape _ _ _ shape).mp (foreignRights (fun below => outside (ancestry.mp below)))⟩

/-- Old completed Bool authority survives the actual zero child and SIFA.
The new child is foreign to the OLD live Bool target, with its real parent. -/
theorem authority_row (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠input.index)
    (target : UniIndex) (targetLive : ∃ node,tree.nodes.get target=some node)
    (position : Nat) (oldValid : position<tree.locations.entries.size) (newValid : position<input.after.locations.entries.size)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags target tree.locations.entries[position].data) :
    S05CompletedAncestryReadMutable.Authority input.after (extend completion input.index input.parent)
      global.protectedTags target input.after.locations.entries[position].data := by
  have frame := leaf_frame tree global runtime parentTag tag input room tagBound
  have targetDifferent : target≠input.index := by
    intro same;obtain ⟨node,present⟩ := targetLive;rw [same,input.vacant] at present;cases present
  have shapes := location_shape input position oldValid newValid
  intro index node present
  by_cases child : index=input.index
  · subst index
    obtain ⟨actual,actualAt,tagEq,parentEq,children,permission,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
      input.stage input.parent .Read input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.stage_new
    have equal : node=actual := Option.some.inj (present.symm.trans actualAt)
    subst node
    have noBelow : ¬ Below (extend completion input.index input.parent) input.index target := by
      rw [old_below_iff completion input.index input.parent noIncoming target targetDifferent]
      exact not_below_vacant completion input.index target noIncoming targetDifferent
    have noPerm : input.after.locations.entries[position].data.perms.get input.index=none :=
      input.future_clean input.index input.clean position newValid
    constructor
    · intro impossible;exact False.elim (noBelow impossible)
    · intro _
      simp only [RawState,noPerm,Option.getD_none,OrdinaryBorrowAuthority.ForeignWrite,TreeNode.defaultLocationState]
      have frozen : actual.defaultInitialPermission=.Frozen := permission
      simp [frozen,LocationState.possible,Permission.isUnique]
  · obtain ⟨old,found,_⟩ := (frame.cases index node present).resolve_left child
    obtain ⟨next,nextAt,tagEq,permission⟩ := old_fields input index old found
    have equal : node=next := Option.some.inj (present.symm.trans nextAt)
    subst node
    have same := raw_shape tree.locations.entries[position].data input.after.locations.entries[position].data index old next shapes permission
    obtain ⟨localRights,foreignRights⟩ := authority index old found
    have ancestry := old_below_iff completion input.index input.parent noIncoming target targetDifferent index
    constructor
    · intro below
      rw [tagEq]
      exact (local_shape _ _ _ same).mpr (localRights (ancestry.mp below))
    · intro below
      rw [tagEq]
      exact (foreign_shape _ _ _ same).mpr (foreignRights (fun old => below (ancestry.mpr old)))

/-- The normal observer clause is transported directly, without converting
the current target's rights into the legacy Positive packet. -/
theorem normal_row (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (target : UniIndex) (targetNode : TreeNode) (present : tree.nodes.get target=some targetNode)
    (position : Nat) (oldValid : position<tree.locations.entries.size) (newValid : position<input.after.locations.entries.size)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree tree.locations.entries[position].data global.protectedTags target) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal input.after input.after.locations.entries[position].data global.protectedTags target) := by
  obtain ⟨forest⟩ := runtime.formed.forest tree.locations.entries[position].data global.protectedTags
  let observer := S03EmptySharedFrame.observerInput input
  have same : observer.after=input.after := congrArg (fun result => result.tree)
    ((observer.child 0 false).symm.trans (input.child 0 false))
  have observerValid : position<observer.after.locations.entries.size := by rw [same];exact newValid
  have result := (S04ZeroReadSharedPositive.normal_path tree parentTag tag observer global.protectedTags
    runtime.formed.fits position oldValid observerValid forest target targetNode present normal).1
  simpa only [same] using result

/-- Whole current Bool-window rights pass through one ACTUAL helper child. -/
theorem owned (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat)
    (noIncoming : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) → predecessor≠input.index)
    (target : UniIndex) (targetNode : TreeNode) (present : tree.nodes.get target=some targetNode)
    (lower upper : UInt64)
    (rights : GeneralRangeMapOrigins.OwnedOn (fun location =>
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags target) ∧
      S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags target location) lower upper tree.locations) :
    GeneralRangeMapOrigins.OwnedOn (fun location =>
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal input.after location global.protectedTags target) ∧
      S05CompletedAncestryReadMutable.Authority input.after (extend completion input.index input.parent) global.protectedTags target location)
      lower upper input.after.locations := by
  intro position newValid positive start stop
  have oldValid : position<tree.locations.entries.size := by
    rw [←rows_length input]
    exact newValid
  have range := row_range input position oldValid newValid
  rw [range] at start stop
  obtain ⟨⟨normal⟩,authority⟩ := rights position oldValid positive start stop
  exact ⟨normal_row tree global runtime parentTag tag input target targetNode present position oldValid newValid normal,
    authority_row tree global completion runtime parentTag tag input room tagBound noIncoming target ⟨targetNode,present⟩
      position oldValid newValid authority⟩

/-- The Bool release remains Write-only; this uses exact permission/accessed
shape, not an obsolete leaf assumption about the source helper parent. -/
theorem write_only (tree : BorrowTree) (parentTag tag : BorTag)
    (input : EmptyForestSharedPool.Input tree parentTag tag) (target : UniIndex)
    (before : Every (fun location => ∀ state,location.perms.get target=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Write) tree.locations) :
    Every (fun location => ∀ state,location.perms.get target=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Write) input.after.locations := by
  intro position newValid state stored accessed kind associated
  have oldValid : position<tree.locations.entries.size := by
    rw [←rows_length input]
    exact newValid
  have shape := location_shape input position oldValid newValid
  have same := congrArg (fun states => (⟨states⟩ : UniValMap StateShape).get target) shape
  rw [lookup_shape,lookup_shape,stored] at same
  cases old : tree.locations.entries[position].data.perms.get target with
  | none => simp only [old,Option.map_none,Option.map_some] at same;cases same
  | some previous =>
    have states : stateShape state=stateShape previous := by simpa only [old,Option.map_some,Option.some.injEq] using same
    have permission : state.permission=previous.permission := congrArg Prod.fst states
    have activity : state.accessed=previous.accessed := congrArg Prod.snd states
    exact before position oldValid previous old (activity.symm.trans accessed) kind (by rw [←permission];exact associated)

/-- Empty source ROOT release remains quiescent even after gaining its REAL
helper descendants. The target need not remain a leaf. -/
theorem quiet (tree : BorrowTree) (parentTag tag : BorTag)
    (input : EmptyForestSharedPool.Input tree parentTag tag) (source : UniIndex)
    (before : S04ReturnReleaseInactive.Quiescent tree source) :
    S04ReturnReleaseInactive.Quiescent input.after source := S03EmptySharedFrame.quiescent input source before


/-- Actual ROOT source release after gaining a helper child is unchanged.
The node may have children; hidden quiescence is the required scan invariant. -/
theorem quiet_release (tree : BorrowTree) (parentTag tag : BorTag)
    (input : EmptyForestSharedPool.Input tree parentTag tag) (sourceTag : BorTag) (source : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag sourceTag=some source) (present : tree.nodes.get source=some node)
    (hidden : node.isExposed=false) (before : S04ReturnReleaseInactive.Quiescent tree source)
    (protections : ProtectedTags) : input.after.releaseProtector sourceTag protections=⟨input.after,.Released⟩ := by
  obtain ⟨next,found,_,_,exposed⟩ := S03EmptySharedFrame.old_node input source node present
  exact S04ReturnReleaseInactive.release input.after sourceTag source next (S03EmptySharedFrame.tagged input sourceTag source tagged)
    found (exposed.trans hidden) (quiet tree parentTag tag input source before) protections

end
end DuplicatePrefix.CurrentCallEmptyEntryLenZeroTransport

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroTransport" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current empty helper transport dependency {dependency}"
