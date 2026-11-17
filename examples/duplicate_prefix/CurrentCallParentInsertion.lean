import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.S05WildcardProtectedRootCompletion

namespace DuplicatePrefix.CurrentCallParentInsertion
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open CurrentCallResourceNormalization S05ConcreteProtectedChildCompletion
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem old_edge (C : Completion) (child parent query predecessor : UniIndex)
    (different : query≠child)
    (edge : (extend C child parent).parents[query.toNat]?=some (some predecessor)) :
    C.parents[query.toNat]?=some (some predecessor) := by
  have bound : query.toNat<C.parents.size := by
    have extendedBound := (Array.getElem?_eq_some_iff.mp edge).1
    simp only [extend,Array.size_ofFn] at extendedBound
    by_cases small : query.toNat<C.parents.size
    · exact small
    · have missing : C.parents[query.toNat]?=none := Array.getElem?_eq_none (by omega)
      have unequal : query.toNat≠child.toNat := fun equal=>different (GeneralBorrowNodeUpdate.index_injective _ _ equal)
      simp [extend,extendedBound,unequal,missing] at edge
  exact (old_parent C child parent query different bound).symm.trans edge

/-- A real fresh allocator slot has no incoming edge in the old interpretation. -/
theorem no_incoming {tree : BorrowTree} {C : Completion} (model : ParentInterpretation tree C)
    (child : UniIndex) (vacant : tree.nodes.get child=none) :
    ∀ (query parent : UniIndex),C.parents[query.toNat]?=some (some parent) → parent≠child := by
  intro query parent edge same
  obtain ⟨node,present⟩ := (model.edgeLive query parent edge).2
  rw [same,vacant] at present
  cases present

private theorem transfer {before after : BorrowTree}
    (old : ∀ index node,before.nodes.get index=some node →
      ∃ next,after.nodes.get index=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed)
    {root target : UniIndex} (path : Path before root target) : Path after root target := by
  induction path with
  | refl node present => obtain ⟨next,found,_,_,_⟩ := old _ node present;exact .refl _ next found
  | step earlier node present edge ih =>
    obtain ⟨next,found,_,parent,_⟩ := old _ node present
    exact .step ih next found (parent.trans edge)

private theorem assemble (before after : BorrowTree) (C : Completion) (model : ParentInterpretation before C)
    (child parent : UniIndex) (vacant : before.nodes.get child=none)
    (size : after.nodes.data.size=max before.nodes.data.size (child.toNat+1))
    (parentLive : ∃ node,before.nodes.get parent=some node) (childLive : ∃ node,after.nodes.get child=some node)
    (old : ∀ index node,before.nodes.get index=some node →
      ∃ next,after.nodes.get index=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed)
    (casesNode : ∀ index node,after.nodes.get index=some node → index=child ∨
      ∃ old,before.nodes.get index=some old ∧ node.parent=old.parent)
    (childPhysical : ∀ node,after.nodes.get child=some node → ∀ predecessor,node.parent=some predecessor → predecessor=parent)
    (primaryLive : ∃ node,before.nodes.get allocationRoot=some node)
    (graph : GeneralBorrowStructuralHistoryState.GraphState after) (order : ParentTagOrder after)
    (virtual : ∀ (position : Nat) (root : UniIndex),after.roots[position]?=some root → ∀ origin,
      (extend C child parent).parents[root.toNat]?=some (some origin) →
      ∃ earlier originRoot rootNode originNode,earlier<position ∧ after.roots[earlier]?=some originRoot ∧
        after.nodes.get root=some rootNode ∧ after.nodes.get origin=some originNode ∧ originNode.isExposed=true ∧
        originNode.tag.value<rootNode.tag.value ∧ Path after originRoot origin) :
    ParentInterpretation after (extend C child parent) := by
  have different (index : UniIndex) (node : TreeNode) (present : before.nodes.get index=some node) : index≠child := by
    intro same;rw [same,vacant] at present;cases present
  have oldParent (index : UniIndex) (node : TreeNode) (present : before.nodes.get index=some node) :
      (extend C child parent).parents[index.toNat]?=C.parents[index.toNat]? := by
    apply old_parent _ _ _ _ (different index node present)
    rw [model.dimension]
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  refine ⟨graph,order,?_,?_,?_,?_,virtual⟩
  · simp only [extend,Array.size_ofFn,model.dimension,size]
  · intro index node present predecessor edge
    rcases casesNode index node present with same | ⟨previous,previousAt,parentEq⟩
    · subst index
      have sameParent := childPhysical node present predecessor edge
      subst predecessor
      exact child_edge C child parent
    · rw [oldParent index previous previousAt]
      exact model.physical index previous previousAt predecessor (parentEq.symm.trans edge)
  · intro query predecessor edge
    by_cases same : query=child
    · subst query
      have sameParent : predecessor=parent := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge C child parent)))
      subst predecessor
      obtain ⟨node,present⟩ := parentLive
      obtain ⟨next,nextAt,_,_,_⟩ := old parent node present
      exact ⟨childLive,⟨next,nextAt⟩⟩
    · obtain ⟨⟨queryNode,queryAt⟩,⟨parentNode,parentAt⟩⟩ := model.edgeLive query predecessor (old_edge C child parent query predecessor same edge)
      obtain ⟨nextQuery,nextQueryAt,_,_,_⟩ := old query queryNode queryAt
      obtain ⟨nextParent,nextParentAt,_,_,_⟩ := old predecessor parentNode parentAt
      exact ⟨⟨nextQuery,nextQueryAt⟩,⟨nextParent,nextParentAt⟩⟩
  · obtain ⟨primary,primaryAt⟩ := primaryLive
    exact (oldParent allocationRoot primary primaryAt).trans model.primaryNone

/-- Concrete insertion retains every chosen old origin and attaches the REAL
fresh child to its actual physical parent, without completing other roots. -/
theorem of_leaf (before after : BorrowTree) (C : Completion) (model : ParentInterpretation before C)
    (child parent : UniIndex) (frame : LeafFrame before after child parent)
    (primaryLive : ∃ node,before.nodes.get allocationRoot=some node)
    (graph : GeneralBorrowStructuralHistoryState.GraphState after) (order : ParentTagOrder after) :
    ParentInterpretation after (extend C child parent) := by
  apply assemble before after C model child parent frame.vacant frame.size frame.parentLive
    (by obtain ⟨node,present,_⟩ := frame.childLive;exact ⟨node,present⟩) frame.old frame.cases
    (by
      intro node present predecessor edge
      obtain ⟨actual,actualAt,parentEq⟩ := frame.childLive
      have equal : node=actual := Option.some.inj (present.symm.trans actualAt)
      exact Option.some.inj (edge.symm.trans (equal ▸ parentEq))) primaryLive graph order
  intro position root slot origin edge
  rw [frame.roots] at slot
  obtain ⟨node,present,_⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have different : root≠child := by intro same;rw [same,frame.vacant] at present;cases present
  have oldEdge := old_edge C child parent root origin different edge
  obtain ⟨earlier,originRoot,rootNode,originNode,bound,originSlot,rootAt,originAt,exposed,older,path⟩ := model.virtual position root slot origin oldEdge
  obtain ⟨nextRoot,nextRootAt,rootTag,_,_⟩ := frame.old root rootNode rootAt
  obtain ⟨nextOrigin,nextOriginAt,originTag,_,originExposed⟩ := frame.old origin originNode originAt
  exact ⟨earlier,originRoot,nextRoot,nextOrigin,bound,by simpa only [frame.roots] using originSlot,
    nextRootAt,nextOriginAt,originExposed.trans exposed,by simpa only [rootTag,originTag] using older,transfer frame.old path⟩

/-- Wildcard insertion retains old origins and chooses exactly ONE real older
exposed origin for the appended root. No full completion is required. -/
theorem of_root (before after : BorrowTree) (C : Completion) (model : ParentInterpretation before C)
    (child origin : UniIndex) (newTag : BorTag) (frame : S05WildcardProtectedRootCompletion.RootFrame before after child origin newTag)
    (primaryLive : ∃ node,before.nodes.get allocationRoot=some node)
    (graph : GeneralBorrowStructuralHistoryState.GraphState after) (order : ParentTagOrder after)
    (originNode : TreeNode) (originAt : before.nodes.get origin=some originNode)
    (exposed : originNode.isExposed=true) (older : originNode.tag.value<newTag.value)
    (originPosition : Nat) (originRoot : UniIndex) (originSlot : before.roots[originPosition]?=some originRoot)
    (originPath : Path before originRoot origin) :
    ParentInterpretation after (extend C child origin) := by
  apply assemble before after C model child origin frame.vacant frame.size frame.parentLive
    (by obtain ⟨node,present,_,_⟩ := frame.childLive;exact ⟨node,present⟩) frame.old frame.cases
    (by
      intro node present predecessor edge
      obtain ⟨actual,actualAt,_,parentless⟩ := frame.childLive
      have equal : node=actual := Option.some.inj (present.symm.trans actualAt)
      rw [equal,parentless] at edge
      cases edge) primaryLive graph order
  intro position root slot chosen edge
  by_cases oldPosition : position<before.roots.size
  · have oldSlot : before.roots[position]?=some root := by
      simpa only [frame.roots,Array.getElem?_push,show position≠before.roots.size by omega,↓reduceIte] using slot
    obtain ⟨node,present,_⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldSlot))
    have different : root≠child := by intro same;rw [same,frame.vacant] at present;cases present
    obtain ⟨earlier,oldRoot,rootNode,oldOrigin,bound,earlierSlot,rootAt,chosenAt,wasExposed,wasOlder,path⟩ :=
      model.virtual position root oldSlot chosen (old_edge C child origin root chosen different edge)
    obtain ⟨nextRoot,nextRootAt,rootTag,_,_⟩ := frame.old root rootNode rootAt
    obtain ⟨nextOrigin,nextOriginAt,originTag,_,originExposed⟩ := frame.old chosen oldOrigin chosenAt
    have earlierBound := (Array.getElem?_eq_some_iff.mp earlierSlot).1
    exact ⟨earlier,oldRoot,nextRoot,nextOrigin,bound,
      by simpa only [frame.roots,Array.getElem?_push,show earlier≠before.roots.size by omega,↓reduceIte] using earlierSlot,
      nextRootAt,nextOriginAt,originExposed.trans wasExposed,by simpa only [rootTag,originTag] using wasOlder,transfer frame.old path⟩
  · have bound := (Array.getElem?_eq_some_iff.mp slot).1
    rw [frame.roots,Array.size_push] at bound
    have positionEq : position=before.roots.size := by omega
    subst position
    have rootEq : root=child := by simpa only [frame.roots,Array.getElem?_push,ite_true,Option.some.injEq] using slot.symm
    subst root
    have originEq : chosen=origin := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge C child origin)))
    subst chosen
    obtain ⟨node,present,nodeTag,_⟩ := frame.childLive
    obtain ⟨next,nextAt,tagEq,_,exposedEq⟩ := frame.old origin originNode originAt
    have originBound := (Array.getElem?_eq_some_iff.mp originSlot).1
    exact ⟨originPosition,originRoot,node,next,originBound,
      by simpa only [frame.roots,Array.getElem?_push,show originPosition≠before.roots.size by omega,↓reduceIte] using originSlot,
      present,nextAt,exposedEq.trans exposed,by simpa only [tagEq,nodeTag] using older,transfer frame.old originPath⟩

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


private theorem inserted_size (nodes : UniValMap TreeNode) (child : UniIndex) (node : TreeNode) :
    (nodes.insert child node).data.size = max nodes.data.size (child.toNat+1) := by
  simp only [UniValMap.insert,Id.run,pure]
  split <;> simp only [Array.size_set,UniValMap.extendTo,Array.size_append,Array.size_replicate] <;> omega

private theorem frame_model (tree : BorrowTree) (global : GlobalState) (mapping : UniKeyMap BorTag)
    (child origin : UniIndex) (tag : BorTag) (offset len : UInt64)
    (vacant : tree.nodes.get child = none) (originLive : ∃ node, tree.nodes.get origin = some node)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts
      (GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
        GeneralBorrowFreshChild.inside offset len) global) :
    S05WildcardProtectedRootCompletion.RootFrame tree (GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len) child origin tag := by
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside offset len
  have newAt : model.nodes.get child = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) :=
    GeneralBorrowFreshLocation.get_same _ _ _
  refine ⟨vacant,inserted_size tree.nodes child _,rfl,originLive,⟨_,newAt,rfl,rfl⟩,?_,?_,physical_runtime model global runtime⟩
  · intro index node present
    have different : index ≠ child := by intro same; rw [same,vacant] at present; cases present
    exact ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ different).trans present,rfl,rfl,rfl⟩
  · intro index node present
    by_cases same : index = child
    · exact Or.inl same
    · exact Or.inr ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ same).symm.trans present,rfl⟩


private theorem old_default_of_stage (tree after : BorrowTree) (child parent : UniIndex)
    (parentNode : TreeNode) (newTag : BorTag) (vacant : tree.nodes.get child=none)
    (parentAt : tree.nodes.get parent=some parentNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (shape : treeShape after=treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping locations))
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query=some node) :
    ∃ next,after.nodeAt query=some next ∧ next.defaultInitialPermission=node.defaultInitialPermission := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) mapping locations
  have notChild : query≠child := by
    intro same
    change tree.nodes.get query=some node at present
    rw [same,vacant] at present
    cases present
  have staged : ∃ previous,stage.nodes.get query=some previous ∧ previous.defaultInitialPermission=node.defaultInitialPermission := by
    by_cases isParent : query=parent
    · subst query
      have same : node=parentNode := Option.some.inj (present.symm.trans parentAt)
      subst node
      refine ⟨updatedParent parentNode child,?_,rfl⟩
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
      exact GeneralBorrowFreshLocation.get_same _ _ _
    · refine ⟨node,?_,rfl⟩
      dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ isParent,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
      exact present
  obtain ⟨previous,previousAt,previousPermission⟩ := staged
  obtain ⟨next,nextAt,_,_,_,permission⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape query previous previousAt
  exact ⟨next,nextAt,permission.trans previousPermission⟩

/-- Actual protected concrete constructor metadata, without a completed parent map. -/
theorem concrete_frame (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag = true)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        LeafFrame tree actual.tree child parent ∧
        ∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission := by
  have output := GeneralBorrowProtectedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildMutable.index input
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : tree.nodes.get child = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have size : (GeneralBorrowFreshMetadataChildMutable.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildMutable.result input).nodes.size = _
      rw [data.size,atEnd]
      change tree.nodes.data.size+1 = _
      omega
    have frame := frame_of_stage tree (GeneralBorrowFreshMetadataChildMutable.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildMutable.mapping input)
      (GeneralBorrowFreshMetadataChildMutable.locations input) (GeneralBorrowFreshMetadataChildMutable.shape input)
      (GeneralBorrowFreshMetadataChildMutable.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := old_default_of_stage tree (GeneralBorrowFreshMetadataChildMutable.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildMutable.mapping input) (GeneralBorrowFreshMetadataChildMutable.locations input) (GeneralBorrowFreshMetadataChildMutable.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have size : (GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes.data.size = max tree.nodes.data.size (child.toNat+1) := by
      change (GeneralBorrowFreshMetadataChildMutableReuse.result input).nodes.size = _
      rw [data.size]
      change tree.nodes.data.size = _
      omega
    have frame := frame_of_stage tree (GeneralBorrowFreshMetadataChildMutableReuse.result input) global output.2.1
      child parent parentNode newTag vacant present (GeneralBorrowFreshMetadataChildMutableReuse.mapping input)
      (GeneralBorrowFreshMetadataChildMutableReuse.locations input) (GeneralBorrowFreshMetadataChildMutableReuse.shape input)
      (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) size data.roots
    refine ⟨child,data.freshLookup,frame,?_⟩
    intro query node oldAt
    obtain ⟨next,nextAt,tagEq,parentEq,exposureEq⟩ := frame.old query node oldAt
    obtain ⟨same,sameAt,permissionEq⟩ := old_default_of_stage tree (GeneralBorrowFreshMetadataChildMutableReuse.result input) child parent parentNode newTag
      vacant present (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) (GeneralBorrowFreshMetadataChildMutableReuse.locations input) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) query node oldAt
    have equal : next=same := Option.some.inj (nextAt.symm.trans sameAt)
    exact ⟨next,nextAt,tagEq,parentEq,exposureEq,equal.symm ▸ permissionEq⟩
/-- Actual protected wildcard constructor metadata, without a completed parent map. -/
theorem wildcard_frame (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        S05WildcardProtectedRootCompletion.RootFrame tree actual.tree child origin tag ∧
        ∀ query node,tree.nodeAt query=some node → ∃ next,actual.tree.nodeAt query=some next ∧
          next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
          next.defaultInitialPermission=node.defaultInitialPermission := by
  have output := GeneralBorrowWildcardConstructorRuntime.protected_mutable tree global runtime tag fresh room tagBound held
    offset len nonzero bounds
  obtain ⟨mapping,child,inserted,_,vacant,_,_,_⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping child inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  rw [actual] at output ⊢
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside offset len
  have frame := frame_model tree global mapping child origin tag offset len vacant ⟨originNode,originAt⟩ output.2.1
  have lookup : model.indexOfTag tag = some child := by
    exact output.2.1.formed.allocator.nodeTags child _ (GeneralBorrowFreshLocation.get_same tree.nodes child _)
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2.1,child,lookup,frame.roots,frame,?_⟩
  intro query node oldAt
  have different : query≠child := by
    intro same
    change tree.nodes.get query=some node at oldAt
    rw [same,vacant] at oldAt
    cases oldAt
  exact ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ different).trans oldAt,rfl,rfl,rfl,rfl⟩


end
end DuplicatePrefix.CurrentCallParentInsertion
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallParentInsertion" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current parent insertion dependency {dependency}"
