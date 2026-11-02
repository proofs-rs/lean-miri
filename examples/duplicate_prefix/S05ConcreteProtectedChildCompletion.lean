import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.GeneralBorrowProtectedConstructorRuntime
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime

/-! Bounded concrete-provenance constructor factor. The input tree is the tree
AFTER the parent's associated Read. This module does not establish that Read,
ordinary admission, full Joint preservation, or wildcard max=none adequacy.
The finite extension preserves old live completed ancestry and appends
child→parent at the actual allocator slot. The final theorem derives full
`Completes` for the actual constructor result in both allocator branches. -/
namespace DuplicatePrefix.S05ConcreteProtectedChildCompletion
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A sparse vacant slot may be reused. Entries elsewhere retain their exact
old parent/depth data; a fresh end slot grows both finite arrays. -/
def extend (completion : Completion) (child parent : UniIndex) : Completion :=
  ⟨Array.ofFn (n := max completion.parents.size (child.toNat+1)) fun index =>
      if index.val = child.toNat then some parent else (completion.parents[index.val]?).getD none,
    Array.ofFn (n := max completion.depths.size (child.toNat+1)) fun index =>
      if index.val = child.toNat then (completion.depths[parent.toNat]?).getD 0 + 1
      else (completion.depths[index.val]?).getD 0⟩

theorem child_edge (completion : Completion) (child parent : UniIndex) :
    (extend completion child parent).parents[child.toNat]? = some (some parent) := by
  simp [extend,show child.toNat < max completion.parents.size (child.toNat+1) by omega]

theorem old_parent (completion : Completion) (child parent query : UniIndex)
    (different : query ≠ child) (bound : query.toNat < completion.parents.size) :
    (extend completion child parent).parents[query.toNat]? = completion.parents[query.toNat]? := by
  have unequal : query.toNat ≠ child.toNat := by
    intro equal
    exact different (by cases query; cases child; simp only [UniIndex.toNat] at equal; congr; exact UInt32.toNat_inj.mp equal)
  simp [extend,show query.toNat < max completion.parents.size (child.toNat+1) by omega,
    unequal,Array.getElem?_eq_getElem bound]

theorem old_depth (completion : Completion) (child parent query : UniIndex)
    (different : query ≠ child) (bound : query.toNat < completion.depths.size) :
    (extend completion child parent).depths[query.toNat]? = completion.depths[query.toNat]? := by
  have unequal : query.toNat ≠ child.toNat := by
    intro equal
    exact different (by cases query; cases child; simp only [UniIndex.toNat] at equal; congr; exact UInt32.toNat_inj.mp equal)
  simp [extend,show query.toNat < max completion.depths.size (child.toNat+1) by omega,
    unequal,Array.getElem?_eq_getElem bound]

/-- No old completed edge can start at a physically vacant slot: `Completes`
requires both endpoints live. Therefore all old paths survive sparse reuse. -/
theorem old_ancestry (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) (child parent : UniIndex)
    (vacant : tree.nodes.get child = none) {ancestor target : UniIndex}
    (path : Below completion ancestor target) :
    Below (extend completion child parent) ancestor target := by
  induction path with
  | refl => exact .refl _
  | @step predecessor target edge path induction =>
    have endpoints := complete.2.2.2.2.2.2 target predecessor edge
    have different : target ≠ child := by
      intro same
      obtain ⟨node,present⟩ := endpoints.1
      rw [same,vacant] at present
      cases present
    have bound := (Array.getElem?_eq_some_iff.mp edge).1
    exact .step ((old_parent completion child parent target different bound).trans edge) induction

theorem ancestors_of_child (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) (child parent : UniIndex)
    (vacant : tree.nodes.get child = none) {ancestor : UniIndex}
    (path : Below completion ancestor parent) :
    Below (extend completion child parent) ancestor child :=
  .step (child_edge completion child parent) (old_ancestry tree completion complete child parent vacant path)

open GeneralBorrowExposedNonleafPrimaryPath

/-- Pure graph facts to be discharged from the actual allocator construction. -/
structure LeafFrame (before after : BorrowTree) (child parent : UniIndex) : Prop where
  vacant : before.nodes.get child = none
  size : after.nodes.data.size = max before.nodes.data.size (child.toNat+1)
  roots : after.roots = before.roots
  parentLive : ∃ node, before.nodes.get parent = some node
  childLive : ∃ node, after.nodes.get child = some node ∧ node.parent = some parent
  old : ∀ index node, before.nodes.get index = some node →
    ∃ next, after.nodes.get index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed
  cases : ∀ index node, after.nodes.get index = some node → index = child ∨
    ∃ old, before.nodes.get index = some old ∧ node.parent = old.parent
  physical : ∀ index node, after.nodes.get index = some node →
    after.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, after.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (node.parent = none ↔ index ∈ after.roots.toList)

private theorem live_different (before after : BorrowTree) (child parent index : UniIndex)
    (frame : LeafFrame before after child parent) (node : TreeNode)
    (present : before.nodes.get index = some node) : index ≠ child := by
  intro same
  rw [same,frame.vacant] at present
  cases present

private theorem path_transfer (before after : BorrowTree) (child parent : UniIndex)
    (frame : LeafFrame before after child parent) {first last : UniIndex}
    (path : Path before first last) : Path after first last := by
  induction path with
  | refl node present =>
    obtain ⟨next,found,_,_,_⟩ := frame.old _ node present
    exact .refl _ next found
  | @step predecessor target path node present edge induction =>
    obtain ⟨next,found,_,parentEq,_⟩ := frame.old target node present
    exact .step induction next found (parentEq.trans edge)

/-- Full completed graph preservation, including unchanged virtual origins.
This theorem's leaf-frame hypotheses are structural facts, not permission or
successful-access assumptions. -/
theorem completes_of_leaf (before after : BorrowTree) (completion : Completion)
    (complete : Completes before completion) (child parent : UniIndex)
    (frame : LeafFrame before after child parent) :
    Completes after (extend completion child parent) := by
  have parentBound : parent.toNat < before.nodes.data.size := by
    obtain ⟨node,present⟩ := frame.parentLive
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  have parentDifferent : parent ≠ child := by
    obtain ⟨node,present⟩ := frame.parentLive
    exact live_different _ _ _ _ _ frame node present
  have oldParent : ∀ index node, before.nodes.get index = some node →
      (extend completion child parent).parents[index.toNat]? = completion.parents[index.toNat]? := by
    intro index node present
    apply old_parent _ _ _ _ (live_different _ _ _ _ _ frame node present)
    rw [complete.1]
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  have oldDepth : ∀ index node, before.nodes.get index = some node →
      (extend completion child parent).depths[index.toNat]? = completion.depths[index.toNat]? := by
    intro index node present
    apply old_depth _ _ _ _ (live_different _ _ _ _ _ frame node present)
    rw [complete.2.1]
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp [extend,complete.1,frame.size]
  · simp [extend,complete.2.1,frame.size]
  · simpa only [frame.roots] using complete.2.2.1
  · intro position root slot
    rw [frame.roots] at slot
    obtain ⟨node,present,parentless⟩ := complete.2.2.2.1 position root slot
    obtain ⟨next,found,_,parentEq,_⟩ := frame.old root node present
    exact ⟨next,found,parentEq.trans parentless⟩
  · intro index node present
    obtain ⟨mapped,children,root⟩ := frame.physical index node present
    refine ⟨mapped,children,?_,root⟩
    intro ancestor edge
    rcases frame.cases index node present with same | ⟨old,found,parentEq⟩
    · subst index
      obtain ⟨childNode,childAt,parentAt⟩ := frame.childLive
      have same : node = childNode := Option.some.inj (present.symm.trans childAt)
      subst node
      have sameParent : ancestor = parent := Option.some.inj (edge.symm.trans parentAt)
      subst ancestor
      exact child_edge completion child parent
    · rw [oldParent index old found]
      exact (complete.2.2.2.2.1 index old found).2.2.1 ancestor (parentEq.symm.trans edge)
  · intro position root slot
    rw [frame.roots] at slot
    have data := complete.2.2.2.2.2.1 position root slot
    obtain ⟨rootNode,rootAt,_⟩ := complete.2.2.2.1 position root slot
    rw [oldParent root rootNode rootAt]
    by_cases zero : position = 0
    · simpa only [zero,↓reduceIte] using data
    · simp only [zero,↓reduceIte] at data ⊢
      obtain ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootAt,originAt,exposed,ordered,path,edge⟩ := data
      obtain ⟨nextRoot,nextRootAt,rootTag,_,_⟩ := frame.old root rootNode rootAt
      obtain ⟨nextOrigin,nextOriginAt,originTag,_,originExposed⟩ := frame.old origin originNode originAt
      exact ⟨earlier,originRoot,origin,nextRoot,nextOrigin,older,by simpa only [frame.roots] using earlierSlot,
        nextRootAt,nextOriginAt,originExposed.trans exposed,by simpa only [rootTag,originTag] using ordered,
        path_transfer _ _ _ _ frame path,edge⟩
  · intro target predecessor edge
    by_cases same : target = child
    · subst target
      have sameParent : predecessor = parent := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge completion child parent)))
      subst predecessor
      obtain ⟨node,present⟩ := frame.parentLive
      obtain ⟨next,nextAt,_,_,_⟩ := frame.old parent node present
      refine ⟨frame.childLive.imp (fun _ data => data.1),⟨next,nextAt⟩,?_⟩
      rw [oldDepth parent node present]
      simp [extend,show child.toNat < max completion.depths.size (child.toNat+1) by omega]
    · have bound : target.toNat < completion.parents.size := by
        have extendedBound := (Array.getElem?_eq_some_iff.mp edge).1
        simp only [extend,Array.size_ofFn] at extendedBound
        by_cases small : target.toNat < completion.parents.size
        · exact small
        have oldMissing : completion.parents[target.toNat]? = none := Array.getElem?_eq_none (by omega)
        have unequal : target.toNat ≠ child.toNat := fun equal => same (GeneralBorrowNodeUpdate.index_injective _ _ equal)
        simp [extend,extendedBound,unequal,oldMissing] at edge
      rw [old_parent completion child parent target same bound] at edge
      obtain ⟨⟨targetNode,targetAt⟩,⟨predecessorNode,predecessorAt⟩,smaller⟩ := complete.2.2.2.2.2.2 target predecessor edge
      obtain ⟨nextTarget,nextTargetAt,_,_,_⟩ := frame.old target targetNode targetAt
      obtain ⟨nextPredecessor,nextPredecessorAt,_,_,_⟩ := frame.old predecessor predecessorNode predecessorAt
      exact ⟨⟨nextTarget,nextTargetAt⟩,⟨nextPredecessor,nextPredecessorAt⟩,
        by simpa only [oldDepth target targetNode targetAt,oldDepth predecessor predecessorNode predecessorAt] using smaller⟩

open GeneralBorrowProjection

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

/-- Actual concrete protected child construction extends the SAME completed
origin assignment, including sparse vacant-slot reuse. The input runtime/tree
is the post-parent-Read state; no callback Positive or future rights are inputs. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion)
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
        LeafFrame tree actual.tree child parent ∧ Completes actual.tree (extend completion child parent) ∧
        (∀ ancestor, Below completion ancestor parent → Below (extend completion child parent) ancestor child) := by
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
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩
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
    exact ⟨child,data.freshLookup,frame,completes_of_leaf tree _ completion complete child parent frame,
      fun ancestor path => ancestors_of_child tree completion complete child parent vacant path⟩

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

/-- No new ancestor is invented for any old live grant. -/
theorem old_ancestry_iff (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) (child parent : UniIndex)
    (vacant : tree.nodes.get child = none) {ancestor target : UniIndex}
    (targetLive : ∃ node, tree.nodes.get target = some node) :
    Below (extend completion child parent) ancestor target ↔ Below completion ancestor target := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _
    | @step predecessor target edge path induction =>
      obtain ⟨node,present⟩ := targetLive
      have different : target ≠ child := by intro same; rw [same,vacant] at present; cases present
      have original := old_edge completion child parent target predecessor different edge
      have predecessorLive := (complete.2.2.2.2.2.2 target predecessor original).2.1
      exact .step original (induction predecessorLive)
  · exact old_ancestry tree completion complete child parent vacant

/-- The exact new ancestry is the old parent's ancestry plus the fresh child. -/
theorem child_ancestry_iff (tree : BorrowTree) (completion : Completion)
    (complete : Completes tree completion) (child parent : UniIndex)
    (vacant : tree.nodes.get child = none) (parentLive : ∃ node, tree.nodes.get parent = some node)
    (ancestor : UniIndex) :
    Below (extend completion child parent) ancestor child ↔ ancestor = child ∨ Below completion ancestor parent := by
  constructor
  · intro path
    cases path with
    | refl => exact Or.inl rfl
    | @step predecessor target edge earlier =>
      have same : predecessor = parent := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge completion child parent)))
      subst predecessor
      exact Or.inr ((old_ancestry_iff tree completion complete child parent vacant parentLive).mp earlier)
  · rintro (same | path)
    · subst ancestor; exact .refl child
    · exact ancestors_of_child tree completion complete child parent vacant path


end DuplicatePrefix.S05ConcreteProtectedChildCompletion

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ConcreteProtectedChildCompletion." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete protected completion dependency {dependency}"
