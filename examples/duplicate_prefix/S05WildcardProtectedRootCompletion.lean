import duplicate_prefix.S05ConcreteProtectedChildCompletion
import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime

/-! Actual protected wildcard-root construction retains ONE chosen exposed
origin in the finite completion. The new physical node remains parentless;
only its completed virtual edge points to that same chosen origin. This is a
current sufficient model, not origin-family admission or history simulation. -/
namespace DuplicatePrefix.S05WildcardProtectedRootCompletion
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open S05ConcreteProtectedChildCompletion
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

structure RootFrame (before after : BorrowTree) (child origin : UniIndex) (newTag : BorTag) : Prop where
  vacant : before.nodes.get child = none
  size : after.nodes.data.size = max before.nodes.data.size (child.toNat+1)
  roots : after.roots = before.roots.push child
  parentLive : ∃ node, before.nodes.get origin = some node
  childLive : ∃ node, after.nodes.get child = some node ∧ node.tag = newTag ∧ node.parent = none
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
    (newTag : BorTag) (frame : RootFrame before after child parent newTag) (node : TreeNode)
    (present : before.nodes.get index = some node) : index ≠ child := by
  intro same
  rw [same,frame.vacant] at present
  cases present

private theorem path_transfer (before after : BorrowTree) (child parent : UniIndex)
    (newTag : BorTag) (frame : RootFrame before after child parent newTag) {first last : UniIndex}
    (path : Path before first last) : Path after first last := by
  induction path with
  | refl node present =>
    obtain ⟨next,found,_,_,_⟩ := frame.old _ node present
    exact .refl _ next found
  | @step predecessor target path node present edge induction =>
    obtain ⟨next,found,_,parentEq,_⟩ := frame.old target node present
    exact .step induction next found (parentEq.trans edge)

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


/-- Appending a parentless physical root adds exactly one virtual origin edge.
Its witness is the SAME supplied exposed origin and its existing root path. -/
theorem completes_of_root (before after : BorrowTree) (completion : Completion)
    (complete : Completes before completion) (child origin : UniIndex) (newTag : BorTag)
    (frame : RootFrame before after child origin newTag)
    (originNode : TreeNode) (originAt : before.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < newTag.value)
    (originPosition : Nat) (originRoot : UniIndex)
    (originSlot : before.roots[originPosition]? = some originRoot)
    (originPath : Path before originRoot origin) :
    Completes after (extend completion child origin) := by
  have oldParent : ∀ index node, before.nodes.get index = some node →
      (extend completion child origin).parents[index.toNat]? = completion.parents[index.toNat]? := by
    intro index node present
    apply old_parent _ _ _ _ (live_different _ _ _ _ _ _ frame node present)
    rw [complete.1]
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  have oldDepth : ∀ index node, before.nodes.get index = some node →
      (extend completion child origin).depths[index.toNat]? = completion.depths[index.toNat]? := by
    intro index node present
    apply old_depth _ _ _ _ (live_different _ _ _ _ _ _ frame node present)
    rw [complete.2.1]
    exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  have originBound := (Array.getElem?_eq_some_iff.mp originSlot).1
  have childOutside : child ∉ before.roots.toList := by
    intro member
    have entry := Array.mem_toList_iff.mp member
    obtain ⟨position,bound,same⟩ := Array.mem_iff_getElem.mp entry
    obtain ⟨node,present,_⟩ := complete.2.2.2.1 position child (by simp only [←same,Array.getElem?_eq_getElem bound])
    rw [frame.vacant] at present
    cases present
  have oldSlot : ∀ position root, after.roots[position]? = some root → position < before.roots.size →
      before.roots[position]? = some root := by
    intro position root slot bound
    simpa only [frame.roots,Array.getElem?_push,show position ≠ before.roots.size by omega,↓reduceIte] using slot
  have lastSlot : ∀ position root, after.roots[position]? = some root → ¬position < before.roots.size →
      position = before.roots.size ∧ root = child := by
    intro position root slot outside
    have bound := (Array.getElem?_eq_some_iff.mp slot).1
    rw [frame.roots,Array.size_push] at bound
    have same : position = before.roots.size := by omega
    subst position
    have sameRoot : root = child := by simpa only [frame.roots,Array.getElem?_push,ite_true,Option.some.injEq] using slot.symm
    exact ⟨rfl,sameRoot⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp [extend,complete.1,frame.size]
  · simp [extend,complete.2.1,frame.size]
  · rw [frame.roots,Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨complete.2.2.1,by simp,?_⟩
    intro old member query single
    have equal : query = child := by simpa only [List.mem_singleton] using single
    subst query
    intro same
    subst old
    exact childOutside member
  · intro position root slot
    by_cases bound : position < before.roots.size
    · obtain ⟨node,present,parentless⟩ := complete.2.2.2.1 position root (oldSlot position root slot bound)
      obtain ⟨next,found,_,parentEq,_⟩ := frame.old root node present
      exact ⟨next,found,parentEq.trans parentless⟩
    · obtain ⟨_,same⟩ := lastSlot position root slot bound
      subst root
      obtain ⟨node,present,_,parentless⟩ := frame.childLive
      exact ⟨node,present,parentless⟩
  · intro index node present
    obtain ⟨mapped,children,root⟩ := frame.physical index node present
    refine ⟨mapped,children,?_,root⟩
    intro parent edge
    rcases frame.cases index node present with same | ⟨old,found,parentEq⟩
    · subst index
      obtain ⟨childNode,childAt,_,parentless⟩ := frame.childLive
      have same : node = childNode := Option.some.inj (present.symm.trans childAt)
      subst node
      rw [parentless] at edge
      cases edge
    · rw [oldParent index old found]
      exact (complete.2.2.2.2.1 index old found).2.2.1 parent (parentEq.symm.trans edge)
  · intro position root slot
    by_cases bound : position < before.roots.size
    · have previousSlot := oldSlot position root slot bound
      have data := complete.2.2.2.2.2.1 position root previousSlot
      obtain ⟨rootNode,rootAt,_⟩ := complete.2.2.2.1 position root previousSlot
      rw [oldParent root rootNode rootAt]
      by_cases zero : position = 0
      · simpa only [zero,↓reduceIte] using data
      · simp only [zero,↓reduceIte] at data ⊢
        obtain ⟨earlier,oldRoot,oldOrigin,rootNode,oldOriginNode,oldBound,earlierSlot,rootAt,oldOriginAt,oldExposed,ordered,path,edge⟩ := data
        obtain ⟨nextRoot,nextRootAt,rootTag,_,_⟩ := frame.old root rootNode rootAt
        obtain ⟨nextOrigin,nextOriginAt,originTag,_,originExposed⟩ := frame.old oldOrigin oldOriginNode oldOriginAt
        have earlierBound := (Array.getElem?_eq_some_iff.mp earlierSlot).1
        have afterSlot : after.roots[earlier]? = some oldRoot := by
          simpa only [frame.roots,Array.getElem?_push,show earlier ≠ before.roots.size by omega,↓reduceIte] using earlierSlot
        exact ⟨earlier,oldRoot,oldOrigin,nextRoot,nextOrigin,oldBound,afterSlot,nextRootAt,nextOriginAt,
          originExposed.trans oldExposed,by simpa only [rootTag,originTag] using ordered,
          path_transfer _ _ _ _ _ frame path,edge⟩
    · obtain ⟨samePosition,sameRoot⟩ := lastSlot position root slot bound
      subst position
      subst root
      simp only [show before.roots.size ≠ 0 by omega,↓reduceIte]
      obtain ⟨childNode,childAt,childTag,_⟩ := frame.childLive
      obtain ⟨nextOrigin,nextOriginAt,originTag,_,originExposed⟩ := frame.old origin originNode originAt
      have afterSlot : after.roots[originPosition]? = some originRoot := by
        simpa only [frame.roots,Array.getElem?_push,show originPosition ≠ before.roots.size by omega,↓reduceIte] using originSlot
      exact ⟨originPosition,originRoot,origin,childNode,nextOrigin,originBound,afterSlot,childAt,nextOriginAt,
        originExposed.trans exposed,by simpa only [originTag,childTag] using older,
        path_transfer _ _ _ _ _ frame originPath,child_edge completion child origin⟩
  · intro target predecessor edge
    by_cases same : target = child
    · subst target
      have sameParent : predecessor = origin := Option.some.inj (Option.some.inj (edge.symm.trans (child_edge completion child origin)))
      subst predecessor
      obtain ⟨next,nextAt,_,_,_⟩ := frame.old origin originNode originAt
      refine ⟨frame.childLive.imp (fun _ data => data.1),⟨next,nextAt⟩,?_⟩
      rw [oldDepth origin originNode originAt]
      simp [extend,show child.toNat < max completion.depths.size (child.toNat+1) by omega]
    · have bound : target.toNat < completion.parents.size := by
        have extendedBound := (Array.getElem?_eq_some_iff.mp edge).1
        simp only [extend,Array.size_ofFn] at extendedBound
        by_cases small : target.toNat < completion.parents.size
        · exact small
        have missing : completion.parents[target.toNat]? = none := Array.getElem?_eq_none (by omega)
        have unequal : target.toNat ≠ child.toNat := fun equal => same (GeneralBorrowNodeUpdate.index_injective _ _ equal)
        simp [extend,extendedBound,unequal,missing] at edge
      rw [old_parent completion child origin target same bound] at edge
      obtain ⟨⟨targetNode,targetAt⟩,⟨predecessorNode,predecessorAt⟩,smaller⟩ := complete.2.2.2.2.2.2 target predecessor edge
      obtain ⟨nextTarget,nextTargetAt,_,_,_⟩ := frame.old target targetNode targetAt
      obtain ⟨nextPredecessor,nextPredecessorAt,_,_,_⟩ := frame.old predecessor predecessorNode predecessorAt
      exact ⟨⟨nextTarget,nextTargetAt⟩,⟨nextPredecessor,nextPredecessorAt⟩,
        by simpa only [oldDepth target targetNode targetAt,oldDepth predecessor predecessorNode predecessorAt] using smaller⟩

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
    RootFrame tree (GeneralBorrowPositiveWildcardConstructor.result tree mapping child tag (.ReservedFrz false) .None
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

/-- Actual protected wildcard construction preserves the chosen exposed origin
as the new root's unique completed parent. Fresh tag order is a separate current
counter fact, normally derived before Strong registration. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < tag.value)
    (originPosition : Nat) (originRoot : UniIndex)
    (originSlot : tree.roots[originPosition]? = some originRoot) (originPath : Path tree originRoot origin)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag tag = some child ∧ actual.tree.roots = tree.roots.push child ∧
        RootFrame tree actual.tree child origin tag ∧ Completes actual.tree (extend completion child origin) := by
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
  exact ⟨output.1,output.2.1,output.2.2.1,output.2.2.2.1,child,lookup,frame.roots,frame,
    completes_of_root tree model completion complete child origin tag frame originNode originAt exposed older
      originPosition originRoot originSlot originPath⟩

end DuplicatePrefix.S05WildcardProtectedRootCompletion

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardProtectedRootCompletion." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard protected completion dependency {dependency}"
