import duplicate_prefix.CurrentCallEmptyEntryBool
import duplicate_prefix.CurrentCallEmptyEntryLenZeroTransport
import duplicate_prefix.CurrentCallEmptyEntryLenZeroFactory

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroHoldings
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CurrentCallEmptyEntryBool S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem node_fields {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index=some node) (different : index≠input.parent) :
    ∃ next,input.after.nodeAt index=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧
      next.children=node.children ∧ next.isExposed=node.isExposed := by
  have staged : input.stage.nodeAt index=some node := by
    have actual := S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
    change (GeneralBorrowFreshNode.attachedNodes tree.nodes input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).get index=some node
    simpa only [S04ZeroReadSharedAttach.liftNode,different,ite_false] using actual
  obtain ⟨next,found,tagEq,parentEq,children,_,exposure⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .Read index node staged
  exact ⟨next,found,tagEq,parentEq,children,exposure⟩

/-- Both ACTUAL helpers transport the same Bool holdings and completion. -/
theorem transport (tree : BorrowTree) (global : GlobalState) (boolTag qTag : BorTag)
    (provenance : Provenance) (offset : UInt64)
    (holdings : BoolHoldings tree global boolTag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag1 tag2 : BorTag) (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (room1 : tree.nodes.size+1≤4294967295) (room2 : first.after.nodes.size+1≤4294967295)
    (bound1 : tag1.value.toNat<global.nextPointerTag.value.toNat) (bound2 : tag2.value.toNat<global.nextPointerTag.value.toNat)
    (different1 : holdings.child≠first.parent) (different2 : holdings.child≠second.parent)
    (geometry : Completes second.after (extend (extend holdings.completion first.index first.parent) second.index second.parent) ∨
      Nonempty (OrphanWriteFactory second.after (extend (extend holdings.completion first.index first.parent) second.index second.parent)
        global.protectedTags holdings.child qTag)) :
    Nonempty (BoolHoldings second.after global boolTag qTag provenance offset) := by
  let C1 := extend holdings.completion first.index first.parent
  have runtime1 := S03EmptySharedRuntime.construct tree global runtime parentTag tag1 first room1 bound1
  obtain ⟨middle,middleAt,middleTag,middleParent,middleChildren,middleHidden⟩ :=
    node_fields first holdings.child holdings.node holdings.present different1
  obtain ⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩ :=
    node_fields second holdings.child middle middleAt different2
  obtain ⟨middleParentNode,middleParentAt,middleParentTag,_,middleParentExposure⟩ :=
    S03EmptySharedFrame.old_node first holdings.parent holdings.parentNode holdings.parentAt
  obtain ⟨parent,parentAt,parentTagEq,_,parentExposure⟩ :=
    S03EmptySharedFrame.old_node second holdings.parent middleParentNode middleParentAt
  have live1 := CurrentCallEmptyEntryLenZeroTransport.parent_live tree holdings.completion parentTag tag1 first holdings.parentLive
  have noIncoming1 := CurrentCallEmptyEntryLenZeroTransport.no_incoming tree holdings.completion parentTag tag1 first holdings.parentLive
  have noIncoming2 := CurrentCallEmptyEntryLenZeroTransport.no_incoming first.after C1 tag1 tag2 second live1
  have differentIndex1 : holdings.child≠first.index := by
    intro same
    have present := holdings.present
    change tree.nodes.get holdings.child=some holdings.node at present
    rw [same,first.vacant] at present
    cases present
  have differentIndex2 : holdings.child≠second.index := by
    intro same
    change first.after.nodes.get holdings.child=some middle at middleAt
    rw [same,second.vacant] at middleAt
    cases middleAt
  have bound : holdings.child.toNat<holdings.completion.parents.size := (Array.getElem?_eq_some_iff.mp holdings.edge).1
  have edge1 : C1.parents[holdings.child.toNat]?=some (some holdings.parent) :=
    (old_parent holdings.completion first.index first.parent holdings.child differentIndex1 bound).trans holdings.edge
  have boundMiddle : holdings.child.toNat<C1.parents.size := (Array.getElem?_eq_some_iff.mp edge1).1
  have edge2 := (old_parent C1 second.index second.parent holdings.child differentIndex2 boundMiddle).trans edge1
  have owned1 := CurrentCallEmptyEntryLenZeroTransport.owned tree global holdings.completion runtime parentTag tag1 first room1 bound1
    noIncoming1 holdings.child holdings.node holdings.present offset (offset+1) holdings.owned
  refine ⟨⟨extend C1 second.index second.parent,holdings.child,node,
    S03EmptySharedFrame.tagged second boolTag holdings.child (S03EmptySharedFrame.tagged first boolTag holdings.child holdings.mapped),nodeAt,
    nodeTag.trans (middleTag.trans holdings.nodeTag),nodeChildren.trans (middleChildren.trans holdings.leaf),
    nodeHidden.trans (middleHidden.trans holdings.hidden),
    S03EmptySharedFrame.activity second holdings.child .Write offset (offset+1)
      (S03EmptySharedFrame.activity first holdings.child .Write offset (offset+1) holdings.active),
    CurrentCallEmptyEntryLenZeroTransport.owned first.after global C1 runtime1 tag1 tag2 second room2 bound2
      noIncoming2 holdings.child middle middleAt offset (offset+1) owned1,
    CurrentCallEmptyEntryLenZeroTransport.write_only first.after tag1 tag2 second holdings.child
      (CurrentCallEmptyEntryLenZeroTransport.write_only tree parentTag tag1 first holdings.child holdings.writeOnly),
    holdings.parent,parent,parentAt,edge2,?_,
    CurrentCallEmptyEntryLenZeroTransport.parent_live first.after C1 tag1 tag2 second live1,?_,geometry,?_⟩⟩
  · cases provenance with
    | concrete allocation oldTag => exact holdings.parentProvenance.trans (parentTagEq.trans middleParentTag).symm
    | wildcard => exact parentExposure.trans (middleParentExposure.trans holdings.parentProvenance)
  · rcases holdings.physicalOrComplete with physical | complete
    · exact Or.inl (nodeParent.trans (middleParent.trans physical))
    · exact Or.inr (CurrentCallEmptyEntryLenZeroTransport.completes first.after global C1 runtime1
        (CurrentCallEmptyEntryLenZeroTransport.completes tree global holdings.completion runtime complete parentTag tag1 first room1 bound1)
        tag1 tag2 second room2 bound2)

  · intro wildcard
    exact CurrentCallEmptyEntryLenZeroTransport.completes first.after global C1 runtime1
      (CurrentCallEmptyEntryLenZeroTransport.completes tree global holdings.completion runtime
        (holdings.wildcardComplete wildcard) parentTag tag1 first room1 bound1) tag1 tag2 second room2 bound2

/-- The actual two-helper consumer derives its own complete-or-orphan geometry. -/
theorem two_helpers (tree : BorrowTree) (global : GlobalState) (boolTag qTag : BorTag)
    (provenance : Provenance) (offset : UInt64)
    (holdings : BoolHoldings tree global boolTag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag1 tag2 : BorTag) (first : EmptyForestSharedPool.Input tree qTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2) (secondParent : second.parent=first.index)
    (room1 : tree.nodes.size+1≤4294967295) (room2 : first.after.nodes.size+1≤4294967295)
    (bound1 : tag1.value.toNat<global.nextPointerTag.value.toNat) (bound2 : tag2.value.toNat<global.nextPointerTag.value.toNat)
    (differentTags : boolTag≠qTag) (qLeaf : CurrentCallEmptyEntrySourceData.Leaf tree qTag) :
    Nonempty (BoolHoldings second.after global boolTag qTag provenance offset) := by
  have different1 : holdings.child≠first.parent := by
    obtain ⟨qIndex,qNode,qMapped,qAt,qNodeTag,_,_,_⟩ := qLeaf
    have parentIndex : first.parent=qIndex := Option.some.inj (first.tagged.symm.trans qMapped)
    intro same
    have atQ : tree.nodeAt qIndex=some holdings.node := (same.trans parentIndex) ▸ holdings.present
    have nodeEq : holdings.node=qNode := Option.some.inj (atQ.symm.trans qAt)
    exact differentTags (holdings.nodeTag.symm.trans (nodeEq ▸ qNodeTag))
  have different2 : holdings.child≠second.parent := by
    rw [secondParent]
    intro same
    have present := holdings.present
    change tree.nodes.get holdings.child=some holdings.node at present
    rw [same,first.vacant] at present
    cases present
  have runtime1 := S03EmptySharedRuntime.construct tree global runtime qTag tag1 first room1 bound1
  have runtime2 := S03EmptySharedRuntime.construct first.after global runtime1 tag1 tag2 second room2 bound2
  have live1 := CurrentCallEmptyEntryLenZeroTransport.parent_live tree holdings.completion qTag tag1 first holdings.parentLive
  have noIncoming1 := CurrentCallEmptyEntryLenZeroTransport.no_incoming tree holdings.completion qTag tag1 first holdings.parentLive
  have noIncoming2 := CurrentCallEmptyEntryLenZeroTransport.no_incoming first.after (extend holdings.completion first.index first.parent) tag1 tag2 second live1
  apply transport tree global boolTag qTag provenance offset holdings runtime qTag tag1 tag2 first second room1 room2 bound1 bound2 different1 different2
  rcases holdings.geometry with complete | existing
  · exact .inl (CurrentCallEmptyEntryLenZeroTransport.completes first.after global _ runtime1
      (CurrentCallEmptyEntryLenZeroTransport.completes tree global _ runtime complete qTag tag1 first room1 bound1)
      tag1 tag2 second room2 bound2)
  · right
    obtain ⟨factory⟩ := existing
    have firstParent : first.parent=factory.orphan := Option.some.inj (first.tagged.symm.trans factory.orphanMapped)
    obtain ⟨qIndex,qNode,qMapped,qAt,_,leaf,hidden,_⟩ := qLeaf
    have qIndexEq : qIndex=factory.orphan := Option.some.inj (qMapped.symm.trans factory.orphanMapped)
    subst qIndex
    obtain ⟨actual,actualAt,parentless⟩ := runtime.formed.rootNodes factory.orphan
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? factory.orphanSlot))
    have actualEq : actual=qNode := Option.some.inj (actualAt.symm.trans qAt)
    obtain ⟨middle,middleAt,_,_,_⟩ := S03EmptySharedFrame.old_node first holdings.child holdings.node holdings.present
    exact CurrentCallEmptyEntryLenZeroFactory.two_helpers factory first second firstParent secondParent qNode qAt hidden
      (actualEq ▸ parentless) leaf holdings.node middle holdings.present middleAt noIncoming1 noIncoming2 global runtime2 rfl

/-- Advancing the real global counter retains the SAME held table. -/
theorem global (tree : BorrowTree) (before after : GlobalState) (boolTag qTag : BorTag)
    (provenance : Provenance) (offset : UInt64)
    (holdings : BoolHoldings tree before boolTag qTag provenance offset)
    (same : after.protectedTags=before.protectedTags) :
    Nonempty (BoolHoldings tree after boolTag qTag provenance offset) := by
  refine ⟨{holdings with owned:=?_,geometry:=?_}⟩
  · simpa only [same] using holdings.owned
  · simpa only [same] using holdings.geometry

end
end DuplicatePrefix.CurrentCallEmptyEntryLenZeroHoldings

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroHoldings" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty holdings transport dependency {dependency}"
