import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.GeneralBorrowWildcardConstructorSlot
import duplicate_prefix.GeneralBorrowParentTagInvariant
namespace DuplicatePrefix.GeneralBorrowConcreteChildCausalOrder
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local irreducible] UniValMap.insert

/-- Arbitrary policy and arbitrary inside partition: topology order survives
all constructor outcomes once the real allocator chooses a vacant slot and
the supplied new tag follows its parent. No successful operation is assumed. -/
theorem inserted_order (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (order : ParentTagOrder tree) (parentTag newTag : BorTag)
    (parent : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (inserted : tree.tagMapping.insert newTag = .Inserted mapping index)
    (vacant : tree.nodes.get index = none)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (freshOrder : parentNode.tag.value ≤ newTag.value)
    (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
    ParentTagOrder (tree.newChild offset (.concrete parentTag) newTag inside outside held).tree := by
  unfold BorrowTree.newChild
  simp only [inserted,Id.run,bind,pure,Bool.false_eq_true,↓reduceIte]
  change tree.tagMapping.get parentTag = some parent at tagged
  simp only [tagged]
  simp only [Option.map_some]
  split
  · exact order
  · split
    · exact order
    · cases foreign : outside.strongestIdempotentForeignAccess held with
      | ImpossibleProtectedReservedIM => simp only [foreign];exact order
      | Access defaultSifa =>
        simp only [foreign]
        have different : parent ≠ index := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant present
        change tree.nodes.get parent = some parentNode at present
        rw [GeneralBorrowFreshLocation.get_other tree.nodes index parent _ different,present]
        simp only [Id.run,bind,pure,←Array.forIn_toList]
        name_fresh_modify_scan
        let newNode : TreeNode := {tag:=newTag,parent:=some parent,defaultInitialPermission:=outside,defaultInitialSifa:=defaultSifa}
        let staged : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) with tagMapping:=mapping}
        have stagedOrder : ParentTagOrder staged :=
          GeneralBorrowFreshParentTagOrder.attached_order tree depth order index parent parentNode newNode vacant present rfl freshOrder
        let property := fun state : Option BorrowTree.ChildInsertResult × BorrowTree × IdempotentForeignAccess =>
          ParentTagOrder state.2.1 ∧ ∀ result,state.1=some result→ParentTagOrder result.tree
        have step : ∀segment∈inside.iterAll.toList,∀state,property state→property (scan segment state).value := by
          intro segment member state good
          rcases state with ⟨returned,current,minimum⟩
          dsimp only [property] at good ⊢
          simp only [scan]
          repeat' first
            | split
            | exact ⟨good.1,fun result equal => by cases equal;exact good.1⟩
            | exact ⟨good.1,by simp⟩
        have initial : property (none,staged,defaultSifa) := ⟨stagedOrder,by simp⟩
        have maintained := GeneralBorrowLoop.list_invariant inside.iterAll.toList scan property step (none,staged,defaultSifa) initial
        dsimp only [staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes] at maintained
        generalize folded : forIn inside.iterAll.toList (none,
          ({tree with tagMapping:=mapping,nodes:=(tree.nodes.insert index newNode).insert parent {parentNode with children:=parentNode.children.push index}} : BorrowTree),defaultSifa) scan = final at maintained ⊢
        rcases final with ⟨returned,current,minimum⟩
        cases returned with
        | some result => exact maintained.2 result rfl
        | none =>
          exact GeneralBorrowFreshParentTagOrder.transfer current _ (GeneralBorrowSifaView.preserves current parent minimum) maintained.1

/-- Every concrete policy, including zero-sized/empty inside partitions and
partial failure, preserves causal parent-tag order. Slot selection (append or
reuse), freshness, and parent/new-tag comparison are derived from the original
runtime. This is a topology invariant, not a constructor-success claim. -/
theorem preserves (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
    ParentTagOrder (tree.newChild offset (.concrete parentTag) global.nextPointerTag inside outside held).tree := by
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime
    global.nextPointerTag (GeneralBorrowParentTagInvariant.fresh tree global runtime) room outside .None
  exact inserted_order tree (GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState) order
    parentTag global.nextPointerTag parent parentNode mapping index inserted vacant tagged present
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
      (GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent parentNode present))))
    offset inside outside held
end DuplicatePrefix.GeneralBorrowConcreteChildCausalOrder
