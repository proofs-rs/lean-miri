import duplicate_prefix.GeneralBorrowConcreteChildCausalOrder
import duplicate_prefix.GeneralBorrowParentTagConstructors
namespace DuplicatePrefix.GeneralBorrowWildcardChildCausalOrder
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
attribute [local irreducible] UniValMap.insert
/-- Arbitrary wildcard constructor policies and partitions preserve causal
order on every outcome. The new node is parentless; failed permission/range
checks do not add any other edge. -/
theorem inserted_order (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (order : ParentTagOrder tree) (newTag : BorTag) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (inserted : tree.tagMapping.insert newTag = .Inserted mapping index)
    (vacant : tree.nodes.get index = none)
    (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
    ParentTagOrder (tree.newChild offset .wildcard newTag inside outside held).tree := by
  unfold BorrowTree.newChild
  simp only [inserted,Id.run,bind,pure,Bool.false_eq_true,↓reduceIte]
  split
  · exact order
  · split
    · exact order
    · cases foreign : outside.strongestIdempotentForeignAccess held with
      | ImpossibleProtectedReservedIM => simp only [foreign];exact order
      | Access defaultSifa =>
        simp only [foreign,Id.run,bind,pure,←Array.forIn_toList]
        name_fresh_modify_scan
        let staged : BorrowTree := {tree with tagMapping:=mapping,nodes:=tree.nodes.insert index {tag:=newTag,parent:=none,defaultInitialPermission:=outside,defaultInitialSifa:=defaultSifa},roots:=tree.roots.push index}
        have stagedOrder : ParentTagOrder staged := by
          simpa only [staged,WildcardHitZeroConstructor.installed,WildcardHitZeroConstructor.rootNode] using
            GeneralBorrowParentTagConstructors.installed_root tree depth order mapping index vacant newTag outside defaultSifa
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
        dsimp only [staged] at maintained
        generalize folded : forIn inside.iterAll.toList (none,
          ({tree with tagMapping:=mapping,nodes:=tree.nodes.insert index {tag:=newTag,parent:=none,defaultInitialPermission:=outside,defaultInitialSifa:=defaultSifa},roots:=tree.roots.push index} : BorrowTree),defaultSifa) scan = final at maintained ⊢
        rcases final with ⟨returned,current,minimum⟩
        cases returned with
        | some result => exact maintained.2 result rfl
        | none => exact maintained.1

/-- The actual fresh allocator chooses append or reuse internally. No policy,
range or constructor-success assumptions enter this causal-order property. -/
theorem preserves (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (offset : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) :
    ParentTagOrder (tree.newChild offset .wildcard global.nextPointerTag inside outside held).tree := by
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime
    global.nextPointerTag (GeneralBorrowParentTagInvariant.fresh tree global runtime) room outside .None
  exact inserted_order tree (GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState) order
    global.nextPointerTag mapping index inserted vacant offset inside outside held
end DuplicatePrefix.GeneralBorrowWildcardChildCausalOrder
