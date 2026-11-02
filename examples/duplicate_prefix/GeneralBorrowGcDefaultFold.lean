import duplicate_prefix.GeneralBorrowGcChildFold
namespace DuplicatePrefix.GeneralBorrowGcDefaultFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem step_preserves (P : BorrowTree → Prop)
    (removed : ∀ tree index, P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.defaultLocationState = oldNode.defaultLocationState →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (seed : BorrowTree) (root : UniIndex) (live : Array BorTag) (parent child : UniIndex)
    (state : ChildState) (good : Good P state) : Good P (childScan seed root live parent child state).value := by
  rcases state with ⟨returned,current,kept⟩
  simp only [childScan,pure]
  split
  · have next := removed current child good.1
    split <;> exact ⟨next,by intro result same;cases same <;> exact next⟩
  · split
    · exact ⟨good.1,by intro result same;cases same⟩
    · rename_i replacement found
      have next := removed current child good.1
      split
      · exact ⟨next,by intro result same;cases same <;> exact next⟩
      · split
        · rename_i node present
          have changed := updated (source_remove_useless_node current child).1 replacement node
            {node with parent := some parent} present rfl next
          exact ⟨changed,by intro result same;cases same⟩
        · exact ⟨next,by intro result same;cases same <;> exact next⟩

/-- The exact production child fold preserves any predicate stable under the
actual deletion primitive and default-preserving node updates, including every
early error prefix. This is a data invariant, not operation-success input. -/
theorem fold_preserves (P : BorrowTree → Prop)
    (removed : ∀ tree index, P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.defaultLocationState = oldNode.defaultLocationState →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (seed : BorrowTree) (root : UniIndex) (live : Array BorTag) (parent : UniIndex)
    (items : Array UniIndex) (state : ChildState) (good : Good P state) :
    Good P (forIn (m := Id) items state (childScan seed root live parent)) := by
  rw [←Array.forIn_toList]
  apply GeneralBorrowLoop.list_invariant items.toList (childScan seed root live parent) (Good P)
  · intro child member current valid
    exact step_preserves P removed updated seed root live parent child current valid
  · exact good

end DuplicatePrefix.GeneralBorrowGcDefaultFold
