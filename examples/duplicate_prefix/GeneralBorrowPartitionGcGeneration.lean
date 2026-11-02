import duplicate_prefix.GeneralBorrowReusableGeneration
import duplicate_prefix.GeneralBorrowPartitionGcHistory

namespace DuplicatePrefix.GeneralBorrowPartitionGcGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionGcHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- All completed operations and final borrow-state resources are outputs of
actual allocation and arbitrary mixed partition history. -/
structure Generated (capacity : UInt64) (rootTag tag : BorTag) (actions : List (Action capacity)) (reserve : Fin 5 → BorTag) where
  state : GeneralBorrowPartitionState.State (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions)
    GeneralBorrowFullSharedSeed.root capacity
  completed : AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions
  tagged : state.node.tag = rootTag
  fresh : GeneralBorrowTagMap.Fresh (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions).tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions).tagMapping (reserve i)

/-- No initial graph, permission, allocator invariant, operation success or
intermediate state is supplied. Tags and conservative storage room are explicit. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup) (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (tagUnused : tag ∉ actions.flatMap Action.tags) (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295) : Generated capacity rootTag tag actions reserve := by
  let initial := GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)
  have initialTag : initial.node.tag = rootTag := rfl
  have fresh : ∀ nextTag ∈ actions.flatMap Action.tags,
      GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have budget : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.size+(actions.flatMap Action.tags).length+4 ≤ 4294967295 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size+_+4 ≤ _
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    exact room
  have history := run _ GeneralBorrowFullSharedSeed.root capacity rootTag initial initialTag actions unique fresh budget
  let post := Classical.choice history.2.1
  exact ⟨post.val,history.1,post.property,
    history.2.2.2 tag tagUnused (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag tag different),
    fun i => history.2.2.2 (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag (reserve i) (fun same => reserved i (by simp [same])))⟩

end DuplicatePrefix.GeneralBorrowPartitionGcGeneration
