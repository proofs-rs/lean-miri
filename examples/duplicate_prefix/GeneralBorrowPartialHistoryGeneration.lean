import duplicate_prefix.GeneralBorrowReusableGeneration
import duplicate_prefix.GeneralBorrowPartitionMixedHistory

namespace DuplicatePrefix.GeneralBorrowPartialHistoryGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Allocation-derived mixed GC history followed by actual arbitrarily
interleaved partial-range accesses and shared stages. -/
structure Generated (capacity : UInt64) (rootTag tag : BorTag)
    (prior : List GeneralBorrowReusableHistory.Action)
    (actions : List (GeneralBorrowPartitionMixedHistory.Action capacity)) (reserve : Fin 5 → BorTag) where
  state : GeneralBorrowPartitionState.State
    (GeneralBorrowPartitionMixedHistory.execute
      (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions)
    GeneralBorrowFullSharedSeed.root capacity
  priorCompleted : GeneralBorrowReusableHistory.AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior
  completed : GeneralBorrowPartitionMixedHistory.AllCompleted
    (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions
  tagged : state.node.tag = rootTag
  fresh : GeneralBorrowTagMap.Fresh
    (GeneralBorrowPartitionMixedHistory.execute
      (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions).tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh
    (GeneralBorrowPartitionMixedHistory.execute
      (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions).tagMapping (reserve i)

/-- Form graph, ownership, allocator, vacant Clean and all historical operation
completions from real allocation. Only initial tag supply and numeric storage
headroom are assumed; no intermediate state or successful operation is an input. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (prior : List GeneralBorrowReusableHistory.Action)
    (actions : List (GeneralBorrowPartitionMixedHistory.Action capacity))
    (unique : ((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags).Nodup)
    (rootUnused : rootTag ∉ (prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags)
    (tagUnused : tag ∉ (prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: ((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags))
    (room : 1+((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags).length+4 ≤ 4294967295) :
    Generated capacity rootTag tag prior actions reserve := by
  let seed := GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different
  have seedTag : seed.node.tag = rootTag := rfl
  have distinct := List.nodup_append.mp unique
  have initialFresh : ∀ nextTag ∈ prior.flatMap GeneralBorrowReusableHistory.Action.tags,
      GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag
      (fun same => rootUnused (List.mem_append_left _ (same ▸ member)))
  have seedSize : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  have first := GeneralBorrowReusableHistory.run _ GeneralBorrowFullSharedSeed.root capacity rootTag seed seedTag prior
    distinct.1 initialFresh (by rw [seedSize];rw [List.length_append] at room;omega)
  let firstState := Classical.choice first.2.1
  let start := GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity firstState.val
  have startTag : start.node.tag = rootTag := firstState.property
  have nextFresh : ∀ nextTag ∈ actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags,
      GeneralBorrowTagMap.Fresh
        (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior).tagMapping nextTag := by
    intro nextTag member
    apply first.2.2.2 nextTag
    · intro old;exact distinct.2.2 nextTag old nextTag member rfl
    · exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag
        (fun same => rootUnused (List.mem_append_right _ (same ▸ member)))
  have budget : (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior).nodes.size+
      (actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags).length+4 ≤ 4294967295 := by
    have bound := first.2.2.1
    rw [seedSize] at bound
    rw [List.length_append] at room
    omega
  have second := GeneralBorrowPartitionMixedHistory.run _ GeneralBorrowFullSharedSeed.root capacity rootTag start startTag actions distinct.2.1 nextFresh budget
  let finalState := Classical.choice second.2.1
  have future : ∀ nextTag, nextTag ∉ (prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
        actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags → rootTag ≠ nextTag →
      GeneralBorrowTagMap.Fresh
        (GeneralBorrowPartitionMixedHistory.execute
          (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions).tagMapping nextTag := by
    intro nextTag unused notRoot
    have absent : nextTag ∉ prior.flatMap GeneralBorrowReusableHistory.Action.tags ∧
        nextTag ∉ actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags := by
      simpa only [List.mem_append,not_or] using unused
    exact second.2.2.2 nextTag absent.2 (first.2.2.2 nextTag absent.1
      (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag notRoot))
  exact ⟨finalState.val,first.1,second.1,finalState.property,future tag tagUnused different,
    fun i => future (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (fun same => reserved i (by simp [same]))⟩

end DuplicatePrefix.GeneralBorrowPartialHistoryGeneration
