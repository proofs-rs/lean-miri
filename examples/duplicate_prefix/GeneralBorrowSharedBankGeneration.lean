import duplicate_prefix.GeneralBorrowSharedBankSeed
import duplicate_prefix.GeneralBorrowSharedBankHistory

namespace DuplicatePrefix.GeneralBorrowSharedBankGeneration
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState DuplicatePrefix.GeneralBorrowSharedBankHistory

def allocation (capacity : UInt64) (capacityPositive : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : State GeneralBorrowFullSharedSeed.root offset len :=
  GeneralBorrowSharedBankSeed.of_partition (BorrowTree.new rootTag (Size.ofBytes capacity))
    GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity capacityPositive rootTag resourceTag different)) offset len bounds

/-- Real allocation followed by any finite prior-parent shared history on the
specified positive subslice. Initial graph, allocator and every stage's Read
owners are constructed internally. The last shared tag is not a mutable caller. -/
theorem generate (capacity : UInt64) (capacityPositive : capacity ≠ 0) (rootTag resourceTag : BorTag)
    (different : rootTag ≠ resourceTag) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (steps : List (BorTag × Nat))
    (choices : Choices 1 steps) (unique : (steps.map Prod.fst).Nodup)
    (rootUnused : rootTag ∉ steps.map Prod.fst) (room : 1+steps.length+4 ≤ 4294967295) :
    let initial := allocation capacity capacityPositive rootTag resourceTag different offset len bounds
    ∃ final, Run nonzero initial steps final ∧
      final.handles.length = 1+steps.length ∧
      final.tree.nodes.size ≤ 1+steps.length ∧
      (∀ tag, tag ∉ steps.map Prod.fst → rootTag ≠ tag → GeneralBorrowTagMap.Fresh final.tree.tagMapping tag) := by
  let initial := allocation capacity capacityPositive rootTag resourceTag different offset len bounds
  have seedSize : initial.tree.nodes.size = 1 := by rfl
  have handles : initial.handles.length = 1 := rfl
  have fresh : ∀ tag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh initial.tree.tagMapping tag := by
    intro tag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity capacityPositive rootTag tag (fun same => rootUnused (same ▸ member))
  obtain ⟨final,history,length,bound,future⟩ := GeneralBorrowSharedBankHistory.generate initial nonzero steps
    (by rw [handles];exact choices) unique fresh (by rw [seedSize];exact room)
  refine ⟨final,history,?_,?_,?_⟩
  · simpa only [handles] using length
  · simpa only [seedSize] using bound
  · intro tag unused notRoot
    exact future tag unused (GeneralBorrowReusableGeneration.seed_fresh capacity capacityPositive rootTag tag notRoot)
end DuplicatePrefix.GeneralBorrowSharedBankGeneration
