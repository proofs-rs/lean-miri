import duplicate_prefix.GeneralBorrowSharedRootBankHistory

namespace DuplicatePrefix.GeneralBorrowSharedRootBankGeneration
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedRootBankState DuplicatePrefix.GeneralBorrowSharedRootBankHistory

def initial (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    State GeneralBorrowFullSharedSeed.root rootTag offset len :=
  GeneralBorrowSharedRootBankState.of_partition (BorrowTree.new rootTag (Size.ofBytes capacity))
    GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)) offset len bounds

set_option autoImplicit false in
/-- Every historical completion and the original mutable root's entry contract
are outputs of finite branching generation. -/
structure Generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (steps : List (BorTag × Nat)) (reserve : Fin 5 → BorTag) where
  state : State GeneralBorrowFullSharedSeed.root rootTag offset len
  history : Run positive (initial capacity nonzero rootTag tag different offset len bounds) steps state
  length : state.bank.handles.length = 1+steps.length
  fresh : GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping (reserve i)

/-- Allocate, build an arbitrary finite prior-parent shared tree, and retain the
ORIGINAL root's mutable label. Requested subslice, tag resources and node budget
are explicit; no final graph, ownership, successful operation or entry Data is
assumed. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (steps : List (BorTag × Nat)) (choices : Choices 1 steps) (unique : (steps.map Prod.fst).Nodup)
    (rootUnused : rootTag ∉ steps.map Prod.fst) (tagUnused : tag ∉ steps.map Prod.fst)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: steps.map Prod.fst)
    (room : 1+steps.length+4 ≤ 4294967295) :
    Generated capacity nonzero rootTag tag different offset len positive bounds steps reserve := by
  let start := initial capacity nonzero rootTag tag different offset len bounds
  have startSize : start.bank.tree.nodes.size = 1 := rfl
  have handles : start.bank.handles.length = 1 := rfl
  have fresh : ∀ nextTag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh start.bank.tree.tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have available := GeneralBorrowSharedRootBankHistory.generate start positive steps (by rw [handles];exact choices)
    unique fresh (by rw [startSize];exact room)
  let final := Classical.choose available
  have output := Classical.choose_spec available
  have future : ∀ nextTag, nextTag ∉ steps.map Prod.fst → rootTag ≠ nextTag → GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping nextTag := by
    intro nextTag unused notRoot
    exact output.2.2.2 nextTag unused (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag notRoot)
  have length : final.bank.handles.length = start.bank.handles.length+steps.length := output.2.1
  rw [handles] at length
  exact ⟨final,output.1,length,future tag tagUnused different,
    fun i => future (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (fun same => reserved i (by simp [same]))⟩
end DuplicatePrefix.GeneralBorrowSharedRootBankGeneration
