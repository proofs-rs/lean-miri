import duplicate_prefix.GeneralBorrowSharedBankGcHistory
import duplicate_prefix.GeneralBorrowSharedRootBankGeneration

namespace DuplicatePrefix.GeneralBorrowSharedBankGcGeneration
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedRootBankState DuplicatePrefix.GeneralBorrowSharedBankGcHistory

open DuplicatePrefix.GeneralBorrowSharedRootBankGeneration (initial)
open DuplicatePrefix.GeneralBorrowSharedBankGcAction
set_option autoImplicit false in
/-- Every historical completion and the original mutable root's entry contract
are outputs of finite branching generation. -/
structure Generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (actions : List Action) (reserve : Fin 5 → BorTag) where
  state : State GeneralBorrowFullSharedSeed.root rootTag offset len
  history : Run positive tag (initial capacity nonzero rootTag tag different offset len bounds) actions state
  length : state.bank.handles.length = 1+(tags actions).length
  fresh : GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping (reserve i)

/-- Allocate, build an arbitrary finite prior-parent shared tree, and retain the
ORIGINAL root's mutable label. Requested subslice, tag resources and node budget
are explicit; no final graph, ownership, successful operation or entry Data is
assumed. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (actions : List Action) (choices : Choices 1 actions) (unique : (tags actions).Nodup)
    (rootUnused : rootTag ∉ tags actions) (tagUnused : tag ∉ tags actions)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: tags actions)
    (room : 1+(tags actions).length+4 ≤ 4294967295) :
    Generated capacity nonzero rootTag tag different offset len positive bounds actions reserve := by
  let start := initial capacity nonzero rootTag tag different offset len bounds
  have startSize : start.bank.tree.nodes.size = 1 := rfl
  have handles : start.bank.handles.length = 1 := rfl
  have fresh : ∀ nextTag ∈ tags actions, GeneralBorrowTagMap.Fresh start.bank.tree.tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have available := GeneralBorrowSharedBankGcHistory.generate start positive tag
    (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag tag different) actions (by rw [handles];exact choices)
    unique tagUnused fresh (by rw [startSize];exact room)
  let final := Classical.choose available
  have output := Classical.choose_spec available
  have future : ∀ nextTag, nextTag ∉ tags actions → rootTag ≠ nextTag → GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping nextTag := by
    intro nextTag unused notRoot
    exact output.2.2.2 nextTag unused (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag notRoot)
  have length : final.bank.handles.length = start.bank.handles.length+(tags actions).length := output.2.1
  rw [handles] at length
  exact ⟨final,output.1,length,future tag tagUnused different,
    fun i => future (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (fun same => reserved i (by simp [same]))⟩
end DuplicatePrefix.GeneralBorrowSharedBankGcGeneration
