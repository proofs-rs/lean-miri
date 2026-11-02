import duplicate_prefix.GeneralBorrowRecursiveRootRestore

namespace DuplicatePrefix.GeneralBorrowRecursiveCallGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowRecursiveRootRestore
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual unprotected shared-chain actions. -/
def actions (tags : List BorTag) : List (BorTag × Bool) := tags.map (fun tag => (tag,false))

/-- A positive requested subslice of an actual allocation supplies the initial
recursive state; the allocation may be larger than the input slice. -/
def initial (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    State GeneralBorrowFullSharedSeed.root offset len :=
  GeneralBorrowRecursiveSharedGeneration.of_partition (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)) offset len bounds

private theorem initial_facts (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    RootFacts (initial capacity nonzero rootTag tag different offset len bounds) rootTag :=
  GeneralBorrowRecursiveRootRestore.of_partition (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)) offset len bounds

set_option autoImplicit false in
/-- Generated final state and every historical completion; these are outputs,
not caller-supplied graph, ownership, operation-success or trace assumptions. -/
structure Generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag) (reserve : Fin 5 → BorTag) where
  state : State GeneralBorrowFullSharedSeed.root offset len
  history : Run positive (initial capacity nonzero rootTag tag different offset len bounds) (actions tags) state
  height : GeneralBorrowRecursiveSharedHistory.height state = tags.length+1
  facts : RootFacts state rootTag
  fresh : GeneralBorrowTagMap.Fresh state.tree.tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh state.tree.tagMapping (reserve i)

/-- Allocate, build an arbitrary finite chain of real shared descendants on
an arbitrary positive in-bounds subslice, and restore the ORIGINAL root's Write
ownership. Resource tags and node capacity are explicit; entry Data is internal. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags) (tagUnused : tag ∉ tags)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) :
    Generated capacity nonzero rootTag tag different offset len positive bounds tags reserve := by
  let start := initial capacity nonzero rootTag tag different offset len bounds
  have startSize : start.tree.nodes.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  have mapped : (actions tags).map Prod.fst = tags := by simp [actions,List.map_map,Function.comp_def]
  have fresh : ∀ nextTag ∈ (actions tags).map Prod.fst, GeneralBorrowTagMap.Fresh start.tree.tagMapping nextTag := by
    rw [mapped]
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have distinct : ((actions tags).map Prod.fst).Nodup := by rw [mapped];exact unique
  have available := GeneralBorrowRecursiveSharedHistory.generate start positive (actions tags) distinct fresh
    (by rw [startSize];simpa only [actions,List.length_map] using room)
  let final := Classical.choose available
  have output := Classical.choose_spec available
  have facts := GeneralBorrowRecursiveRootRestore.Run.root_facts output.1 rootTag
    (initial_facts capacity nonzero rootTag tag different offset len bounds) (by
      intro step member
      obtain ⟨nextTag,member,rfl⟩ := List.mem_map.mp member
      rfl)
  have startHeight : GeneralBorrowRecursiveSharedHistory.height start = 1 := by
    let location : LocationTree := ⟨⟨#[]⟩,{}⟩
    have path := (initial_facts capacity nonzero rootTag tag different offset len bounds).path location
    have count := congrArg List.length path
    simpa only [GeneralBorrowRecursiveSharedHistory.height,start,initial,GeneralBorrowRecursiveSharedGeneration.of_partition,List.length_singleton,location] using count
  have height : GeneralBorrowRecursiveSharedHistory.height final = tags.length+1 := by
    have count := output.1.height
    change GeneralBorrowRecursiveSharedHistory.height final = GeneralBorrowRecursiveSharedHistory.height start+(actions tags).length at count
    rw [startHeight] at count
    simpa only [actions,List.length_map,Nat.add_comm] using count
  have future : ∀ nextTag, nextTag ∉ tags → rootTag ≠ nextTag → GeneralBorrowTagMap.Fresh final.tree.tagMapping nextTag := by
    intro nextTag unused notRoot
    exact output.2.2 nextTag (by simpa only [mapped] using unused)
      (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag notRoot)
  exact ⟨final,output.1,height,facts,future tag tagUnused different,
    fun i => future (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (fun same => reserved i (by simp [same]))⟩

end DuplicatePrefix.GeneralBorrowRecursiveCallGeneration
