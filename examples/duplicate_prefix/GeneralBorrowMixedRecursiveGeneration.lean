import duplicate_prefix.GeneralBorrowPartitionGcGeneration
import duplicate_prefix.GeneralBorrowRecursiveCallGeneration

namespace DuplicatePrefix.GeneralBorrowMixedRecursiveGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowRecursiveRootRestore
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- A real mixed/GC prefix and a subsequent real arbitrary-depth descendant
chain, with all completed operations and final entry resources as outputs. -/
structure Generated (capacity : UInt64) (rootTag tag : BorTag)
    (prior : List (GeneralBorrowPartitionGcHistory.Action capacity))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag) (reserve : Fin 5 → BorTag) where
  prefixState : GeneralBorrowPartitionState.State
    (GeneralBorrowPartitionGcHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior)
    GeneralBorrowFullSharedSeed.root capacity
  prefixTagged : prefixState.node.tag = rootTag
  prefixCompleted : GeneralBorrowPartitionGcHistory.AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior
  state : State GeneralBorrowFullSharedSeed.root offset len
  history : Run positive
    (GeneralBorrowRecursiveSharedGeneration.of_partition _ GeneralBorrowFullSharedSeed.root capacity prefixState offset len bounds)
    (GeneralBorrowRecursiveCallGeneration.actions tags) state
  height : GeneralBorrowRecursiveSharedHistory.height state = tags.length+1
  facts : RootFacts state rootTag
  fresh : GeneralBorrowTagMap.Fresh state.tree.tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh state.tree.tagMapping (reserve i)

/-- Actual arbitrary partial-range root access/shared/default/activation/zero/GC
history can precede an arbitrary-depth unprotected descendant chain. Original
root ownership, both history phases and final resources are derived internally;
only tag supply, capacity and requested-range bounds are input data. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (prior : List (GeneralBorrowPartitionGcHistory.Action capacity))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag)
    (unique : ((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags).Nodup)
    (rootUnused : rootTag ∉ (prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags)
    (tagUnused : tag ∉ (prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: ((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags))
    (room : 1+((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags).length+4 ≤ 4294967295) :
    Generated capacity rootTag tag prior offset len positive bounds tags reserve := by
  let seed := GeneralBorrowPartitionState.of_reusable _ GeneralBorrowFullSharedSeed.root capacity
    (GeneralBorrowReusableGeneration.seed capacity nonzero rootTag tag different)
  have seedTag : seed.node.tag = rootTag := rfl
  have distinct := List.nodup_append.mp unique
  have firstFresh : ∀ nextTag ∈ prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags,
      GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping nextTag := by
    intro nextTag member
    exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag
      (fun same => rootUnused (List.mem_append_left _ (same ▸ member)))
  have seedSize : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  have first := GeneralBorrowPartitionGcHistory.run _ GeneralBorrowFullSharedSeed.root capacity rootTag seed seedTag prior distinct.1 firstFresh
    (by rw [seedSize];rw [List.length_append] at room;omega)
  let prefixState := Classical.choice first.2.1
  let start := GeneralBorrowRecursiveSharedGeneration.of_partition _ GeneralBorrowFullSharedSeed.root capacity prefixState.val offset len bounds
  have startFacts : RootFacts start rootTag := by
    have known := GeneralBorrowRecursiveRootRestore.of_partition _ GeneralBorrowFullSharedSeed.root capacity prefixState.val offset len bounds
    rw [prefixState.property] at known
    exact known
  have mapped : (GeneralBorrowRecursiveCallGeneration.actions tags).map Prod.fst = tags := by
    simp [GeneralBorrowRecursiveCallGeneration.actions,List.map_map,Function.comp_def]
  have chainUnique : ((GeneralBorrowRecursiveCallGeneration.actions tags).map Prod.fst).Nodup := by rw [mapped];exact distinct.2.1
  have chainFresh : ∀ nextTag ∈ (GeneralBorrowRecursiveCallGeneration.actions tags).map Prod.fst,
      GeneralBorrowTagMap.Fresh start.tree.tagMapping nextTag := by
    rw [mapped]
    intro nextTag member
    apply first.2.2.2 nextTag
    · intro earlier;exact distinct.2.2 nextTag earlier nextTag member rfl
    · exact GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag
        (fun same => rootUnused (List.mem_append_right _ (same ▸ member)))
  have chainRoom : start.tree.nodes.size+(GeneralBorrowRecursiveCallGeneration.actions tags).length+4 ≤ 4294967295 := by
    have growth := first.2.2.1
    rw [seedSize] at growth
    rw [List.length_append] at room
    change (GeneralBorrowPartitionGcHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior).nodes.size+
      (GeneralBorrowRecursiveCallGeneration.actions tags).length+4 ≤ _
    simp only [GeneralBorrowRecursiveCallGeneration.actions,List.length_map]
    omega
  have second := GeneralBorrowRecursiveSharedHistory.generate start positive (GeneralBorrowRecursiveCallGeneration.actions tags) chainUnique chainFresh chainRoom
  let final := Classical.choose second
  have output := Classical.choose_spec second
  have facts := GeneralBorrowRecursiveRootRestore.Run.root_facts output.1 rootTag startFacts (by
    intro step member
    obtain ⟨nextTag,member,rfl⟩ := List.mem_map.mp member
    rfl)
  have startHeight : GeneralBorrowRecursiveSharedHistory.height start = 1 := by
    let location : LocationTree := ⟨⟨#[]⟩,{}⟩
    have path := startFacts.path location
    have count := congrArg List.length path
    simpa only [GeneralBorrowRecursiveSharedHistory.height,start,GeneralBorrowRecursiveSharedGeneration.of_partition,List.length_singleton,location] using count
  have height : GeneralBorrowRecursiveSharedHistory.height final = tags.length+1 := by
    have count := output.1.height
    change GeneralBorrowRecursiveSharedHistory.height final = GeneralBorrowRecursiveSharedHistory.height start+(GeneralBorrowRecursiveCallGeneration.actions tags).length at count
    rw [startHeight] at count
    simpa only [GeneralBorrowRecursiveCallGeneration.actions,List.length_map,Nat.add_comm] using count
  have future : ∀ nextTag, nextTag ∉ (prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags → rootTag ≠ nextTag →
      GeneralBorrowTagMap.Fresh final.tree.tagMapping nextTag := by
    intro nextTag unused notRoot
    have absent : nextTag ∉ prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags ∧ nextTag ∉ tags := by
      simpa only [List.mem_append,not_or] using unused
    exact output.2.2 nextTag (by simpa only [mapped] using absent.2)
      (first.2.2.2 nextTag absent.1 (GeneralBorrowReusableGeneration.seed_fresh capacity nonzero rootTag nextTag notRoot))
  exact ⟨prefixState.val,prefixState.property,first.1,final,output.1,height,facts,future tag tagUnused different,
    fun i => future (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (fun same => reserved i (by simp [same]))⟩

end DuplicatePrefix.GeneralBorrowMixedRecursiveGeneration
