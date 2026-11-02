import duplicate_prefix.ConcreteEmptyPoolEntry
import duplicate_prefix.EmptyForestSharedPool

namespace DuplicatePrefix.ConcreteEmptyPoolEntryNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
open GeneralBorrowFreshReborrowStages (Slot)
open ConcreteEmptyPoolEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert
variable {tree : BorrowTree} {parentTag tag : BorTag}

def growth (input : Input tree parentTag tag) : Nat := match input.slot with | .append .. => 1 | .reuse .. => 0

theorem stage_size (input : Input tree parentTag tag) : input.stage.nodes.size = tree.nodes.size+growth input := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes input.index input.parent input.parentNode input.vacant input.present
  have before : (tree.nodes.insert input.index (GeneralBorrowFreshChild.child tag input.parent)).get input.parent = some input.parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes input.index input.parent (GeneralBorrowFreshChild.child tag input.parent) different).trans input.present
  change ((tree.nodes.insert input.index (GeneralBorrowFreshChild.child tag input.parent)).insert input.parent (updatedParent input.parentNode input.index)).size = _
  rw [GeneralBorrowNodeUpdate.insert_existing_size _ input.parent input.parentNode _ before]
  cases selected : input.slot with
  | append noFree aligned fits =>
    have endEq : input.index.toNat = tree.nodes.data.size := by
      simp only [Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    simpa only [growth,selected] using append_size tree.nodes input.index (GeneralBorrowFreshChild.child tag input.parent) endEq
  | reuse child available bounded missing slack =>
    simpa only [Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,growth,Nat.add_zero] using
      GeneralBorrowFreshReuseNode.bounded_size tree.nodes child (GeneralBorrowFreshChild.child tag input.parent) bounded

theorem node_size (input : Input tree parentTag tag) : input.after.nodes.size = tree.nodes.size+growth input :=
  (GeneralBorrowFreshMetadata.node_size input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .None)).trans (stage_size input)

/-- The actual zero constructor consumes only the selected free slot and
preserves all residual sparse vacancy/uniqueness and allocator accounting. -/
theorem allocator (input : Input tree parentTag tag)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (accounting : GeneralBorrowFreshStagePool.Accounting tree) :
    GeneralBorrowFreshAllocatorInvariant.Pool input.after.nodes input.after.tagMapping.deassigned ∧
    GeneralBorrowFreshStagePool.Accounting input.after := by
  have stagePool : GeneralBorrowFreshAllocatorInvariant.Pool input.stage.nodes input.stage.tagMapping.deassigned := by
    cases selected : input.slot with
    | append noFree aligned fits =>
      have empty := Array.back?_eq_none_iff.mp noFree
      change GeneralBorrowFreshAllocatorInvariant.Pool input.stage.nodes input.mapping.deassigned
      simp only [Input.mapping,Input.free,selected,empty]
      exact ⟨by simp,by simp,by simp⟩
    | reuse child available bounded missing slack =>
      have attached := GeneralBorrowFreshAllocatorInvariant.attached tree.nodes tree.tagMapping.deassigned pool
        child input.parent available input.parentNode (GeneralBorrowFreshChild.child tag input.parent) input.present
      simpa only [Input.stage,Input.mapping,Input.free,Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,GeneralBorrowFreshGraph.attached] using attached
  refine ⟨GeneralBorrowFreshStagePool.shape_pool input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .None) stagePool,?_⟩
  unfold GeneralBorrowFreshStagePool.Accounting
  rw [input.mapping_after,node_size input]
  simp only [Input.mapping,Array.size_push]
  change tree.tagMapping.mapping.size+1+input.free.size = tree.nodes.size+growth input
  unfold GeneralBorrowFreshStagePool.Accounting at accounting
  cases selected : input.slot with
  | append noFree aligned fits =>
    have empty := Array.back?_eq_none_iff.mp noFree
    simp only [Input.free,growth,selected,empty,Array.size_empty,Nat.add_zero]
    simpa only [empty,Array.size_empty,Nat.add_zero] using congrArg (fun n => n+1) accounting
  | reuse child available bounded missing slack =>
    have nonempty : 0 < tree.tagMapping.deassigned.size := by
      obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp available
      rw [eq,Array.size_push]
      omega
    simp only [Input.free,growth,selected,Array.size_pop,Nat.add_zero]
    omega

/-- Empty constructors materialize no permissions. The independent initial
all-vacant Clean invariant survives node insertion and the actual SIFA loop. -/
theorem vacant_clean (input : Input tree parentTag tag) (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean input.after := by
  have first := GeneralBorrowGcVacantClean.insert_preserves tree input.index (GeneralBorrowFreshChild.child tag input.parent) clean
  have second := GeneralBorrowGcVacantClean.insert_preserves
    {tree with nodes := tree.nodes.insert input.index (GeneralBorrowFreshChild.child tag input.parent)} input.parent
    (updatedParent input.parentNode input.index) first
  have stageClean : GeneralBorrowGcVacantClean.VacantClean input.stage := second
  intro query vacant
  have stageVacant : input.stage.nodes.get query = none := by
    cases present : input.stage.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,lookup,_,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields input.stage input.after
        (GeneralBorrowSifaView.preserves input.stage input.parent .None) query node present
      change input.after.nodes.get query = some next at lookup
      rw [vacant] at lookup
      cases lookup
  exact GeneralBorrowFreshFutureClean.sifa_preserves input.stage input.parent .None query (stageClean query stageVacant)

/-- Form a genuine SHARED continuation Input after the actual protected Default append OR reuse
step. New-parent presence, depth, remaining pool, accounting and Clean are all
derived. The only additional facts are initial next-tag freshness/distinctness
and conservative numeric room. -/
noncomputable def next (input : Input tree parentTag tag) (nextTag : BorTag)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (accounting : GeneralBorrowFreshStagePool.Accounting tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : tag ≠ nextTag)
    (room : tree.nodes.size+1 ≤ 4294967295) : EmptyForestSharedPool.Input input.after tag nextTag := by
  let node := Classical.choose input.node_exists
  have present : input.after.nodeAt input.index = some node := (Classical.choose_spec input.node_exists).1
  have good := allocator input pool accounting
  have lookup : input.after.indexOfTag tag = some input.index := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index input.free
  have nextFresh : GeneralBorrowTagMap.Fresh input.after.tagMapping nextTag := by
    rw [input.mapping_after]
    intro row member
    rcases Array.mem_push.mp member with old | last
    · exact fresh row old
    · cases last;exact different
  have fits : input.after.tagMapping.mapping.size ≤ 4294967295 := by
    have sizes := node_size input
    have growthBound : growth input ≤ 1 := by cases selected : input.slot <;> simp [growth,selected]
    have balanced := good.2
    unfold GeneralBorrowFreshStagePool.Accounting at balanced
    omega
  exact EmptyForestSharedPool.factory input.after tag nextTag input.index node input.afterDepth lookup present nextFresh
    good.1 good.2 fits (vacant_clean input clean)

end DuplicatePrefix.ConcreteEmptyPoolEntryNext
