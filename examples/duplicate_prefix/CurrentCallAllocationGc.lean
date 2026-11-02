import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.GeneralBorrowGcForestComplete
import duplicate_prefix.GeneralBorrowGcResourceFrame
import duplicate_prefix.GeneralBorrowGcForestGeometry
import duplicate_prefix.RetagEntry
namespace DuplicatePrefix.CurrentCallAllocationGc
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Canonical allocation identity survives the actual collector and its actual
installation. No old intermediate nodes, permissions, or completion edges are claimed. -/
theorem collect (before post : Before) (tracker next : MachineHooks.BorrowState) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree)
    (capability : AllocationCapability before tracker id allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global)
    (liveTags : Array BorTag)
    (installed : Present (ActualWorld post) id (allocation.setExtra (allocation.extra.removeUnreachableTags liveTags).tree))
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id) :
    AllocationCapability post next id (allocation.setExtra (allocation.extra.removeUnreachableTags liveTags).tree) := by
  let tree := allocation.extra
  have formed := runtime.formed.toGraphState
  obtain ⟨forest⟩ := formed.forest default tracker.global.protectedTags
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨_,_,capacity,_,_,_,_,_,metadata,roots⟩ := GeneralBorrowGcForestComplete.complete tree default tracker.global.protectedTags
    forest depth formed.children formed.fits formed.rootNodes runtime.formed.well liveTags
  have rootFrame := (GeneralBorrowGcResourceFrame.preserves (n:=0) (fun step=>Fin.elim0 step) tree liveTags
    (by intro step;exact Fin.elim0 step)).roots
  obtain ⟨oldNode,oldAt,parentless,disabled,tagged⟩ := capability.rootNode
  have member : allocationRoot∈tree.roots.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? capability.rootSlot)
  obtain ⟨node,present,noneParent⟩ := roots allocationRoot member
  obtain ⟨original,originalAt,preserved⟩ := metadata allocationRoot node present
  have equal : original=oldNode := Option.some.inj (originalAt.symm.trans oldAt)
  subst original
  refine ⟨installed,capability.extent,capacity.trans capability.treeExtent,?_,node,present,noneParent,?_,?_⟩
  · change (tree.removeUnreachableTags liveTags).tree.roots[0]?=some allocationRoot
    rw [rootFrame]
    exact capability.rootSlot
  · exact preserved.permission.trans disabled
  · rw [rootTag,preserved.tag]
    exact tagged

/-- Install the actual collected allocation into the actual heap; canonical
root identity uses the unchanged allocation-tag cache, rather than the old world. -/
theorem install (before : Before) (tracker next : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capability : AllocationCapability before tracker id entry.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (liveTags : Array BorTag) (rootTag : next.global.rootTag? id=tracker.global.rootTag? id) :
    let collected := (entry.allocation.extra.removeUnreachableTags liveTags).tree
    let post := {before with memory:=RetagEntry.updatedMemory before.memory id entry collected,borrowTracker:=some next}
    AllocationCapability post next id (entry.allocation.setExtra collected) := by
  let collected := (entry.allocation.extra.removeUnreachableTags liveTags).tree
  let post := {before with memory:=RetagEntry.updatedMemory before.memory id entry collected,borrowTracker:=some next}
  apply collect before post tracker next id entry.allocation capability runtime liveTags _ rootTag
  simp only [Present,ActualWorld,Array.toList_map]
  apply List.mem_map.mpr
  refine ⟨(id,{entry with allocation:=entry.allocation.setExtra collected}),?_,rfl⟩
  exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some
    (MemoryCopyBridge.live_lookup_replaced before.memory id {entry with allocation:=entry.allocation.setExtra collected}))

end
end DuplicatePrefix.CurrentCallAllocationGc
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallAllocationGc" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocation GC capability dependency {dependency}"
