import duplicate_prefix.CurrentCallSpatialSubrangeInstall
namespace DuplicatePrefix.CurrentCallSpatialSubrangeSequence
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)

def readResult (start amount : UInt64) := role.backing.allocation.extra.performBorrowAccessRange
  (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed

def readMachine (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (start amount : UInt64) : Before :=
  {before with memory:=RetagEntry.updatedMemory before.memory role.backing.id entry (readResult role start amount).tree}

structure ReadStage (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (start amount : UInt64) where
  context : Context (readMachine role entry start amount)
  current : RoleCover (readMachine role entry start amount) tracker context .mut offset length
  allocation : current.backing.allocation=role.backing.allocation.setExtra (readResult role start amount).tree
  id : current.backing.id=role.backing.id
  family : current.family=role.family
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts current.backing.allocation.extra tracker.global
  distinct : current.backing.allocation.extra.roots.toList.Nodup
  short : current.backing.allocation.extra.nodes.size<65536
  done : (readResult role start amount).status=.Completed
  shape : (readResult role start amount).tree={role.backing.allocation.extra with locations:=(readResult role start amount).tree.locations}
  capacity : (readResult role start amount).tree.locations.size=role.backing.allocation.extra.locations.size
  frames : Origins (CurrentCallSpatialRows.Frame role) role.backing.allocation.extra.locations (readResult role start amount).tree.locations

private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).extra=tree:=by cases allocation;rfl
private theorem present_live (machine : Before) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) : Present (ActualWorld machine) id entry.allocation:=by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
private theorem present_allocation {world id old new} (eq : new=old) (present : Present world id old) : Present world id new:=by cases eq;exact present
private theorem runtime_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) : DuplicatePrefixBorrowContract.RuntimeFacts (allocation.setExtra tree).extra global:=runtime

theorem read_stage
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (tag : BorTag) (grant : UniIndex) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (tagged : role.backing.allocation.extra.indexOfTag tag=some grant)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (_live : before.memory.live.find? (fun row=>row.1==role.backing.id)=some (role.backing.id,entry))
    (allocationEq : role.backing.allocation=entry.allocation)
    (start amount : UInt64) (lower : offset≤start.toNat) (upper : start.toNat+amount.toNat≤offset+length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    Nonempty (ReadStage role entry start amount) := by
  obtain ⟨contract,afterRuntime,parents⟩:=CurrentCallSpatialSubrange.Read.access_runtime role rfl runtime distinct short start amount lower upper nonzero bounds .VisitChildrenOfAccessed
  have live : (readMachine role entry start amount).memory.live.find? (fun row=>row.1==role.backing.id)=some
      (role.backing.id,{entry with allocation:=entry.allocation.setExtra (readResult role start amount).tree}):=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  have actual:=present_live (readMachine role entry start amount) role.backing.id
    {entry with allocation:=entry.allocation.setExtra (readResult role start amount).tree} live
  have allocationPresent : Present (ActualWorld (readMachine role entry start amount)) role.backing.id
      (role.backing.allocation.setExtra (readResult role start amount).tree):=
    present_allocation (congrArg (fun allocation : Allocation Provenance BorrowTree=>allocation.setExtra (readResult role start amount).tree) allocationEq) actual
  have updatedShape : (role.backing.allocation.setExtra (readResult role start amount).tree).extra=
      {role.backing.allocation.extra with locations:=(role.backing.allocation.setExtra (readResult role start amount).tree).extra.locations}:=contract.tree_eq
  obtain ⟨context,current,allocation,idEq,family⟩:=CurrentCallSpatialSubrangeInstall.cover role
    (role.backing.allocation.setExtra (readResult role start amount).tree) allocationPresent rfl rfl updatedShape contract.capacity
    (runtime_setExtra _ _ _ afterRuntime) contract.frames tag grant concrete tagged
  have treeEq : current.backing.allocation.extra=(readResult role start amount).tree:=
    (congrArg Allocation.extra allocation).trans (extra_setExtra _ _)
  refine ⟨⟨context,current,allocation,idEq,family,?_,?_,?_,contract.completed,contract.tree_eq,contract.capacity,contract.frames⟩⟩
  · rw [treeEq];exact afterRuntime
  · rw [treeEq];dsimp only [readResult];rw [contract.roots];exact distinct
  · rw [treeEq];dsimp only [readResult];rw [contract.nodes];exact short

namespace ReadStage
variable {role} {entry start amount} (stage : ReadStage role entry start amount)

theorem tree : stage.current.backing.allocation.extra=(readResult role start amount).tree:=
  (congrArg Allocation.extra stage.allocation).trans (extra_setExtra _ _)

theorem provenance : CurrentCallSpatialRows.provenance stage.current=CurrentCallSpatialRows.provenance role:=by
  unfold CurrentCallSpatialRows.provenance
  rw [stage.family]

def writeResult (writeStart writeAmount : UInt64) := stage.current.backing.allocation.extra.performBorrowAccessRange
  (CurrentCallSpatialRows.provenance stage.current) (Size.ofBytes writeStart) (Size.ofBytes writeAmount) .Write
  tracker.global.protectedTags .VisitChildrenOfAccessed

theorem write_eq (writeStart writeAmount : UInt64) : writeResult stage writeStart writeAmount=
    (readResult role start amount).tree.performBorrowAccessRange (CurrentCallSpatialRows.provenance role)
      (Size.ofBytes writeStart) (Size.ofBytes writeAmount) .Write tracker.global.protectedTags .VisitChildrenOfAccessed:=by
  unfold writeResult
  rw [tree stage,provenance stage]

/-- The second fold retains the entire same source bank reconstructed after
Read, rather than restricting it to the requested destination interval. -/
abbrev write := CurrentCallSpatialSubrange.Write.range stage.current rfl stage.runtime stage.distinct stage.short
end ReadStage

end
end DuplicatePrefix.CurrentCallSpatialSubrangeSequence
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSubrangeSequence" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sequential full-bank access dependency {dependency}"
