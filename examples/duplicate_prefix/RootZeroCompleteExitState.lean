import duplicate_prefix.RootPhysicalReturn
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RootZeroCompleteExitState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows

theorem extra_self (allocation : Allocation Provenance BorrowTree) : allocation.setExtra allocation.extra = allocation := by
  cases allocation
  rfl

theorem commit_lookup_self
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id target : AllocId)
    (entry targetEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (targetPresent : memory.live.find? (fun row => row.1 == target) = some (target,targetEntry)) :
    (StackPopRelease.commitTree memory id entry entry.allocation.extra).live.find? (fun row => row.1 == target) = some (target,targetEntry) := by
  by_cases same : target=id
  · subst target
    rw [present] at targetPresent
    have equal : targetEntry=entry := (Prod.mk.inj (Option.some.inj targetPresent)).2.symm
    subst targetEntry
    simpa only [extra_self] using StackPopRelease.lookup_commit_same memory id entry entry.allocation.extra
  · exact StackPopRelease.lookup_commit_other memory id target entry targetEntry entry.allocation.extra same targetPresent

theorem profile_lookup {protections rows before after}
    (profile : RootPhysicalReturnPlan.Profile protections rows before after)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : before.live.find? (fun row => row.1 == id)= some (id,entry)) :
    after.live.find? (fun row => row.1 == id)= some (id,entry) := by
  induction profile with
  | nil => exact present
  | nonlive _ _ _ _ _ _ _ _ _ ih => exact ih present
  | slot _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)
  | buffer _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)
  | emptyBuffer _ _ _ _ _ _ _ p _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)
  | four _ _ _ _ _ _ _ _ _ p _ _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)
  | emptyFour _ _ _ _ _ _ _ p _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)
  | nestedWritten _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ ih => exact ih (commit_lookup_self _ _ _ _ _ p present)

theorem relevance_frame_irrelevant
    (first second : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K U) (index : Nat) :
    GenericPopFrame.afterRelevanceAt #[] first machine index = GenericPopFrame.afterRelevanceAt #[] second machine index := by
  simp [GenericPopFrame.afterRelevanceAt, GenericPopFrame.afterRelevance, FrameRelevance.computeTop,
    List.range_succ, List.forIn_nil]

#print axioms profile_lookup
#print axioms relevance_frame_irrelevant
end DuplicatePrefix.RootZeroCompleteExitState
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootZeroCompleteExitState.profile_lookup,
      ``DuplicatePrefix.RootZeroCompleteExitState.relevance_frame_irrelevant] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved zero return state dependency {dependency}"
