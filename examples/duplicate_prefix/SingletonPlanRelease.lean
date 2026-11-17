import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.SingletonPlanRelease
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem equation {K : Type} (protections : ProtectedTags)
    (before after : MemoryState Provenance BorrowTree K) (id : AllocId) (tag : BorTag)
    (entry finalEntry : LocalAllocation Provenance BorrowTree K)
    (present : before.live.find? (fun row => row.1 == id) = some (id,entry))
    (finalPresent : after.live.find? (fun row => row.1 == id) = some (id,finalEntry))
    (plan : StackPopRelease.Plan protections [(id,tag)] before after) :
    entry.allocation.extra.releaseProtector tag protections = ⟨finalEntry.allocation.extra,.Released⟩ := by
  cases plan with
  | skip _ _ info _ _ _ lookup notLive tail =>
      have got : info = ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
        have lookup' : (Except.ok info : Except AllocationLookupError AllocationInfo) = .ok
            ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
          simpa only [MemoryState.getAllocInfo,present,pure,Except.pure] using lookup.symm
        exact Except.ok.inj lookup'
      exact False.elim (notLive (by rw [got]))
  | live _ _ actual tree _ _ _ found released tail =>
      have actualEq : actual=entry := congrArg Prod.snd (Option.some.inj (found.symm.trans present))
      subst actual
      cases tail
      have committed := StackPopRelease.lookup_commit_same before id entry tree
      have entries := congrArg Prod.snd (Option.some.inj (committed.symm.trans finalPresent))
      have trees := congrArg (fun entry : LocalAllocation Provenance BorrowTree K => entry.allocation.extra) entries
      have treeEq : tree=finalEntry.allocation.extra := by
        simpa only [Allocation.setExtra,Allocation.mapExtra] using trees
      rw [← treeEq]
      exact released
end DuplicatePrefix.SingletonPlanRelease
