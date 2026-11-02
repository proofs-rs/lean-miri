import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.MemoryCopyBridge
namespace DuplicatePrefix.CurrentCallConversionTargetMetadataFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 250000

def heap (before : MemoryState Provenance BorrowTree MiriMemoryKind) (sourceId : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) : MemoryState Provenance BorrowTree MiriMemoryKind :=
  {before with live:=(before.live.filter (fun row=>row.1!=sourceId)).push (sourceId,entry)}

private theorem other_lookup (before : MemoryState Provenance BorrowTree MiriMemoryKind)
    (sourceId id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (different : id≠sourceId) :
    (heap before sourceId entry).live.find? (fun row=>row.1==id)=before.live.find? (fun row=>row.1==id) := by
  have filtered : (before.live.filter (fun row=>row.1!=sourceId)).find? (fun row=>row.1==id)=before.live.find? (fun row=>row.1==id):=by
    rw [Array.find?_filter]
    congr 1
    funext row
    by_cases hit : (row.1==id)=true
    · have same : row.1=id:=beq_iff_eq.mp hit
      have apart : row.1≠sourceId:=fun equal=>different (same.symm.trans equal)
      have keep : (row.1!=sourceId)=true:=by simpa using apart
      simp [hit,keep]
    · simp [hit]
  simp [heap,Array.find?_push,Ne.symm different,filtered]

/-- Actual source installation preserves raw relocation metadata for every
old target. The source's old base survives, so its new live allocation needs
no extra uncached-alignment premise. Other live and global rows are retained. -/
theorem transport (before after : Before) (sourceId : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (memoryEq : after.memory=heap before.memory sourceId entry)
    (sourceCached : ∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some base)
    (preserved : ∀id base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base→
      after.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base)
    (id : AllocId) (metadata : RelocationTargetMetadata before id) : RelocationTargetMetadata after id := by
  have liveOther (different : id≠sourceId) : after.memory.live.find? (fun row=>row.1==id)=before.memory.live.find? (fun row=>row.1==id):=by
    rw [memoryEq];exact other_lookup before.memory sourceId id entry different
  refine ⟨?_,?_,?_⟩
  · by_cases same : id=sourceId
    · subst id
      exact GlobalAddressLiveErrorExclusion.Supplier.localRow entry (by rw [memoryEq];exact MemoryCopyBridge.live_lookup_replaced before.memory sourceId entry)
    · have old:=metadata.1
      cases old with
      | localRow oldEntry present=>exact .localRow oldEntry ((liveOther same).trans present)
      | functionRow absent present=>exact .functionRow ((liveOther same).trans absent) (by rw [memoryEq];exact present)
      | vaListRow absent noFunction present=>exact .vaListRow ((liveOther same).trans absent) (by rw [memoryEq];exact noFunction) (by rw [memoryEq];exact present)
      | globalRow descriptor absent noFunction noVaList present=>
        exact .globalRow descriptor ((liveOther same).trans absent) (by rw [memoryEq];exact noFunction) (by rw [memoryEq];exact noVaList) (by rw [memoryEq];exact present)
  · rw [memoryEq]
    exact metadata.2.1
  · intro miss
    have oldMiss : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none:=by
      cases cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id) with
      | none=>rfl
      | some base=>have hit:=preserved id base cached;rw [miss] at hit;cases hit
    by_cases same : id=sourceId
    · subst id
      obtain ⟨base,cached⟩:=sourceCached
      rw [oldMiss] at cached
      cases cached
    · have oldAlignment:=metadata.2.2 oldMiss
      constructor
      · intro oldEntry present
        exact oldAlignment.1 oldEntry ((liveOther same).symm.trans present)
      · intro descriptor present
        rw [memoryEq] at present
        exact oldAlignment.2 descriptor present
end DuplicatePrefix.CurrentCallConversionTargetMetadataFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionTargetMetadataFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved source-install relocation metadata dependency {dependency}"
