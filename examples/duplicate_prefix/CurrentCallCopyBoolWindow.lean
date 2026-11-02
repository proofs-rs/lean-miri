import duplicate_prefix.CurrentCallRootPhysicalWindow
namespace DuplicatePrefix.CurrentCallCopyBoolWindow
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual source replacement preserves the original Bool pointer geometry,
using only physical copy output on the same allocation. -/
theorem replace {before final : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (window : CurrentCallBoolScalarWrite.Window before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (copied : Allocation Provenance BorrowTree)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (bytes : copied.byteSize = entry.allocation.byteSize) (length : copied.len = entry.allocation.len)
    (mutable : copied.mutability = .Mut) (maskWF : InitMaskCopy.WellFormed copied.initializationMask)
    (maskLen : copied.initializationMask.len = copied.byteSize)
    (pointers : ∀ row ∈ copied.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ copied.len)
    (addresses : final.user.addresses = before.user.addresses)
    (memory : final.memory.live = (before.memory.live.filter (fun row => row.1 != id)).push
      (id,{entry with allocation := copied})) :
    ∃ next : CurrentCallBoolScalarWrite.Window final place,
      next.pointer=window.pointer ∧ next.id=window.id ∧ next.offset=window.offset ∧
      CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  have transported := CurrentCallBoolWindow.replace_binding before final window.pointer window.id window.offset.toNat 1
    binding id entry {entry with allocation:=copied} live length bytes addresses memory
  by_cases same : id=window.id
  · subst id
    have entryEq : entry=window.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans window.live))).2
    subst entry
    let next : CurrentCallBoolScalarWrite.Window final place := {window with
      entry := {window.entry with allocation:=copied}
      live := by rw [memory];exact MemoryCopyBridge.live_lookup_replaced before.memory window.id _
      cachedBase := by rw [addresses];exact window.cachedBase
      size := bytes.trans window.size
      bytes := length.trans window.bytes
      mutable := mutable
      maskValid := maskWF
      maskLength := maskLen.trans (bytes.trans window.size)
      pointerBounds := pointers}
    exact ⟨next,rfl,rfl,rfl,transported⟩
  · let next : CurrentCallBoolScalarWrite.Window final place := {window with
      live := by
        rw [memory,Array.find?_push,Array.find?_filter]
        have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
            decide ((row.1 != id)=true ∧ (row.1 == window.id)=true)) = (fun row => row.1 == window.id) := by
          funext row
          by_cases hit : row.1=window.id
          · simp [hit,Ne.symm same]
          · simp [hit]
        rw [predicate,window.live];simp [same]
      cachedBase := by rw [addresses];exact window.cachedBase}
    exact ⟨next,rfl,rfl,rfl,transported⟩

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``replace) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved copied Bool-window dependency {dependency}"
end DuplicatePrefix.CurrentCallCopyBoolWindow
