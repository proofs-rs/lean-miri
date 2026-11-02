import duplicate_prefix.CurrentCallRootPhysicalWindow
namespace DuplicatePrefix.CurrentCallScalarTreeWindow
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A literal tree-only row replacement preserves original Bool storage and pointer geometry. -/
theorem replace {before final : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (window : CurrentCallBoolScalarWrite.Window before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (addresses : final.user.addresses = before.user.addresses)
    (memory : final.memory.live = (before.memory.live.filter (fun row => row.1 != id)).push
      (id,{entry with allocation := entry.allocation.setExtra tree})) :
    ∃ next : CurrentCallBoolScalarWrite.Window final place,
      next.pointer=window.pointer ∧ next.id=window.id ∧ next.offset=window.offset ∧
      CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  have transported := CurrentCallBoolWindow.replace_binding before final window.pointer window.id window.offset.toNat 1
    binding id entry {entry with allocation:=entry.allocation.setExtra tree} live rfl rfl addresses memory
  by_cases same : id=window.id
  · subst id
    have entryEq : entry=window.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans window.live))).2
    subst entry
    let next : CurrentCallBoolScalarWrite.Window final place := {window with
      entry := {window.entry with allocation:=window.entry.allocation.setExtra tree}
      live := by rw [memory];exact MemoryCopyBridge.live_lookup_replaced before.memory window.id _
      cachedBase := by rw [addresses];exact window.cachedBase
      size := window.size
      bytes := window.bytes
      mutable := window.mutable
      maskValid := window.maskValid
      maskLength := window.maskLength
      pointerBounds := window.pointerBounds}
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
end DuplicatePrefix.CurrentCallScalarTreeWindow
