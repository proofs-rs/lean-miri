import duplicate_prefix.CurrentCallBoolWindow

namespace DuplicatePrefix.CurrentCallBoolTreeWindow
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentBoolUninitWrite
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual tree-only source installation preserves the full original Bool
physical window, including initialization and provenance metadata. The source
and Bool may share an allocation; no bytes or pointer geometry are changed. -/
theorem replace {before final : Before} {place : MPlaceTy Provenance}
    (window : PhysicalWindow before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (tree : BorrowTree)
    (addresses : final.user.addresses=before.user.addresses)
    (memory : final.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=entry.allocation.setExtra tree})) :
    ∃ next : PhysicalWindow final place,next.pointer=window.pointer ∧ next.id=window.id ∧ next.offset=window.offset ∧
      next.capacity=window.capacity ∧ CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  have transported := CurrentCallBoolWindow.replace_binding before final window.pointer window.id window.offset.toNat 1
    binding id entry {entry with allocation:=entry.allocation.setExtra tree} live rfl rfl addresses memory
  by_cases same : id=window.id
  · subst id
    have entryEq : entry=window.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans window.live))).2
    subst entry
    have present : final.memory.live.find? (fun row=>row.1==window.id)=
        some (window.id,{window.entry with allocation:=window.entry.allocation.setExtra tree}) := by
      rw [memory]
      exact MemoryCopyBridge.live_lookup_replaced before.memory window.id _
    let next := CurrentCallBoolWindow.tree_only window final tree addresses present
    exact ⟨next,rfl,rfl,rfl,rfl,transported⟩
  · have present : final.memory.live.find? (fun row=>row.1==window.id)=some (window.id,window.entry) := by
      rw [memory,Array.find?_push,Array.find?_filter]
      have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
          decide ((row.1!=id)=true ∧ (row.1==window.id)=true))=(fun row=>row.1==window.id) := by
        funext row
        by_cases hit : row.1=window.id
        · simp [hit,Ne.symm same]
        · simp [hit]
      rw [predicate,window.live]
      simp [same]
    let next : PhysicalWindow final place := {window with live:=present,cachedBase:=by rw [addresses];exact window.cachedBase}
    exact ⟨next,rfl,rfl,rfl,rfl,transported⟩

end DuplicatePrefix.CurrentCallBoolTreeWindow
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBoolTreeWindow" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Bool tree-window dependency {dependency}"
