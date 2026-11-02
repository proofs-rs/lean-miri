import duplicate_prefix.CurrentCallBoolTreeWindow
import duplicate_prefix.CurrentCallBoolProtection

namespace DuplicatePrefix.CurrentCallOtherAllocationWindow
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentBoolUninitWrite
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Replacing or materializing one ID leaves the first matching row for every
other ID unchanged. No initial live row for the replacement is required. -/
theorem lookup {α : Type} (rows : Array (AllocId × α)) (id other : AllocId) (value : α)
    (different : id≠other) :
    ((rows.filter (fun row=>row.1!=id)).push (id,value)).find? (fun row=>row.1==other)=
      rows.find? (fun row=>row.1==other) := by
  rw [Array.find?_push,Array.find?_filter]
  have predicate : (fun row : AllocId × α=>decide ((row.1!=id)=true ∧(row.1==other)=true))=
      (fun row=>row.1==other) := by
    funext row
    by_cases hit : row.1=other
    · simp [hit,Ne.symm different]
    · simp [hit]
  rw [predicate]
  cases found : rows.find? (fun row=>row.1==other) <;> simp [different]

/-- An actual other-ID heap installation preserves the original pointer
normalization, including wildcard inverse-map geometry. -/
theorem binding {before after : Before} {pointer : Pointer Provenance} {other offset length}
    (old : CandidateCallBindings.WindowBinding before pointer other offset length)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (different : id≠other)
    (memory : after.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push (id,entry))
    (addresses : after.user.addresses=before.user.addresses) :
    CandidateCallBindings.WindowBinding after pointer other offset length := by
  obtain ⟨oldEntry,base,live,cached,size,room,bounds,address,nonnull,provenance⟩:=old
  refine ⟨oldEntry,base,?_,?_,size,room,bounds,address,nonnull,?_⟩
  · rw [memory,lookup _ id other entry different];exact live
  · rw [addresses];exact cached
  · rw [addresses];exact provenance

/-- Materializing a distinct allocation preserves all Bool storage metadata;
only its actual live lookup and unchanged address cache need transport. -/
theorem physical {before after : Before} {place : MPlaceTy Provenance}
    (window : PhysicalWindow before place)
    (old : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (different : id≠window.id)
    (memory : after.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push (id,entry))
    (addresses : after.user.addresses=before.user.addresses) :
    ∃ next : PhysicalWindow after place,next.pointer=window.pointer ∧next.id=window.id ∧next.offset=window.offset ∧
      next.entry=window.entry ∧next.capacity=window.capacity ∧
      CandidateCallBindings.WindowBinding after next.pointer next.id next.offset.toNat 1 := by
  let next : PhysicalWindow after place := {window with
    live:=by rw [memory,lookup _ id window.id entry different];exact window.live
    cachedBase:=by rw [addresses];exact window.cachedBase}
  exact ⟨next,rfl,rfl,rfl,rfl,rfl,binding old id entry different memory addresses⟩

/-- The queried plain-memory profile row survives a distinct allocation's
extras insertion; unrelated registry rows and synchronization data are allowed. -/
theorem ready {before after : Before} {other offset length}
    (old : CurrentCallBoolProtection.WindowReady before other offset length)
    (id : AllocId) (extra : MemoryExtras.AllocationExtra Unit) (different : id≠other)
    (extras : after.user.payload.payload.user.runtime.extras.allocations=
      (before.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=id)).push (id,extra)) :
    CurrentCallBoolProtection.WindowReady after other offset length := by
  obtain ⟨sync,present,outside⟩:=old
  refine ⟨sync,?_,outside⟩
  rw [extras,lookup _ id other extra different]
  exact present

end DuplicatePrefix.CurrentCallOtherAllocationWindow
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallOtherAllocationWindow" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved other-allocation window dependency {dependency}"
