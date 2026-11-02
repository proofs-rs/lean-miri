import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.CurrentCallBoolScalarWrite
import duplicate_prefix.S04ReturnProvenanceClear
import duplicate_prefix.StackPopRelease
import duplicate_prefix.DuplicatePrefixPhysicalContexts
import duplicate_prefix.CandidateCurrentWindowPointerChecks
namespace DuplicatePrefix.CurrentCallRootPhysicalWindow
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

/-- Physical original-Bool write prerequisites after real entry writeUninit;
initialization and full post-clear provenance well-formedness are unnecessary. -/
theorem of_entry {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    (out : CurrentCallEntry.Output input #[]) (count : UInt64) (facts : CurrentCallEntry.Facts out count) :
    ∃ window : CurrentCallBoolScalarWrite.Window (out.machine count) place,
      window.id = call.returnId ∧ window.pointer = out.source.base.raw.returnPointer.value ∧
      window.offset = UInt64.ofNat call.returnOffset ∧
      CandidateCallBindings.WindowBinding (out.machine count) window.pointer window.id window.offset.toNat 1 := by
  let physical := out.physical
  let tree := (CurrentCallBoolProtection.writeResult out.borrowed).tree
  have mutation : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
      (Size.ofBytes 8) (physical.entry.allocation.setExtra tree) = .ok () out.updated := by
    simpa only [Allocation.setExtra,Allocation.mapExtra] using facts.mutation
  obtain ⟨length,bytes,mutable,extra,maskWF,maskLen,clear⟩ := CurrentCallBoolWindow.mutation_metadata physical tree out.updated mutation
  have memory : (out.machine count).memory.live = ((CurrentCallBoolWindow.after out.source).memory.live.filter
      (fun row => row.1 != physical.id)).push (physical.id,{physical.entry with allocation := out.updated}) :=
    congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice (CurrentCallBoolWindow.after out.source).memory physical.id
      {physical.entry with allocation := physical.entry.allocation.setExtra out.borrowed.output.child.tree}
      {physical.entry with allocation := out.updated})
  have live : (out.machine count).memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id,{physical.entry with allocation := out.updated}) := by
    rw [memory]
    exact MemoryCopyBridge.live_lookup_replaced (CurrentCallBoolWindow.after out.source).memory physical.id _
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1 (by
    have fits := physical.capacity.toNat_lt
    have bounds := physical.bounds
    simpa only [Size.ofBytes,UInt64.toNat_one] using (show physical.offset.toNat+1<2^64 by omega))
  have subset := S04ReturnProvenanceClear.clear_pointer_subset physical.entry.allocation.provenanceMap out.updated.provenanceMap
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) _
    (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree)) endpoint clear
  let window : CurrentCallBoolScalarWrite.Window (out.machine count) place := {
    pointer := physical.pointer, physicalPointer := physical.physicalPointer,layout := physical.layout,aligned := physical.aligned
    id := physical.id,entry := {physical.entry with allocation := out.updated},base := physical.base,offset := physical.offset,capacity := physical.capacity
    live := live,cachedBase := physical.cachedBase,pointerAddress := physical.pointerAddress,bounds := physical.bounds
    size := bytes.trans physical.size,bytes := length.trans physical.bytes,mutable := mutable,maskValid := maskWF
    maskLength := maskLen.trans (bytes.trans physical.size),pointerBounds := by
      intro row member
      rw [length]
      exact ProvenanceCopy.WellFormed.pointerBounds physical.provenanceMap row (subset row member) }
  obtain ⟨_,_,_,_,binding⟩ := CurrentCallBoolWindow.after_source options limits remaining span out.ctx
    (CurrentCallPush.preparedMachine before #[]) tracker argument len place call data (CurrentCallPush.prepared_input input #[])
    #[] (CurrentCallEntry.sourceInputFrame input #[]) {} out.source
  have offsetBound : call.returnOffset < 2^64 := by
    obtain ⟨entry,base,_,_,_,room,bounds,_⟩ := binding
    omega
  have normalized : physical.offset.toNat = call.returnOffset := by
    rw [facts.returnOffset]
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetBound]
  have binding' : CandidateCallBindings.WindowBinding (CurrentCallBoolWindow.after out.source) physical.pointer physical.id physical.offset.toNat 1 := by
    rw [facts.returnPointer,facts.returnId,normalized]
    exact binding
  have finalBinding := CurrentCallBoolWindow.replace_binding (CurrentCallBoolWindow.after out.source) (out.machine count)
    physical.pointer physical.id physical.offset.toNat 1 binding' physical.id physical.entry {physical.entry with allocation := out.updated}
    physical.live length bytes rfl memory
  exact ⟨window,facts.returnId,facts.returnPointer,facts.returnOffset,finalBinding⟩
/-- Accounting, thread relevance and whole-frame protector removal preserve
all scalar physical fields when live memory and address selectors agree. -/
theorem view {before final : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (window : CurrentCallBoolScalarWrite.Window before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (addresses : final.user.addresses = before.user.addresses) (memory : final.memory.live = before.memory.live) :
    ∃ next : CurrentCallBoolScalarWrite.Window final place, next.pointer = window.pointer ∧ next.id = window.id ∧ next.offset = window.offset ∧
      next.entry = window.entry ∧ CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  let next : CurrentCallBoolScalarWrite.Window final place := {window with
    live := by rw [memory];exact window.live
    cachedBase := by rw [addresses];exact window.cachedBase}
  refine ⟨next,rfl,rfl,rfl,rfl,?_⟩
  obtain ⟨entry,base,live,cached,rest⟩ := binding
  exact ⟨entry,base,by rw [memory];exact live,by rw [addresses];exact cached,rest.1,rest.2.1,rest.2.2.1,rest.2.2.2.1,rest.2.2.2.2.1,
    by rw [addresses];exact rest.2.2.2.2.2⟩

/-- Exact release filter/push transports the original Bool scalar window for
both equal and distinct allocation IDs. -/
theorem tree_update {before final : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (window : CurrentCallBoolScalarWrite.Window before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (addresses : final.user.addresses = before.user.addresses)
    (memory : final.memory.live = (StackPopRelease.commitTree before.memory id entry tree).live) :
    ∃ next : CurrentCallBoolScalarWrite.Window final place, next.pointer = window.pointer ∧ next.id = window.id ∧ next.offset = window.offset ∧
      CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  have finalBinding := CurrentCallBoolWindow.replace_binding before final window.pointer window.id window.offset.toNat 1 binding id entry
    {entry with allocation := entry.allocation.setExtra tree} live rfl rfl addresses memory
  by_cases same : id = window.id
  · subst id
    have entryEq : entry = window.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans window.live))).2
    subst entry
    let next : CurrentCallBoolScalarWrite.Window final place := {window with
      entry := {window.entry with allocation := window.entry.allocation.setExtra tree}
      live := by rw [memory];exact StackPopRelease.lookup_commit_same before.memory window.id window.entry tree
      cachedBase := by rw [addresses];exact window.cachedBase}
    exact ⟨next,rfl,rfl,rfl,finalBinding⟩
  · let next : CurrentCallBoolScalarWrite.Window final place := {window with
      live := by rw [memory];exact StackPopRelease.lookup_commit_other before.memory id window.id entry window.entry tree (Ne.symm same) window.live
      cachedBase := by rw [addresses];exact window.cachedBase}
    exact ⟨next,rfl,rfl,rfl,finalBinding⟩

/-- The actual pre-store resolver is derived from current original-pointer
geometry, including the real wildcard inverse map and exposure check. -/
theorem resolve (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (place : MPlaceTy Provenance) (window : CurrentCallBoolScalarWrite.Window state.machine place)
    (binding : CandidateCallBindings.WindowBinding state.machine window.pointer window.id window.offset.toNat 1) :
    (PreparedContracts.actualConfig options () (remaining+1) span).access.resolvePointer state.machine.memory
      window.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨window.id,Size.ofBytes window.offset,S04ReturnBorrowBridge.extra window.pointer.provenance⟩) state.machine := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.writeContext
  rw [contexts.outerAccessEq,show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
  obtain ⟨entry,base,live,cached,_,_,_,_,_,provenanceBinding⟩ := binding
  have entryEq : entry = window.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans window.live))).2
  subst entry
  have baseEq : base = window.base := congrArg (fun row => row.address) (Option.some.inj (cached.symm.trans window.cachedBase))
  subst base
  have off : window.pointer.offset = Size.ofBytes (window.base+window.offset) := by
    cases h : window.pointer.offset
    simpa [h,Size.ofBytes] using congrArg Size.ofBytes window.pointerAddress
  have pointerEq : window.pointer.withOptionalProvenance = Pointer.new (some window.pointer.provenance) (Size.ofBytes (window.base+window.offset)) := by
    change (⟨window.pointer.offset,some window.pointer.provenance⟩ : Pointer (Option Provenance)) = _
    rw [off];rfl
  rw [pointerEq]
  cases prov : window.pointer.provenance with
  | concrete id tag =>
    have same : id = window.id := by simpa only [prov] using provenanceBinding
    subst id
    have resolved := MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine
      window.id tag window.base window.offset (Int.ofNat (1 : UInt64).toNat) contexts.width (by decide) (by decide) window.cachedBase
    simpa only [prov,S04ReturnBorrowBridge.extra] using resolved
  | wildcard =>
    obtain ⟨mode,exposed,geometry⟩ := (show state.machine.user.addresses.provenanceMode ≠ .strict ∧
      state.machine.user.addresses.exposed.contains window.id = true ∧
      WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap window.pointer.offset.bytes window.base window.id window.entry.allocation.byteSize
      from by simpa only [prov] using provenanceBinding)
    have geometry' : WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap (window.base+window.offset) window.base window.id window.entry.allocation.byteSize := by
      rw [←window.pointerAddress];exact geometry
    have resolved := GeneralBorrowPositiveWildcardWindowPointerChecks.resolve context.pointers state window.base window.offset 1 window.id window.entry
      geometry' contexts.width mode exposed window.cachedBase window.live (by decide)
    simpa only [prov,S04ReturnBorrowBridge.extra] using resolved

theorem bool_live {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    (out : CurrentCallEntry.Output input #[]) (count : UInt64) :
    (out.machine count).memory.live.find? (fun row => row.1 == out.physical.id) =
      some (out.physical.id,{out.physical.entry with allocation := out.updated}) := by
  have memory : (out.machine count).memory.live = ((CurrentCallBoolWindow.after out.source).memory.live.filter
      (fun row => row.1 != out.physical.id)).push (out.physical.id,{out.physical.entry with allocation := out.updated}) :=
    congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice (CurrentCallBoolWindow.after out.source).memory out.physical.id
      {out.physical.entry with allocation := out.physical.entry.allocation.setExtra out.borrowed.output.child.tree}
      {out.physical.entry with allocation := out.updated})
  rw [memory]
  exact MemoryCopyBridge.live_lookup_replaced (CurrentCallBoolWindow.after out.source).memory out.physical.id _

/-- Every actual release Plan changes borrow trees only, so the original
scalar window and wildcard geometry survive its entire sequential heap walk. -/
theorem plan (protections : ProtectedTags) (rows : List (AllocId × BorTag))
    (initialMemory finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (actual : StackPopRelease.Plan protections rows initialMemory finalMemory)
    (before final : DuplicatePrefixCallSpecification.Before) (memoryBefore : before.memory = initialMemory)
    (memoryAfter : final.memory = finalMemory) (addresses : final.user.addresses = before.user.addresses)
    (place : MPlaceTy Provenance) (window : CurrentCallBoolScalarWrite.Window before place)
    (binding : CandidateCallBindings.WindowBinding before window.pointer window.id window.offset.toNat 1) :
    ∃ next : CurrentCallBoolScalarWrite.Window final place, next.pointer = window.pointer ∧ next.id = window.id ∧ next.offset = window.offset ∧
      CandidateCallBindings.WindowBinding final next.pointer next.id next.offset.toNat 1 := by
  induction actual generalizing before final with
  | nil memory =>
    obtain ⟨next,pointer,id,offset,_,binding⟩ := view window binding addresses (by rw [memoryAfter,memoryBefore])
    exact ⟨next,pointer,id,offset,binding⟩
  | skip id tag info rest memory done lookup notLive tail ih =>
    exact ih before final memoryBefore memoryAfter addresses window binding
  | live id tag entry tree rest memory done present released tail ih =>
    let middle := {before with memory := StackPopRelease.commitTree before.memory id entry tree}
    obtain ⟨next,pointer,idEq,offset,bindingNext⟩ := tree_update window binding id entry tree (by rw [memoryBefore];exact present)
      (final := middle) rfl rfl
    obtain ⟨last,lastPointer,lastId,lastOffset,lastBinding⟩ := ih middle final (by simp only [middle,memoryBefore]) memoryAfter addresses next bindingNext
    exact ⟨last,lastPointer.trans pointer,lastId.trans idEq,lastOffset.trans offset,lastBinding⟩

end
end DuplicatePrefix.CurrentCallRootPhysicalWindow
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallRootPhysicalWindow." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved root physical window dependency {dependency}"
