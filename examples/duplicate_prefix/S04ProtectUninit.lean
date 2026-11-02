import duplicate_prefix.S04ProtectUninitMetadata
import duplicate_prefix.S04ProtectUninitWrite

namespace DuplicatePrefix.S04ProtectUninit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open Miri.Input DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

/-- Exact installed state after protection and the uninitializing store. -/
def finished (before : Before) (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) : RootState :=
  let protectedState := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  {protectedState with machine := {protectedState.machine with memory :=
    {protectedState.machine.memory with live := ((protectedState.machine.memory.live.filter fun row => row.1 != input.id).push
      (input.id,{input.entry with allocation := updated}))}}}

/-- The configured return-destination protection: actual fresh protected retag
followed by the actual uninitializing write through that child. All premises
describe the original machine; the next Input, tree order, resources and access
completion are derived internally. The destination may occupy any valid byte
of a general allocation, including the allocation containing the argument.

The extras row/no weak buffer and local synchronization separation are explicit
initial metadata obligations, not fields silently added to Contract. -/
theorem invoke_concrete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat) :
    ∃ (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
      let after := finished before place input frames frame borrowFrame fresh tree updated
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) = .ok () after ∧
      after.machine.memory.live.find? (fun row => row.1 == input.id) =
        some (input.id,{input.entry with allocation := updated}) ∧
      updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      ∃ finalTracker, after.machine.borrowTracker = some finalTracker ∧
        DuplicatePrefixBorrowContract.RuntimeFacts updated.extra finalTracker.global ∧
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra ∧
        ∃ child selected maximum,
          updated.extra.indexOfTag input.tracker.global.nextPointerTag = some child ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra finalTracker.global.protectedTags
            (some child) selected maximum input.offset 1) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write input.offset (input.offset+1) := by
  obtain ⟨fresh,tree,retag,next,nextId,nextOffset,nextCapacity,nextTree,runtime,growth⟩ :=
    S04ReturnProtectionInput.invoke_concrete budget before tracker model place len input state resources
      tag concrete frames frame borrowFrame frameBorrow
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  have metadata := S04ProtectUninitMetadata.of_retag budget before tracker model place len input state resources
    tag concrete frames frame borrowFrame frameBorrow fresh tree retag
  have nextConcrete : next.pointer.provenance = .concrete next.id input.tracker.global.nextPointerTag := by
    have pointer := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) next.physicalPointer
    have encoded : some (.concrete input.id input.tracker.global.nextPointerTag) = some next.pointer.provenance := pointer
    rw [nextId]
    exact (Option.some.inj encoded).symm
  have nextEntry : next.entry = {input.entry with allocation := input.entry.allocation.setExtra tree} := by
    have present := next.live
    change (RetagEntry.updatedMemory before.memory input.id input.entry tree).live.find?
      (fun row => row.1 == next.id) = some (next.id,next.entry) at present
    rw [nextId] at present
    have known := MemoryCopyBridge.live_lookup_replaced before.memory input.id
      {input.entry with allocation := input.entry.allocation.setExtra tree}
    exact (congrArg Prod.snd (Option.some.inj (known.symm.trans present))).symm
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts next.entry.allocation.extra next.tracker.global := by
    rw [nextTree]
    exact runtime
  have nextExtras : current.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == next.id) = some (next.id,⟨none,sync⟩) := by
    rw [nextId]
    exact extras
  have nextOutside : ∀ row ∈ sync,
      row.1.bytes.toNat < next.offset.toNat ∨ next.offset.toNat + 1 ≤ row.1.bytes.toNat := by
    rw [nextOffset]
    exact outside
  obtain ⟨updated,write,extra,bytes,length,mutable,afterRuntime,afterTags,afterOrder,afterPositive,afterActivity⟩ := S04ProtectUninitWrite.from_current
    (options := options) (remaining := remaining) span current _ next nextRuntime (by rw [nextTree]; exact metadata.1)
    (by rw [nextTree]; exact metadata.2.1) (by rw [nextTree]; exact metadata.2.2.1)
    input.tracker.global.nextPointerTag nextConcrete model.noDataRace model.noBackend sync nextExtras nextOutside
  let after : RootState := {current with machine := {current.machine with memory :=
    {current.machine.memory with live := ((current.machine.memory.live.filter fun row => row.1 != next.id).push
      (next.id,{next.entry with allocation := updated}))}}}
  have afterEq : after = finished before place input frames frame borrowFrame fresh tree updated := by
    dsimp only [after,finished]
    rw [nextId,nextEntry]
  have configuredWrite : (config options remaining span).retag.writeUninit
      (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) current = .ok () after := by
    obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
    rw [ctx.construction]
    change (do
      let access ← ValidityMachine.scopedAccess (config options remaining span).access
      PlaceMachine.writeMemory access (fun _ => false) .uninit
        (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)) current = .ok () after
    have ghost : current.machine.user.payload.ghost = false := model.ghostOff
    have accessGhost : (config options remaining span).access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).accessEq]
      rfl
    have scopedResult := S04ProtectUninitWrite.scopedAccess_of_not_ghost
      (config options remaining span).access current accessGhost ghost
    simp only [bind,EStateM.bind,scopedResult]
    exact write
  refine ⟨fresh,tree,updated,?_⟩
  dsimp only
  rw [←afterEq]
  refine ⟨?_,?_,?_,?_,mutable,next.tracker,?_,?_,?_,?_⟩
  · unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,
      input.enabled,Option.isSome_some,↓reduceIte]
    erw [retag]
    exact configuredWrite
  · change ((current.machine.memory.live.filter fun row => row.1 != next.id).push
      (next.id,{next.entry with allocation := updated})).find? (fun row => row.1 == input.id) = _
    rw [nextId,MemoryCopyBridge.live_lookup_replaced,nextEntry]
  · simpa only [nextEntry,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using bytes
  · simpa only [nextEntry,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using length
  · exact next.enabled
  · rw [extra]
    exact afterRuntime
  · rw [extra]
    exact afterOrder
  · obtain ⟨child,tagged,active⟩ := metadata.2.2.2
    have binding := next.binding
    simp only [DuplicatePrefixReferenceInput.Binding,nextConcrete] at binding
    obtain ⟨_,anchor,source,anchorTag⟩ := binding
    have same : anchor = child := by
      rw [nextTree] at anchorTag
      exact Option.some.inj (anchorTag.symm.trans tagged)
    subst anchor
    refine ⟨child,next.selectedRoot,next.maximum,?_,?_,?_⟩
    · rw [extra]
      unfold BorrowTree.indexOfTag
      rw [afterTags]
      change next.entry.allocation.extra.indexOfTag _ = _
      rw [nextTree]
      exact tagged
    · rw [extra]
      simpa only [source,nextOffset] using afterPositive
    · rw [extra]
      have retained := afterActivity child (by simpa only [nextTree,nextOffset] using active)
      simpa only [nextOffset] using retained

end
end DuplicatePrefix.S04ProtectUninit
