import duplicate_prefix.S02AcceptedActualReturnReady
import duplicate_prefix.S02AcceptedDestinationCapabilityAfterCopy
import duplicate_prefix.S02DestinationPhysicalCopyTransport
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SeparateDestinationZeroExtras
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02AcceptedDestinationReturnParent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual accepted copy leaves a distinct concrete bool return place physically
valid and authorized for the final Return step. -/
theorem preserved
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (entry : CompilerFrameContext.ActualFrame)
    (initial post finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (originalTracker guardTracker : MachineHooks.BorrowState)
    (sourceRaw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra originalTracker.global)
    (guardTree : BorrowTree)
    (originalPacket : S02SeparateDestinationZeroCore.Packet entry initial place)
    (copyPacket : GeneralBorrowRawAsMutToCopy.Input)
    (copied : Allocation Provenance BorrowTree)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial))
    (sourceId : originalPacket.sourceId = reference.id)
    (tracked : initial.borrowTracker = some originalTracker)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra guardTree sourceRaw.selected originalTracker guardTracker)
    (postMemory : post.memory = RetagEntry.updatedMemory initial.memory reference.id sourceEntry guardTree)
    (postAddresses : post.user.addresses = initial.user.addresses)
    (copyMemory : finalMachine.memory = CopyHelperCall.memoryAfter post.memory reference.id sourceEntry.kind copied)
    (copyAddresses : finalMachine.user.addresses = post.user.addresses)
    (postExtras : post.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras)
    (copyExtras : finalMachine.user.payload.payload.user.runtime.extras = post.user.payload.payload.user.runtime.extras)
    (protections : (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags = guardTracker.global.protectedTags)
    (counter : guardTracker.global.nextPointerTag.value.toNat ≤
      (GeneralBorrowRawAsMutToCopy.held copyPacket).global.nextPointerTag.value.toNat) :
    ∃ destination : S03FinalReturnInputBounds.Destination finalMachine place,
      destination.id = originalPacket.destination.id ∧
      destination.entry = originalPacket.destination.entry ∧
      destination.offset = originalPacket.destination.offset ∧
      destination.parent = originalPacket.destination.parent ∧
      DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra
        (GeneralBorrowRawAsMutToCopy.held copyPacket).global ∧
      DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra
        (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags
        (some originalPacket.child) (some originalPacket.selected) originalPacket.maximum destination.offset 1 ∧
      finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
  obtain ⟨_,_,_,_,tickAddresses,_,_,_⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span initial
  let postDest := S02SeparateDestinationRejectedPhysicalTransport.after_body (post := post)
    options remaining span originalPacket.destination reference.id sourceEntry guardTree
    (by rw [←sourceId]; exact Ne.symm originalPacket.separate)
    (by simpa only [(S02SeparateDestinationTickLedger.preserved options remaining span initial).1]
      using postMemory)
    (by simpa only [tickAddresses] using postAddresses)
  have differentId : postDest.id ≠ reference.id := by
    have postDestId : postDest.id = originalPacket.destination.id := by
      simp only [postDest, S02SeparateDestinationRejectedPhysicalTransport.after_body,
        S02SeparateDestinationPhysicalTransport.other_source]
    rw [postDestId]
    rw [←sourceId]
    exact originalPacket.separate
  let destination := S02DestinationPhysicalCopyTransport.after_source_copy post finalMachine
    place postDest reference.id sourceEntry.kind copied differentId copyMemory copyAddresses
  have destId : destination.id = originalPacket.destination.id := by
    simpa only [destination,S02DestinationPhysicalCopyTransport.after_source_copy] using
      (show postDest.id = originalPacket.destination.id by
        simp only [postDest,S02SeparateDestinationRejectedPhysicalTransport.after_body,
          S02SeparateDestinationPhysicalTransport.other_source])
  have destEntry : destination.entry = originalPacket.destination.entry := rfl
  have destOffset : destination.offset = originalPacket.destination.offset := rfl
  have destParent : destination.parent = originalPacket.destination.parent := rfl
  obtain ⟨runtime,positive⟩ := S02AcceptedDestinationCapabilityAfterCopy.preserved
    originalPacket originalTracker guardTracker (GeneralBorrowRawAsMutToCopy.held copyPacket)
    tracked sourceEntry.allocation.extra guardTree sourceRaw.selected graph protections counter
  obtain ⟨extraFrame,extraMachine,extraActual,initialExtras⟩ :=
    S02SeparateDestinationZeroExtras.ready id tag address len count input nonempty different
      returnTag returnConcrete
  have sameExtra : Storage.withCurrent #[] extraFrame extraMachine = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (extraActual.symm.trans actual)).2
  have machineExtra := S02SeparateDestinationPacketJoin.same_machine extraFrame entry extraMachine initial sameExtra
  have physicalId : originalPacket.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination originalPacket.destination
      returnTag returnConcrete).1
  have extras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId,copyExtras,postExtras,physicalId,←machineExtra]
    exact initialExtras
  refine ⟨destination,destId,destEntry,destOffset,destParent,?_,?_,extras⟩
  · simpa only [destEntry] using runtime
  · simpa only [destEntry,destOffset] using positive

end
end DuplicatePrefix.S02AcceptedDestinationReturnParent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedDestinationReturnParent.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted destination Return dependency {dependency}"
