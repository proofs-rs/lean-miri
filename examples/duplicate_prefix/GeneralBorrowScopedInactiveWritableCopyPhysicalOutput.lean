import duplicate_prefix.GeneralBorrowScopedInactiveWritableCopyRootGuardBody
namespace DuplicatePrefix.GeneralBorrowScopedInactiveWritableCopyPhysicalOutput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (input : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)
  (data : GeneralBorrowScopedInactiveWritableCopyRootGuardBody.CopyData options remaining span machine input.tracker sourcePointer destinationPointer n)
/-- The exact source-derived output of the complete physical copy invocation. -/
structure Output where
  result : Allocation Provenance BorrowTree
  finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (CopyRootOutput.caller caller input.valid) finalMachine)
  live : finalMachine.memory.live.find? (fun row => row.1 == data.id) = some (data.id,⟨data.kind,result⟩)
  bytes : result.byteSize = data.allocation.byteSize
  len : result.len = data.allocation.len
  tree : result.extra = ((data.allocation.extra.performBorrowAccessRange (.concrete data.tag) (Size.ofBytes data.offset) (Size.ofBytes n) .Read input.tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange (.concrete data.tag) (Size.ofBytes (data.offset+n)) (Size.ofBytes n) .Write input.tracker.global.protectedTags .VisitChildrenOfAccessed).tree
  snapshot : AllocationCopy.snapshot result = (AllocationCopy.snapshot data.allocation).extract 0 (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract data.offset.toNat (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract (data.offset+n+n).toNat data.allocation.len
  memory : finalMachine.memory = CopyHelperCall.memoryAfter machine.memory data.id data.kind result
  tracked : finalMachine.borrowTracker = some input.tracker
  race : finalMachine.dataRace = none
  ghost : finalMachine.user.payload.ghost = false
  shallow : finalMachine.user.payload.validation = .Shallow
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0
  fixed : finalMachine.threads.fixedScheduling = true
  addresses : finalMachine.user.addresses = machine.user.addresses
  types : finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types
  backend : finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend
  extras : finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras
  strong : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableAccessData.Data result.extra location input.tracker.global.protectedTags data.borrow.anchor data.borrow.selected data.borrow.head data.borrow.tail data.borrow.support))
        data.offset (data.offset+data.sliceLen) result.extra.locations
  well : result.extra.locations.WellFormed
  capacity : result.extra.locations.size = data.allocation.extra.locations.size
  active : ∃ activeThread, finalMachine.threads.activeThread? = some activeThread

/-- Executes actual root copy call, guards, helper, intrinsic, and return. -/
theorem run (statementFuel : limits.validation=input.fuel+1) (mode : input.tracker.retagMode=.Default) :
    Nonempty (Output options limits remaining span frames caller machine sourcePointer destinationPointer n input data) := by
  obtain ⟨result,finalMachine,trace,live,bytes,len,tree,snapshot,memory,tracked,race,ghost,shallow,unchecked,noGc,fixed,addresses,types,backend,extras,strong,well,capacity,active⟩ :=
    GeneralBorrowScopedInactiveWritableCopyRootGuardBody.complete options limits remaining span frames caller machine sourcePointer destinationPointer n input statementFuel mode data
  exact ⟨⟨result,finalMachine,trace,live,bytes,len,tree,snapshot,memory,tracked,race,ghost,shallow,unchecked,noGc,fixed,addresses,types,backend,extras,strong,well,capacity,active⟩⟩
end DuplicatePrefix.GeneralBorrowScopedInactiveWritableCopyPhysicalOutput
