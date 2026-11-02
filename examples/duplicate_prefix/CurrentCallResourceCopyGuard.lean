import duplicate_prefix.CurrentCallResourceCopyAccess
import duplicate_prefix.CurrentCallResourceEntrySourceStorage
import duplicate_prefix.CurrentCallCopyGuardReturn
namespace DuplicatePrefix.CurrentCallResourceCopyGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (ready : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)
/-- Actual guard/copy/return from current raw resources and initialized storage.
Both borrow-access statuses are derived inside this theorem. -/
theorem run {data owner id offset sliceLen}
    (W : UniformWindow machine ready.tracker data owner id offset.toNat sliceLen.toNat .mut)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (allocation : entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra ready.tracker.global)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : W.pointer.value.provenance=.concrete id tag)
    (storage : CurrentCallResourceEntrySourceStorage.Data entry.allocation offset sliceLen)
    (profile : CurrentCallBoolProtection.WindowReady machine id offset.toNat sliceLen.toNat)
    (base : UInt64)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (positive : (0 : UInt64)<n) (within : n≤sliceLen/2)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (mode : ready.tracker.retagMode=.Default)
    (bounded : n≤(config options (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceValue : sourcePointer=Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (destinationValue : destinationPointer=Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))) :
    let readAccess := entry.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes n)
      .Read ready.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n)
      .Write ready.tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ guardMachine copied finalMachine,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (CurrentCallCopyGuardReturn.returnedFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine guardMachine ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨entry.kind,copied⟩) ∧
      copied.byteSize = entry.allocation.byteSize ∧ copied.len = entry.allocation.len ∧ copied.extra = writeAccess.tree ∧
      AllocationCopy.snapshot copied = (AllocationCopy.snapshot entry.allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot entry.allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot entry.allocation).extract (offset+n+n).toNat entry.allocation.len ∧
      S02SameDestinationAcceptedCopyPhysical.Physical copied ∧
      finalMachine.memory = (CanonicalCopy.replaceAllocation (Storage.withCurrent frames caller machine) id entry.kind copied).machine.memory ∧
      finalMachine.borrowTracker = some ready.tracker ∧
      finalMachine.user = (CopyHelperClock.advance options remaining span
        (CopyHelperClock.advance options remaining span (CopyHelperClock.advance options remaining span guardMachine))).user ∧
      finalMachine.dataRace = machine.dataRace ∧ finalMachine.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  have bounds : offset.toNat+sliceLen.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
    rw [W.issued.capability.treeExtent,←allocation]
    exact storage.slice.bounds
  have access := CurrentCallResourceCopyAccess.run W entry live allocation runtime distinct short tag concrete n positive within bounds
  have numeric := PositiveRootCopyBounds.guarded sliceLen n offset entry.allocation.byteSize.bytes within storage.slice.bounds
  have fits : offset.toNat+sliceLen.toNat<2^64 := Nat.lt_of_le_of_lt storage.slice.bounds entry.allocation.byteSize.bytes.toNat_lt
  have middle : (offset+n).toNat=offset.toNat+n.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : offset.toNat+n.toNat<2^64)]
  have readReady := profile.subrange offset.toNat n.toNat (Nat.le_refl _) (by omega)
  have writeReady := profile.subrange (offset+n).toNat n.toNat (by omega) (by omega)
  have initialized := DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ n storage.slice within
  have first := access.1
  have second := access.2.1
  rw [←allocation] at first second
  exact CurrentCallCopyGuardReturn.run options limits remaining span frames caller machine sourcePointer destinationPointer n ready
    statementFuel statementEq mode id tag base offset sliceLen entry.kind entry.allocation positive storage.slice.bounds numeric.2.1
    storage.storage storage.slice.maskValid storage.slice.maskLength initialized storage.provenance storage.storageFits storage.mutable
    readReady writeReady live cached first second bounded sourceValue destinationValue
end
end DuplicatePrefix.CurrentCallResourceCopyGuard
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyGuard" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved current resource copy guard dependency {dependency}"
