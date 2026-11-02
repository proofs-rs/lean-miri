import duplicate_prefix.GeneralBorrowRawAsMutCopyLedger
import duplicate_prefix.GeneralBorrowRawAsMutCopyResources
import duplicate_prefix.GeneralBorrowRawCopyRootGuardBody
namespace DuplicatePrefix.GeneralBorrowRawAsMutActualCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- Form the real Copy MIR call and its CopyData internally from the derived
mutable suffix ledger and elementary initial allocation facts. -/
theorem from_suffix (packet : GeneralBorrowRawAsMutToCopy.Input)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (shape : PositiveRootSuccessProfile.FrameShape packet.caller caller (GeneralBorrowRawAsMutToCopy.pointer packet)
      (Scalar.fromPointer (PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).access.runtime.base
        (Pointer.new (Provenance.concrete packet.id packet.tag) (Size.ofBytes (packet.base+packet.offset+packet.count)))) packet.count)
    (memory : machine.memory = GeneralBorrowRawAsMutToCopy.memory packet)
    (tracked : machine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held packet))
    (outcome : GeneralBorrowRawAsMutCopyLedger.Outcome packet machine)
    (statementFuel : packet.limits.validation = packet.fuel+1)
    (storage : packet.entry.allocation.len = packet.entry.allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed packet.entry.allocation.initializationMask)
    (maskLen : packet.entry.allocation.initializationMask.len = packet.entry.allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn packet.entry.allocation.initializationMask (Size.ofBytes packet.offset) (Size.ofBytes (packet.offset+packet.count)))
    (valid : ProvenanceCopy.WellFormed packet.entry.allocation.provenanceMap packet.entry.allocation.len)
    (storageFits : packet.entry.allocation.len+64 < 18446744073709551616)
    (mutable : packet.entry.allocation.mutability = .Mut)
    (extras : packet.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.id) = some (packet.id,⟨none,#[]⟩))
    (bounded : packet.count ≤ (PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).projection.maxSizeOfVal.bytes) :
    let cfg := PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span
    let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
    let read := released.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes packet.offset)
      (Size.ofBytes packet.count) .Read (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes (packet.offset+packet.count))
      (Size.ofBytes packet.count) .Write (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg packet.limits (Storage.withCurrent #[] caller machine)
        (Storage.withCurrent #[] (CopyRootOutput.caller caller (by rw [shape.size];decide)) finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == packet.id) = some (packet.id,⟨packet.entry.kind,result⟩) ∧
      result.byteSize = packet.entry.allocation.byteSize ∧ result.len = packet.entry.allocation.len ∧
      result.extra = write.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot packet.entry.allocation).extract 0 (packet.offset+packet.count).toNat ++
        (AllocationCopy.snapshot packet.entry.allocation).extract packet.offset.toNat (packet.offset+packet.count).toNat ++
        (AllocationCopy.snapshot packet.entry.allocation).extract (packet.offset+packet.count+packet.count).toNat packet.entry.allocation.len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.extra (GeneralBorrowRawAsMutToCopy.held packet).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags
        (some packet.anchor) (some packet.selected) packet.maximum packet.offset packet.len) ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held packet) ∧
      finalMachine.memory = CopyHelperCall.memoryAfter machine.memory packet.id packet.entry.kind result ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.user.payload.payload.user.backend = .none ∧ finalMachine.user.payload.ghost = false ∧
      finalMachine.user.payload.validation = .Shallow ∧ finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      ∃ thread, finalMachine.threads.activeThread? = some thread := by
  let cfg := PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span
  let source := GeneralBorrowRawAsMutToCopy.pointer packet
  let destination := Scalar.fromPointer cfg.access.runtime.base
    (Pointer.new (Provenance.concrete packet.id packet.tag) (Size.ofBytes (packet.base+packet.offset+packet.count)))
  let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
  let allocation := packet.entry.allocation.setExtra released
  let held := GeneralBorrowRawAsMutToCopy.held packet
  obtain ⟨borrow,borrowAnchor,borrowSelected,borrowMaximum⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have valid18 : 18 < caller.locals.size := by rw [shape.size];decide
  have valid19 : 19 < caller.locals.size := by rw [shape.size];decide
  have valid21 : 21 < caller.locals.size := by rw [shape.size];decide
  have valid24 : 24 < caller.locals.size := by rw [shape.size];decide
  have cell18 : caller.locals[18] = ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid18).symm.trans shape.slot18)
  have cell19 : caller.locals[19] = ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid19).symm.trans shape.slot19)
  have cell21 : caller.locals[21] = ⟨.live (.immediate (.scalar destination)),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid21).symm.trans shape.slot21)
  have cell24 : caller.locals[24] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 packet.count)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid24).symm.trans shape.slot24)
  let input : CopyRootEntry.Input packet.options packet.limits packet.remaining packet.span #[] caller machine source destination packet.count := {
    debug := packet.debug,tracker := held,tracked := tracked,valid := valid18,old := .uninit,
    live := by rw [cell18],uncached := by rw [cell18],noClocks := by rw [shape.extra];exact packet.clocks,
    noRace := outcome.race,body := shape.body.trans packet.body,identity := shape.identity.trans packet.identity,
    callee := shape.callee.trans packet.callee,trackNone := shape.trackedCaller.trans packet.track,
    location := shape.location,fuel := packet.fuel,validationFuel := packet.validation,
    ghost := outcome.ghost,shallow := outcome.shallow,thread := packet.thread,active := outcome.active,
    top := packet.top,relevant := by rw [shape.extra];exact packet.relevant,
    budget := packet.budget,budgetEq := packet.dispatch,backend := outcome.backend,unchecked := outcome.unchecked,
    noGc := outcome.noGc,fixed := outcome.fixed,source := packet.source,cmp := packet.cmp,
    valid19 := valid19,valid21 := valid21,valid24 := valid24,
    live19 := by rw [cell19],cache19 := by rw [cell19],live21 := by rw [cell21],cache21 := by rw [cell21],
    live24 := by rw [cell24],cache24 := by rw [cell24] }
  let data : GeneralBorrowRawCopyRootGuardBody.CopyData packet.options packet.remaining packet.span machine held source destination packet.count := {
    id := packet.id,tag := packet.tag,base := packet.base,offset := packet.offset,sliceLen := packet.len,
    kind := packet.entry.kind,allocation := allocation,positive := packet.countPositive,
    sliceBounds := packet.bounds,copyBounds := borrow.twice,storage := storage,maskValid := maskValid,
    maskLen := maskLen,initialized := initialized,valid := valid,storageFits := storageFits,mutable := mutable,
    extras := by rw [outcome.extras];exact extras,
    live := by rw [memory];exact StackPopRelease.lookup_commit_same packet.machine.memory packet.id packet.entry released,
    cached := by rw [outcome.addresses];exact packet.cachedAddress,
    borrow := borrow,bounded := bounded,source := rfl,destination := by simp only [destination,UInt64.add_assoc];rfl }
  obtain ⟨result,finalMachine,trace,lookup,bytes,len,tree,snapshot,mem,tracker,race,ghost,shallow,unchecked,noGc,fixed,
    addresses,types,backend,extras,runtime,positive,well,capacity,active⟩ :=
    GeneralBorrowRawCopyRootGuardBody.complete packet.options packet.limits packet.remaining packet.span #[] caller machine source destination packet.count
      input statementFuel packet.mode data
  have positive' : Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra held.global.protectedTags
      (some packet.anchor) (some packet.selected) packet.maximum packet.offset packet.len) := by
    change Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra held.global.protectedTags
      (some borrow.anchor) (some borrow.selected) borrow.maximum packet.offset packet.len) at positive
    rw [borrowAnchor,borrowSelected,borrowMaximum] at positive
    exact positive
  exact ⟨result,finalMachine,trace,lookup,bytes,len,tree,snapshot,runtime,positive',tracker,mem,
    addresses,types,extras,backend.trans outcome.backend,ghost,shallow,race,fixed,unchecked,noGc,active⟩
end
end DuplicatePrefix.GeneralBorrowRawAsMutActualCopy
