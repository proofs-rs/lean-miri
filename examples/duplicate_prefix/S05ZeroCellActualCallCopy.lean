import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.S05CompletedCopyRootGuardBody
import duplicate_prefix.CanonicalCopyBound

/-! The fixed packet's actual copy call and normal helper return. Tree Borrows
completion is computed from the generated AsMut-return tree internally. This
execution adapter does not define caller validity or ordinary-input coverage. -/
namespace DuplicatePrefix.S05ZeroCellActualCallCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellActualCallRepaired
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

def sourcePointer (span : PreparedContracts.FixedSpanQuery) : Scalar Provenance :=
  Scalar.fromPointer (ActualReferenceContext.config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete sourceId PureTree.tag) (Size.ofBytes 4096))
def destinationPointer (span : PreparedContracts.FixedSpanQuery) : Scalar Provenance :=
  Scalar.fromPointer (ActualReferenceContext.config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete sourceId PureTree.tag) (Size.ofBytes 4097))

/-- The operation statuses required by the low-level continuation are proved
from fixed source data; none is a premise of this adapter. -/
theorem complete (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (input : CopyRootEntry.Input options limits remaining span frames caller machine
      (sourcePointer span) (destinationPointer span) 1)
    (tracker : input.tracker = copyTracker)
    (live : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,copyEntry))
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) =
      some (sourceId,⟨none,#[]⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩) :
    ∃ result finalMachine,
      SuccessfulTrace.Trace (ActualReferenceContext.config options (remaining+1) span) limits
        (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (CopyRootOutput.caller caller input.valid) finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,⟨copyEntry.kind,result⟩) ∧
      result.byteSize = Size.ofBytes 2 ∧ result.len = 2 ∧ result.extra = PureTree.write.tree ∧
      finalMachine.memory = CopyHelperCall.memoryAfter machine.memory sourceId copyEntry.kind result ∧
      finalMachine.borrowTracker = some copyTracker ∧
      finalMachine.dataRace = none ∧ finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((ActualReferenceContext.config options (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.threads.fixedScheduling = true ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by
  let data : S05CompletedCopyRootGuardBody.CopyData options remaining span machine input.tracker
      (sourcePointer span) (destinationPointer span) 1 := {
    id := sourceId, tag := PureTree.tag, base := 4096, offset := 0, sliceLen := 2,
    kind := copyEntry.kind, allocation := copyEntry.allocation,
    positive := by decide, sliceBounds := by change 0+2 ≤ 2; decide,
    copyBounds := by decide, storage := by rfl,
    maskValid := by cbv, maskLen := by rfl, initialized := by cbv,
    valid := by
      change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 2
      constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers],
    storageFits := by change 2+64 < 18446744073709551616; decide,
    mutable := by rfl, extras := extras, live := live, cached := cached,
    readValid := by simpa only [tracker,copyEntry,Allocation.setExtra,Allocation.mapExtra,copyTracker,PureTree.held,PureTree.read,Size.ZERO,Size.ofBytes,UInt64.zero_add] using PureTree.read_completed,
    writeValid := by simpa only [tracker,copyEntry,Allocation.setExtra,Allocation.mapExtra,copyTracker,PureTree.held,PureTree.write,PureTree.read,Size.ZERO,Size.ofBytes,UInt64.zero_add] using PureTree.write_completed,
    bounded := by rw [CanonicalCopyBound.actual_maximum]; decide,
    source := by simp only [sourcePointer,UInt64.add_zero],
    destination := by simp only [destinationPointer]; rfl }
  obtain ⟨result,finalMachine,trace,lookup,bytes,len,tree,_,memory,tracked,race,ghost,shallow,
    unchecked,noGc,fixed,addresses,types,backend,extras,active⟩ :=
    S05CompletedCopyRootGuardBody.complete options limits remaining span frames caller machine
      (sourcePointer span) (destinationPointer span) 1 input input.validationFuel
      (by rw [tracker];rfl) data
  exact ⟨result,finalMachine,trace,lookup,bytes,len,by simpa only [data,tracker,copyEntry,Allocation.setExtra,Allocation.mapExtra,copyTracker,PureTree.held,PureTree.write,PureTree.read,Size.ZERO,Size.ofBytes,UInt64.zero_add] using tree,memory,by simpa only [tracker] using tracked,
    race,ghost,shallow,unchecked,noGc,fixed,addresses,types,backend,extras,active⟩

end
end DuplicatePrefix.S05ZeroCellActualCallCopy
