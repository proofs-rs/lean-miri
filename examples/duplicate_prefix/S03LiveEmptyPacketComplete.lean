import duplicate_prefix.S03LiveEmptyPacket
import duplicate_prefix.S03EmptyPositiveReturnBounds
import duplicate_prefix.S03ZeroCountBodyBounds

namespace DuplicatePrefix.S03LiveEmptyPacketComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Every-count body and original Return from the packet produced by actual
live empty initialization. Concrete and wildcard initial argument branches
share this endpoint after their real FnEntry creates the concrete zero tag. -/
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (machine : Before)
    (place : MPlaceTy Provenance) (address count : UInt64)
    (packet : S03LiveEmptyInstalledPacket.Packet options remaining span frame machine place address count)
    (nonnull : address ≠ 0) (validityFuel dynamicFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (dispatchEq : limits.callDispatch = budget+1)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (debugOff : options.place.debugAssertions = false)
    (validationEq : options.limits.validation = validityFuel+1) (source : PreparedContracts.SourceComparator) :
    let cfg := config options (remaining+1) span
    let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,limits,fun _ _ => True⟩
    ∃ done,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine) done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn context 1 (Storage.withCurrent #[] frame machine) ∧
      CallSafety.NoUBBeforeReturn context 1 (Storage.withCurrent #[] frame machine) := by
  by_cases nonzero : count = 0
  · subst count
    obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03ZeroCountBodyBounds.complete options limits remaining span frame machine
      packet.tracker packet.borrowFrame packet.defaultMode packet.enabled packet.frameTracked place packet.destination
      packet.returnTag packet.child packet.selected packet.maximum packet.returnNode packet.argument
      packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden packet.hiddenFrame
      packet.runtime packet.positive packet.distinct (fun _ _ => packet.order) (by have room:=packet.headroom;omega) packet.activity
      packet.thread packet.active packet.race packet.backend packet.ghost packet.shallow
      #[] packet.extras (by simp) validityFuel debugOff validationEq source
      packet.sourceBody packet.identity packet.callee packet.location packet.frameSize
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨2,by decide⟩))
      packet.noLocalClocks packet.returnPlace packet.continuation packet.immediateLocals packet.varargs
      packet.unchecked packet.noGc packet.fixed
    exact ⟨done,trace,terminal,empty,noErrors,noUb⟩
  · let argumentOffset := address-packet.destination.base
    have addressEq : packet.destination.base+argumentOffset=address := by
      change packet.destination.base+(address-packet.destination.base)=address
      rw [UInt64.add_comm,UInt64.sub_add_cancel]
    have unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩ := by
      intro id valid lower upper
      have bounded : id < 25 := by rw [←packet.frameSize];exact valid
      have slot := packet.slots ⟨id,bounded⟩
      simpa only [Fin.val_mk,show ¬(14=id ∨ 13=id ∨ 6=id ∨ 0=id) by omega,
        show ¬2=id by omega,show ¬1=id by omega,↓reduceIte] using slot
    obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03EmptyPositiveReturnBounds.complete options limits remaining span frame machine
      packet.tracker packet.borrowFrame packet.defaultMode packet.enabled packet.frameTracked place packet.destination
      packet.returnTag packet.child packet.selected packet.maximum packet.returnNode packet.zeroTag packet.zeroIndex packet.zero packet.owned
      packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden packet.hiddenFrame
      packet.runtime packet.positive packet.distinct (fun _ _ => packet.order) packet.headroom packet.activity
      packet.thread packet.active packet.topZero packet.race packet.backend packet.ghost packet.shallow
      #[] packet.extras (by simp) validityFuel dynamicFuel budget dynamicEq dispatchEq
      precise implicitWrites cmp packet.fresh packet.tagRoomNext packet.metadata packet.notConstructed
      debugOff validationEq source
      packet.sourceBody packet.identity packet.callee packet.location packet.frameSize
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨3,by decide⟩))
      argumentOffset count (by rw [addressEq];exact nonnull) nonzero
      (by simpa [addressEq,ActualReferenceContext.config,CanonicalConfigFacts.actual_access_runtime] using
        congrArg (fun row => row.value) (packet.slots ⟨1,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨1,by decide⟩)) unused
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨13,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨13,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (packet.slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (packet.slots ⟨2,by decide⟩))
      packet.noLocalClocks packet.returnPlace packet.continuation packet.immediateLocals packet.varargs
      packet.unchecked packet.noGc packet.fixed
    exact ⟨done,trace,terminal,empty,noErrors,noUb⟩

end
end DuplicatePrefix.S03LiveEmptyPacketComplete
