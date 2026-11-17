import duplicate_prefix.S03SeparateWildcardLivePacket
import duplicate_prefix.S03SeparateWildcardPositiveReturn
import duplicate_prefix.S03ZeroCountBodyWildcard

namespace DuplicatePrefix.S03SeparateWildcardLivePacketComplete
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
    (packet : S03SeparateWildcardLivePacket.Packet options remaining span frame machine place address count)
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
    obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03ZeroCountBodyWildcard.complete options limits remaining span frame machine
      packet.tracker packet.borrowFrame packet.defaultMode packet.enabled packet.frameTracked place packet.destination
      packet.returnTag packet.child packet.returnNode packet.argument
      packet.returnTagged packet.returnPresent packet.returnSame packet.parentless packet.leaf packet.returnHidden packet.hiddenFrame
      packet.runtime packet.positive packet.distinct packet.order packet.exposed packet.notPrimary packet.short packet.activity
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
  · obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03SeparateWildcardPositiveReturn.complete options limits remaining span frame machine
      place address count packet nonnull nonzero validityFuel dynamicFuel budget dynamicEq dispatchEq precise implicitWrites cmp debugOff validationEq source
    exact ⟨done,trace,terminal,empty,noErrors,noUb⟩

end
end DuplicatePrefix.S03SeparateWildcardLivePacketComplete
