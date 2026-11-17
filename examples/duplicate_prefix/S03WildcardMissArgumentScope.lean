import duplicate_prefix.S03WildcardMissArguments
import duplicate_prefix.CallArgumentStages
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.S03WildcardMissArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts RootFrameData S03WildcardMissArguments
theorem arguments_in_scope (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validityEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra)) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (target : TargetDataLayout)
    (targetEq : target = (ActualReferenceContext.config options remaining span).access.runtime.base)
    (address n : UInt64) (nonzero : address ≠ 0)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        (first target address) (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (result root target address n).frame (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)) := by
  let selected : MachineHooks.BorrowState := {tracker with retagMode := .FnEntry}
  let entered := {machine with borrowTracker := some selected}
  have hb := S03WildcardMissArguments.body options limits remaining span cmp precise implicitWrites debug dynamicFuel validityFuel
    dynamicEq validityEq frames root entered target targetEq address n nonzero dead1 cache1 dead2 cache2 ghost shallow selected rfl rfl fresh addressMode miss metadata notConstructed
  have hs := CallArgumentStages.with_retag_mode_updated .FnEntry
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (first target address) (second n))
    (Storage.withCurrent frames root.frame machine)
    (Storage.withCurrent frames (result root target address n).frame (ReferenceBorrowDriver.allocatedMachine entered selected fresh))
    tracker (ReferenceBorrowDriver.allocatedTracker selected fresh) (2,2) enabled hb rfl
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  simpa only [Storage.withCurrent, ReferenceBorrowDriver.allocatedMachine, ReferenceBorrowDriver.allocatedTracker, selected, entered] using hs
end DuplicatePrefix.S03WildcardMissArgumentScope
