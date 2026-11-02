import duplicate_prefix.NonliveEmptyRootArguments
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.NonliveEmptyRootArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def resultMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩}
theorem scope
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo) (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n)) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame
        (resultMachine machine tracker fresh)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let entered := ScopedFrame.entered machine tracker .FnEntry
  let nextMachine := ConcreteEmptyRootCopy.nonliveMachine entered tracker.global fresh
  let nextTracker : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,.FnEntry⟩
  have body := NonliveEmptyRootArguments.body options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker.global base offset n nonzero frames root entered dead1 cache1 dead2 cache2
    ghost shallow cachedAddress info allocationInfo nonlive borrowFrame frameBorrow rfl fresh metadata notConstructed
  have result := ScopedFrame.changed_state
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n))
    (Storage.withCurrent frames root.frame machine)
    (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame nextMachine)
    tracker nextTracker .FnEntry (2,2) enabled rfl body
  exact result
end
end DuplicatePrefix.NonliveEmptyRootArgumentScope

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.NonliveEmptyRootArgumentScope.scope) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved nonlive empty root scoped argument dependency {dependency}"
