import duplicate_prefix.ConcreteEmptyRootArguments
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.ConcreteEmptyRootArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def resultMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (parent : BorTag) (capacity : UInt64) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    memory := RetagEntry.updatedMemory machine.memory id entry (TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag capacity)}
theorem scope
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset capacity n : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag) (rootUnprotected : tracker.global.protectedTags.contains parentTag = false)
    (tree : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity) (race : machine.dataRace = none)
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
        (resultMachine machine tracker fresh id entry parentTag capacity)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let entered := ScopedFrame.entered machine tracker .FnEntry
  let nextMachine := ConcreteEmptyRootCopy.changedMachine entered tracker.global fresh id entry parentTag capacity
  let nextTracker : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,.FnEntry⟩
  have body := ConcreteEmptyRootArguments.body options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker.global base offset capacity n nonzero entry frames root entered dead1 cache1 dead2 cache2
    ghost shallow cachedAddress present borrowFrame frameBorrow rfl fresh distinct tree metadata notConstructed
  have result := ScopedFrame.changed_state
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n))
    (Storage.withCurrent frames root.frame machine)
    (Storage.withCurrent frames (RootArgumentsTwo.result (firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n).frame nextMachine)
    tracker nextTracker .FnEntry (2,2) enabled rfl body
  exact result
end
end DuplicatePrefix.ConcreteEmptyRootArgumentScope
