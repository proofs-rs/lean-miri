import duplicate_prefix.ConcreteEmptyRootArguments
import duplicate_prefix.RootArgumentsTwo
namespace DuplicatePrefix.NonliveEmptyRootArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem body
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
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
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag) n).frame
        (ConcreteEmptyRootCopy.nonliveMachine machine global fresh)) := by
  let l1 := firstLive root
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let d1 := ConcreteEmptyRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag
  let m1 := ConcreteEmptyRootCopy.nonliveMachine machine global fresh
  have live1 : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by
    simp [l1,firstLive,live,write,i1]
  have cached1 : (l1.frame.locals[1]'(l1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp [l1,firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,i1]
  have copy1 := ConcreteEmptyRootCopy.copy_nonlive options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id parentTag global base offset nonzero frames l1.frame machine
    1 (l1.valid i1) .uninit live1 cached1 l1.noClocks ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh info allocationInfo nonlive
    metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView (by simp)
  have nextDead : (d1.frame.locals[2]'(d1.valid i2)).value = .dead := by
    simpa [d1,ConcreteEmptyRootArguments.firstDone,ConcreteEmptyRootArguments.protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using dead2
  have nextCache : (d1.frame.locals[2]'(d1.valid i2)).layout = none := by
    simpa [d1,ConcreteEmptyRootArguments.firstDone,ConcreteEmptyRootArguments.protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using cache2
  exact RootArgumentsTwo.body options limits remaining span debugOff validityFuel validationEq frames root d1 machine m1
    value n dead1 cache1 nextDead nextCache ghost shallow ghost shallow copy1
end
end DuplicatePrefix.NonliveEmptyRootArguments
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.NonliveEmptyRootArguments.body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved nonlive empty root arguments dependency {dependency}"
