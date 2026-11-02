import duplicate_prefix.S05DiagnosticFnEntryArgument
import duplicate_prefix.PositiveRootArguments
namespace DuplicatePrefix.S05DiagnosticRootArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def changedMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (parentTag : BorTag) :=
  let tracker : MachineHooks.BorrowState := ⟨global,.FnEntry⟩
  {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) global.nextPointerTag with
    memory := RetagEntry.updatedMemory machine.memory id entry
      (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}

/-- Both actual typed argument passes for the six-node diagnostic. This does not
execute destination registration, finish the call frame, or assert whole-call safety. -/
theorem body
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base n : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
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
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (tree : entry.allocation.extra = S05DiagnosticFnEntryRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 6)
    (nextEq : global.nextPointerTag = S05DiagnosticFnEntryRead.tag 8)
    (protectedEq : global.protectedTags = ({} : ProtectedTags))
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second n) (Storage.withCurrent frames root.frame machine) =
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag) n).frame
        (changedMachine machine global fresh id entry parentTag)) := by
  let l1 := firstLive root
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
  let d1 := PositiveRootArguments.firstDone root adjusted borrowFrame id global.nextPointerTag
  let m1 := changedMachine machine global fresh id entry parentTag
  have live1 : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by
    simp [l1,firstLive,live,write,i1]
  have cached1 : (l1.frame.locals[1]'(l1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp [l1,firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,i1]
  have copyRaw := S05DiagnosticFnEntryArgument.copy_argument options limits remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base 0 2 parentTag (by decide)
    (by simpa using nonzero) (by decide) (by simpa using bounds) frames l1.frame machine
    ⟨global,.FnEntry⟩ enabled rfl borrowFrame frameBorrow fresh tree parentEq rfl rfl nextEq protectedEq
    1 (l1.valid i1) .uninit live1 cached1 l1.noClocks ghost shallow cachedAddress present race metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView (by simp)
  have copy1 : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size l1.frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames l1.frame machine) = .ok () (Storage.withCurrent frames d1.frame m1) := by
    simpa [value,adjusted,d1,m1,l1,changedMachine,PositiveRootArguments.firstDone,protectedRoot,
      S05DiagnosticFnEntryArgument.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using copyRaw
  have nextDead : (d1.frame.locals[2]'(d1.valid i2)).value = .dead := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using dead2
  have nextCache : (d1.frame.locals[2]'(d1.valid i2)).layout = none := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using cache2
  exact RootArgumentsTwo.body options limits remaining span debugOff validityFuel validationEq frames root d1 machine m1
    value n dead1 cache1 nextDead nextCache ghost shallow ghost shallow copy1
#print axioms body
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticRootArguments." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved diagnostic root argument dependency {dependency}"
end
end DuplicatePrefix.S05DiagnosticRootArguments
