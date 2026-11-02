import duplicate_prefix.AsMutEntry
import duplicate_prefix.AsMutDispatch
import duplicate_prefix.CallItemDispatch
namespace DuplicatePrefix.AsMutDispatchEntry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_dispatch
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (destId : MIR.LocalId) (destValid : destId < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[destId].value = .live (.immediate old))
    (destCached : caller.locals[destId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let before := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initFnCall (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (budget+1) ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,.Rust,some HelperCompilerFacts.asMutPtrAbi,
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩],false,destination,some 7,.Continue⟩ before =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let args : Array (FnArg Provenance) := #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩]
  have entry := AsMutEntry.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames caller machine tracker enabled
    defaultMode mask nextTag fresh destId destValid old destLive destCached callerClocks ghost shallow cachedAddress present race
    metadata notConstructed thread index current active top topPresent
  have find := AsMutDispatch.find_mir options limits (remaining+1) span state args destination (some 7) .Continue backend race
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () (remaining+1) span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    rfl
  have kind : HelperCompilerFacts.asMutPtrCall.callee.kind = .Item HelperCompilerFacts.asMutPtrCall.callee.defId := by
    with_unfolding_all rfl
  dsimp only
  apply CallItemDispatch.dispatch_one h _ state _ budget
  rw [CallItemDispatch.item_step h HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrCall.callee.defId
    HelperCompilerFacts.asMutPtrAbi args false destination (some 7) .Continue .Rust kind AsMutCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  rw [find]
  simp only [bind,EStateM.bind]
  dsimp only [h,args,destination,state]
  rw [entry]
  rfl

#print axioms actual_dispatch
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_dispatch) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut dispatch dependency {dependency}"
end
end DuplicatePrefix.AsMutDispatchEntry
