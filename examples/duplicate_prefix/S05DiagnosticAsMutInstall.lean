import duplicate_prefix.S05DiagnosticAsMutRead
import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.AsMutInstall
import duplicate_prefix.ScopedFrame
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.S05DiagnosticAsMutInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
def finalTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64) :=
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree

/-- Actual diagnostic as_mut_ptr argument installation; every borrow completion is internal. -/
theorem install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (treeEq : entry.allocation.extra = S05DiagnosticAsMutRead.tree)
    (parentEq : exprTag = S05DiagnosticFnEntryRead.tag 12)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 13)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (AsMutInstall.resultFrame frame valid value output borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let cache := AsMutInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := RootArgumentEntry.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,RootArgumentEntry.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some ActualReferenceMetadata.reference := by
    simp [live,RootArgumentEntry.liveFrame,cache,AsMutInstall.cacheFrame,LocalOperands.cachedLayoutFrame]
  let copied := AsMutPtrArgumentCopy.copiedFrame live 1 value liveValid
  have postValid : 1 < copied.locals.size := by simpa [copied,AsMutPtrArgumentCopy.copiedFrame] using liveValid
  have postLive : copied.locals[1].value = .live (.immediate value) := by simp [copied,AsMutPtrArgumentCopy.copiedFrame]
  have postCached : copied.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [copied,AsMutPtrArgumentCopy.copiedFrame] using cached
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have readFacts : read.status = .Completed ∧ read.tree = S05DiagnosticAsMutRead.afterRead := by
    simpa only [read,treeEq,parentEq,nextEq,offsetEq,lenEq,protectedEq,TypedBorrowSteps.registeredGlobal,
      S05DiagnosticAsMutRead.protections,S05DiagnosticDefaultRead.protections,Size.ZERO,Size.ofBytes] using S05DiagnosticAsMutRead.read
  have childDone : child.outcome = .ok () := by
    dsimp only [child]
    rw [readFacts.2]
    simpa only [parentEq,nextEq,offsetEq,lenEq,Size.ZERO,Size.ofBytes] using S05DiagnosticAsMutRead.constructor
  have childComplete := GeneralBorrowFreshReborrowStages.child_complete child childDone
  have info := RootReferenceInfo.facts options remaining span ctx false
  have validated := ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy GeneralBorrowFreshChild.inside
    rfl (by decide +kernel) (ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified
    id entry base offset len exprTag positive nonzero signedFits bounds frames copied machine tracker enabled mode
    borrowFrame frameBorrow fresh 1 postValid postLive postCached ghost shallow cachedAddress present race read.tree child.tree
    rfl readFacts.1 childComplete metadata notConstructed
  have checked := ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames live machine
    1 .uninit value liveValid (by simp [live,RootArgumentEntry.liveFrame]) cached noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size live 1 ActualReferenceMetadata.reference).stackView rfl _
    (by rw [validationEq]; exact validated)
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have typed : cache.body.locals[1]? = some 3 := by change frame.body.locals[1]? = some 3; rw [body]; rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames cache machine 1 3 cacheValid
    typed AsMutArgument.reference_storage_trivial (by simpa [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,LocalOperands.cachedLayoutFrame] using dead) noClocks
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff frames live machine 1
    ActualReferenceMetadata.reference liveValid cached ActualReferenceMetadata.reference_sized
  have compat : h.checkArgumentCompat () (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (Storage.withCurrent frames cache machine) = .ok true (Storage.withCurrent frames cache machine) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    exact AsMutEntryFacts.argument_compat _ options.compatibilityBudget _
  have passed := CallArgumentStages.copy_argument h () ⟨.immediate value,ActualReferenceMetadata.reference⟩
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ 3
    (Storage.withCurrent frames cache machine) _ _ _ _
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) compat rfl rfl storage evaluate checked
  have query := AsMutLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨613⟩
  change AsMutCallCore.spanAt h ⟨613⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := AsMutLocalStages.layout1 options limits (remaining+1) span frames (AsMutInstall.spanFrame frame) machine
    body identity callee valid uncached
  dsimp only [AsMutInstall.spanFrame] at layout
  dsimp only [cache,AsMutInstall.cacheFrame,AsMutInstall.spanFrame] at passed
  unfold AsMutInstall.action
  simp only [bind,EStateM.bind]
  rw [query]
  dsimp only
  rw [setspan]
  dsimp only
  rw [layout]
  dsimp only
  rw [ActualReferenceMetadata.reference_ty]
  rw [passed]
  simp only [pure,Pure.pure,EStateM.pure]
  congr 1


theorem scoped_install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (treeEq : entry.allocation.extra = S05DiagnosticAsMutRead.tree)
    (parentEq : exprTag = S05DiagnosticFnEntryRead.tag 12)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 13)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (AsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (AsMutInstall.resultFrame frame valid value output borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let activeTracker := {tracker with retagMode := .FnEntry}
  let activeMachine := {machine with borrowTracker := some activeTracker}
  have made := install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits frames frame activeMachine
    activeTracker rfl rfl borrowFrame frameBorrow fresh treeEq parentEq nextEq protectedEq offsetEq lenEq bounds valid body identity callee uncached dead noClocks ghost shallow
    cachedAddress present race metadata notConstructed
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent]
  rw [enabled]
  dsimp only
  simp only [Storage.withCurrent,activeMachine,activeTracker] at made
  rw [made]
  simp only [Storage.withCurrent,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal,activeMachine,activeTracker]
  rfl

end
end DuplicatePrefix.S05DiagnosticAsMutInstall

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutInstall." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut install dependency {dependency}"
