import duplicate_prefix.AsMutLocalStages
import duplicate_prefix.AsMutArgument
import duplicate_prefix.AsMutCallCore
namespace DuplicatePrefix.AsMutInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def spanFrame (frame : CompilerFrameContext.ActualFrame) :=
  {frame with location := .unwinding ⟨613⟩}
def cacheFrame (frame : CompilerFrameContext.ActualFrame) (valid : (1 : MIR.LocalId) < frame.locals.size) :=
  LocalOperands.cachedLayoutFrame (spanFrame frame) 1 ActualReferenceMetadata.reference valid

def resultFrame (frame : CompilerFrameContext.ActualFrame) (valid : (1 : MIR.LocalId) < frame.locals.size)
    (value adjusted : Immediate Provenance) (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  let cached := cacheFrame frame valid
  let live := RootArgumentEntry.liveFrame cached 1 (by simpa [cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid)
  let copied := AsMutPtrArgumentCopy.copiedFrame live 1 value (by simpa [live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid)
  {(TypedBorrowSteps.registeredFrame copied borrowFrame id tag) with
   locals := (copied.locals.set 1 {value := .live (.immediate adjusted),layout := (copied.locals[1]'(by simpa [copied,AsMutPtrArgumentCopy.copiedFrame,live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid)).layout}
      (by simpa [copied,AsMutPtrArgumentCopy.copiedFrame,live,cached,cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using valid))}

def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  AsMutCallCore.spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ ty.ty false
  pure (1,1)

theorem install
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead)
    (uncached : frame.locals[1].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  have query := AsMutLocalStages.span1 options limits (remaining+1) span frames frame machine body identity callee
  have setspan := CallEntryLocals.set_span options limits (remaining+1) span frames frame machine ⟨613⟩
  change AsMutCallCore.spanAt h ⟨613⟩ (Storage.withCurrent frames frame machine) = _ at setspan
  have layout := AsMutLocalStages.layout1 options limits (remaining+1) span frames (spanFrame frame) machine
    body identity callee valid uncached
  have cachedValid : (1 : MIR.LocalId) < (cacheFrame frame valid).locals.size := by
    simpa [cacheFrame,spanFrame,LocalOperands.cachedLayoutFrame] using valid
  have cached : (cacheFrame frame valid).locals[1].layout = some ActualReferenceMetadata.reference := by
    simp [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self]
  have deadCached : (cacheFrame frame valid).locals[1].value = .dead := by
    simpa [cacheFrame,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,spanFrame] using dead
  have passed := AsMutArgument.pass_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames (cacheFrame frame valid)
    machine tracker enabled mode borrowFrame frameBorrow mask nextTag fresh cachedValid body deadCached cached noClocks ghost shallow
    cachedAddress present race metadata notConstructed
  dsimp only [spanFrame] at layout
  dsimp only [cacheFrame,spanFrame] at passed
  unfold action
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

#print axioms install
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut install dependency {dependency}"
end
end DuplicatePrefix.AsMutInstall
