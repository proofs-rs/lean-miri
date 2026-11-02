import duplicate_prefix.S02SameDestinationInstalledLocals
import duplicate_prefix.S02SameDestinationMachineGeometry

namespace DuplicatePrefix.S02SameZeroFrameSettings
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact positive, same-allocation destination call supplies the frame and machine
control premises of the count-zero body from the original initial contract.
This packet is joined by determinism of the actual call, not a successful-body
or future-safety premise. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
      (thread : Miri.Concurrency.ThreadRecord)
      (fuel : Nat),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.bodyIdentity = RootBody.reflected.body.identity ∧
      frame.functionInstance = RootBody.reflected.functionInstance ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.locals.size = 25 ∧
      frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ ∧
      frame.locals[3]? = some ⟨.dead,none⟩ ∧
      frame.locals[4]? = some ⟨.dead,none⟩ ∧
      frame.locals[5]? = some ⟨.dead,none⟩ ∧
      frame.extra.dataRace = none ∧ frame.extra.borrowTracker = some borrowFrame ∧
      frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
      frame.returnContinuation = .stop true ∧ CopyHelperCleanup.AllImmediate frame ∧
      frame.vaList = #[] ∧
      machine.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
      machine.threads.activeThread? = some thread ∧ machine.dataRace = none ∧
      machine.user.payload.payload.user.backend = .none ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
      machine.threads.fixedScheduling = true ∧
      options.place.debugAssertions = false ∧ options.limits.validation = fuel+1 := by
  obtain ⟨reference,frame,machine,actual,size,location,slots,noClocks,immediate⟩ :=
    S02SameDestinationInstalledLocals.ready id tag address len 0 input nonempty sameAllocation returnTag returnConcrete
  obtain ⟨_reference2,destId,destTag,frame2,machine2,actual2,frameEq,body,identity,callee,_location,_size,
    _slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SameDestinationInstalledFrame.concrete_positive_installed id tag address len 0 input nonempty sameAllocation
      returnTag returnConcrete
  obtain ⟨_reference3,tracker,frame3,post,actual3,tracked,defaultMode,ghost,shallow,unchecked,noGc,fixed,race,
    _addresses,_types,backend,thread,active,_cache⟩ :=
    S02SameDestinationMachineGeometry.after_exact id tag address len 0 input nonempty sameAllocation
      returnTag returnConcrete
  have same2 : Storage.withCurrent #[] frame machine = Storage.withCurrent #[] frame2 machine2 :=
    (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
  have same3 : Storage.withCurrent #[] frame machine = Storage.withCurrent #[] frame3 post :=
    (EStateM.Result.ok.inj (actual.symm.trans actual3)).2
  have frame2Eq : frame = frame2 := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same2
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have machine3Eq : machine = post := congrArg (fun s : RootState => s.machine) same3
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete _reference2.id _reference2.tracker.global.nextPointerTag)
      (Size.ofBytes (_reference2.base+_reference2.offset))) len ActualReferenceMetadata.reference).imm
  have metadata := PositiveRootInstalledFrame.metadata root adjusted 0 {}
    _reference2.id _reference2.tracker.global.nextPointerTag destId destTag
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have frameProperties : frame.returnContinuation = .stop true ∧
      frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
      frame.vaList = #[] ∧
      ∃ borrowFrame, frame.extra.borrowTracker = some borrowFrame := by
    rw [frame2Eq,frameEq]
    refine ⟨metadata.2.2.2.1.trans control.2.2.1,?_,?_,?_⟩
    · rw [metadata.2.2.2.2.1,control.2.2.2]
      rfl
    · rw [metadata.2.2.2.2.2.1]
      rfl
    · exact ⟨_,metadata.2.2.2.2.2.2.2.1⟩
  obtain ⟨continuation,returnPlace,varargs,borrowFrame,frameTracked⟩ := frameProperties
  have fuelPositive : 0 < options.limits.validation := by
    have bound := input.contract.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at bound
    omega
  let fuel := options.limits.validation - 1
  have validationFuel : options.limits.validation = fuel+1 := by
    dsimp only [fuel]
    omega
  have localValue (i : Fin 25) := slots i
  have localSlot (i : Fin 25) : frame.locals[i.val]'(by rw [size]; exact i.isLt) =
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
      some ActualReferenceMetadata.reference⟩ else ⟨.dead,none⟩ := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (by rw [size]; exact i.isLt)).symm.trans (localValue i))
  refine ⟨frame,machine,tracker,borrowFrame,thread,fuel,actual,?_,?_,?_,location,size,?_,?_,?_,?_,?_,
    noClocks,frameTracked,returnPlace,continuation,immediate,varargs,?_,defaultMode,?_,?_,?_,
    ?_,?_,?_,?_,?_,?_,validationFuel⟩
  · rw [frame2Eq]; exact body
  · rw [frame2Eq]; exact identity
  · rw [frame2Eq]; exact callee
  · simpa using slots ⟨0,by decide⟩
  · simpa using slots ⟨2,by decide⟩
  · simpa using slots ⟨3,by decide⟩
  · simpa using slots ⟨4,by decide⟩
  · simpa using slots ⟨5,by decide⟩
  · rw [machine3Eq]; exact tracked
  · rw [machine3Eq]; exact active
  · rw [machine3Eq]; exact race
  · rw [machine3Eq]; exact backend
  · rw [machine3Eq]; exact ghost
  · rw [machine3Eq]; exact shallow
  · rw [machine3Eq]; exact unchecked
  · rw [machine3Eq]; exact noGc
  · rw [machine3Eq]; exact fixed
  · exact input.contract.model.debugOff

end
end DuplicatePrefix.S02SameZeroFrameSettings

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameZeroFrameSettings.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved zero frame/settings dependency {dependency}"
