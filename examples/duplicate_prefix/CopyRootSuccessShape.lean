import duplicate_prefix.CopyRootOutput
import duplicate_prefix.PositiveRootSuccessProfile
import duplicate_prefix.RootSuccessToReturn

namespace DuplicatePrefix.CopyRootSuccessShape
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

set_option autoImplicit false in
/-- The concrete caller restored by the copy helper satisfies every local-state
requirement of the root success cleanup. Machine and protector-release conditions
are separate obligations. -/
structure Shape (before after : CompilerFrameContext.ActualFrame)
    (pointer destinationValue : Scalar Provenance) (count : UInt64) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  destination : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
  trackedCaller : after.trackCallerArg = before.trackCallerArg
  size : after.locals.size = 25
  location : after.location = .mir ⟨9,0⟩
  slot0 : after.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  slot15 : after.locals[15]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
  slot17 : after.locals[17]? = some ⟨.live (.immediate .uninit),none⟩
  slot18 : after.locals[18]? = some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩
  slot19 : after.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩
  slot21 : after.locals[21]? = some ⟨.live (.immediate (.scalar destinationValue)),some CopyCompilerFacts.destPointerLayout⟩
  slot24 : after.locals[24]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  immediate : CopyHelperCleanup.AllImmediate after

set_option autoImplicit false in
theorem of_copy (before frame : CompilerFrameContext.ActualFrame)
    (pointer destinationValue : Scalar Provenance) (count : UInt64)
    (shape : PositiveRootSuccessProfile.FrameShape before frame pointer destinationValue count)
    (zero : before.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (valid : 18 < frame.locals.size) :
    Shape before (CopyRootOutput.caller frame valid) pointer destinationValue count := by
  obtain ⟨body,identity,callee,extra,continuation,destination,varargs,trackedCaller,localsIdentity,size,location⟩ :=
    CopyRootOutput.metadata frame valid
  refine ⟨body.trans shape.body,identity.trans shape.identity,callee.trans shape.callee,
    extra.trans shape.extra,destination.trans shape.destination,continuation.trans shape.continuation,
    varargs.trans shape.varargs,localsIdentity.trans shape.localsIdentity,trackedCaller.trans shape.trackedCaller,
    size.trans shape.size,location,?_,?_,?_,?_,?_,?_,?_,CopyRootOutput.all_immediate frame valid shape.immediate⟩
  · exact (CopyRootOutput.other frame valid 0 (by decide)).trans (shape.slot0.trans zero)
  · exact (CopyRootOutput.other frame valid 15 (by decide)).trans shape.slot15
  · exact (CopyRootOutput.other frame valid 17 (by decide)).trans shape.slot17
  · exact (Array.getElem?_eq_getElem (by rw [size,shape.size];decide)).trans
      (congrArg some (CopyRootOutput.slot18 frame valid))
  · exact (CopyRootOutput.other frame valid 19 (by decide)).trans shape.slot19
  · exact (CopyRootOutput.other frame valid 21 (by decide)).trans shape.slot21
  · exact (CopyRootOutput.other frame valid 24 (by decide)).trans shape.slot24

set_option autoImplicit false in
private theorem row_at (frame : CompilerFrameContext.ActualFrame) (index : Nat)
    (valid : index < frame.locals.size) (row : LocalState Provenance LocalLayout)
    (known : frame.locals[index]? = some row) : frame.locals[index]'valid = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)

set_option autoImplicit false in
/-- Execute the root cleanup from the caller actually restored by the helper;
no cleanup statement or Goto success is assumed. -/
theorem reaches_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (before frame : CompilerFrameContext.ActualFrame)
    (pointer destinationValue : Scalar Provenance) (count : UInt64)
    (shape : PositiveRootSuccessProfile.FrameShape before frame pointer destinationValue count)
    (zero : before.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (valid : 18 < frame.locals.size)
    (body : before.body = RootBody.reflected.body.body)
    (identity : before.bodyIdentity = RootBody.reflected.body.identity)
    (callee : before.functionInstance = RootBody.reflected.functionInstance)
    (noClocks : before.extra.dataRace = none)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let restored := CopyRootOutput.caller frame valid
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames restored machine)
        (Storage.withCurrent frames {done with location := .mir ⟨10,0⟩}
          (SourceControl.accounted config.terminators (Storage.withCurrent frames done machine)).machine) ∧
      RootSuccessCleanupFacts.Shape restored done RootCompilerFacts.boolLayout (.scalar (.fromBool true)) := by
  have ready := of_copy before frame pointer destinationValue count shape zero valid
  let restored := CopyRootOutput.caller frame valid
  have at0 := row_at restored 0 (by rw [ready.size];decide) _ ready.slot0
  have at15 := row_at restored 15 (by rw [ready.size];decide) _ ready.slot15
  have at17 := row_at restored 17 (by rw [ready.size];decide) _ ready.slot17
  have at18 := row_at restored 18 (by rw [ready.size];decide) _ ready.slot18
  have at19 := row_at restored 19 (by rw [ready.size];decide) _ ready.slot19
  have at21 := row_at restored 21 (by rw [ready.size];decide) _ ready.slot21
  have at24 := row_at restored 24 (by rw [ready.size];decide) _ ready.slot24
  exact RootSuccessToReturn.reaches_return options limits remaining span source debugOff fuel validationFuel frames restored machine
    ready.size (.scalar pointer) .uninit (.scalar pointer) (.scalar destinationValue) (.scalar (.fromScalarInt (.ofUInt64 count)))
    (congrArg (fun row => row.value) at0) (congrArg (fun row => row.layout) at0)
    (congrArg (fun row => row.value) at15) (congrArg (fun row => row.value) at17) (congrArg (fun row => row.layout) at17)
    (congrArg (fun row => row.value) at18) (congrArg (fun row => row.value) at19)
    (congrArg (fun row => row.value) at21) (congrArg (fun row => row.value) at24)
    (ready.body.trans body) (ready.identity.trans identity) (ready.callee.trans callee) ready.location
    (by rw [ready.extra];exact noClocks) tracker tracked defaultMode ghost shallow unchecked noGc fixed

end DuplicatePrefix.CopyRootSuccessShape
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyRootSuccessShape.of_copy,``DuplicatePrefix.CopyRootSuccessShape.reaches_return] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved restored root success cleanup dependency {dependency}"
