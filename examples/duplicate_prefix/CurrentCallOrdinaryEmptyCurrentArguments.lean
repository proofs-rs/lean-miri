import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentState
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallOrdinaryEmptyCurrentState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument}
    {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)


/-- The genuine CURRENT source copy supplies the enclosing FnEntry argument
computation. Its original mode is restored without repeating materialization. -/
theorem arguments (updated : Immediate Provenance) (count : UInt64)
    (copy :
      let rootFrame:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
      let rawValue:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate rawValue,reference⟩
        (LocalPlaces.localRuntimePlace 0 (firstLive rootFrame).frame 1 reference).stackView
        (Storage.withCurrent #[] (firstLive rootFrame).frame
          (ScopedFrame.entered (CurrentCallPush.preparedMachine before #[]) input.tracker .FnEntry))=
        .ok () (Storage.withCurrent #[]
          (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated
            (({} : FrameState).addProtector id input.tracker.global.nextPointerTag)).frame
          (closed options result.machine id root result.converted tree result.global .FnEntry))) :
    let rootFrame:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let rawValue:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate rawValue,reference⟩ (second count))
      (Storage.withCurrent #[] rootFrame.frame (CurrentCallPush.preparedMachine before #[]))=
      .ok (2,2) (Storage.withCurrent #[]
        (RootArgumentsTwo.result (CurrentCallEmptyProtocolControl.sourceRoot rootFrame updated
          (({} : FrameState).addProtector id input.tracker.global.nextPointerTag)) count).frame
        (closed options result.machine id root result.converted tree result.global input.tracker.retagMode)) := by
  let rootFrame:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  have raw : rootFrame.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  let fuel:=options.limits.validation-1
  have fuelEq : options.limits.validation=fuel+1 := by
    have room:=input.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at room
    dsimp only [fuel]
    omega
  have currentModel:=CurrentCallOrdinaryEmptyCurrentState.model input id pointer root source externStatic tail finalAddresses finalTape result tree
  have afterShallow : (closed options result.machine id root result.converted tree result.global .FnEntry).user.payload.validation=.Shallow := currentModel.shallow
  exact CurrentCallEmptyProtocolControl.arguments options limits remaining span input.model.debugOff fuel fuelEq
    #[] rootFrame raw (CurrentCallPush.preparedMachine before #[])
    (closed options result.machine id root result.converted tree result.global .FnEntry)
    input.tracker ⟨result.global,.FnEntry⟩ input.runtime.enabled rfl input.model.ghostOff input.model.shallow
    rfl afterShallow _ updated (({} : FrameState).addProtector id input.tracker.global.nextPointerTag) count copy

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentArguments

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryEmptyCurrentArguments.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved CURRENT empty argument dependency {name}: {dependency}"
