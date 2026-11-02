import duplicate_prefix.CurrentCallInstalledCheckpoint
import duplicate_prefix.CurrentCallCheckpointSafety
import duplicate_prefix.CurrentCallSpatialEntryFacts
import duplicate_prefix.CurrentCallOrdinaryInput

/-! Couple the actual argument-copy and Bool-protection equations to the one
installed checkpoint and original all-count result. These equations are internal
outputs of the entry producers; they are not ordinary-input assumptions. -/
namespace DuplicatePrefix.CurrentCallOrdinaryPositiveFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures CandidateCurrentJointCall CandidateStableCallOwnership CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open Lean Elab Term in
elab "entry_finish_rule " suffix:str : term => do
  let found := (← getEnv).constants.toList.filter (fun (name, _) => name.toString.endsWith suffix.getString)
  match found with
  | [(name, _)] => return mkConst name
  | _ => throwError "expected one checked entry-finish theorem {suffix.getString}"

theorem invoke {options limits remaining span initial argument len place}
    (input : OrdinaryInput options limits remaining span initial argument len place)
    (pointer : Pointer Provenance) (encoding : argument = .pointer pointer) (count : UInt64)
    (sourceMachine sourceFnMachine finalMachine : Before)
    (sourceFnTracker next : MachineHooks.BorrowState) (offset : Nat)
    (source : Source finalMachine next offset len) (copyReady : CopyReady source)
    (output : Return finalMachine next place)
    (sourcePointer : source.role.family.value = CurrentCallTypedFnEntry.changedPointer pointer source.role.backing.id source.tag)
    (sourceTracked : sourceFnMachine.borrowTracker = some sourceFnTracker)
    (sourceGhost : sourceFnMachine.user.payload.ghost = false)
    (sourceShallow : sourceFnMachine.user.payload.validation = .Shallow)
    (sourceMachineEq : sourceMachine = {sourceFnMachine with borrowTracker := some {sourceFnTracker with retagMode := input.tracker.retagMode}})
    (copy :
      let root := CurrentCallSpatialEntryControl.root initial #[] place input.model.noDataRace
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm, ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace 0 (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent #[] (firstLive root).frame (ScopedFrame.entered (CurrentCallPush.preparedMachine initial #[]) input.tracker .FnEntry)) =
        .ok () (Storage.withCurrent #[]
          (CurrentCallSourceArguments.doneRoot options remaining span root {} pointer len source.role.backing.id source.tag).frame sourceFnMachine))
    (protection :
      let root := CurrentCallSpatialEntryControl.root initial #[] place input.model.noDataRace
      let args := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {} pointer len source.role.backing.id source.tag) count
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
        (Storage.withCurrent #[] (atSpan args ⟨601⟩).frame sourceMachine) =
        .ok () (Storage.withCurrent #[] (registeredFrame (atSpan args ⟨601⟩).frame
          (({} : FrameState).addProtector source.role.backing.id source.tag) output.id output.node.tag) finalMachine))
    (tracked : finalMachine.borrowTracker = some next) (mode : next.retagMode = .Default)
    (model : DuplicatePrefixCallModel.Model options remaining span finalMachine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types)
    (tagsDifferent : source.tag ≠ output.node.tag)
    (absent : output.id ≠ source.role.backing.id → ∀index node, output.window.allocation.extra.nodes.get index = some node → node.tag ≠ source.tag)
    (separate : output.id = source.role.backing.id → ∀byte, Window source.role.backing.id offset len.toNat byte → Window output.id output.offset 1 byte → False)
    (ids : (finalMachine.memory.live.toList.map Prod.fst).Nodup)
    (tags : next.global.nextPointerTag.value.toNat + 6 < 18446744073709551615)
    (threads : finalMachine.threads = (CurrentCallPush.preparedMachine initial #[]).threads) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial argument len count place := by
  have work : 0 < DuplicatePrefixCallSpecification.work initial len := by unfold DuplicatePrefixCallSpecification.work; omega
  have validationPositive : 0 < options.limits.validation := by have room := input.resources.configuredFuel.2.2.2; omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by have room := input.resources.dynamicFuel; omega
  let validationFuel := options.limits.validation - 1
  let dynamicFuel := options.place.dynamicFuel - 1
  have validationEq : options.limits.validation = validationFuel + 1 := by omega
  have dynamicEq : options.place.dynamicFuel = dynamicFuel + 1 := by omega
  let checkpoint : Checkpoint options remaining span len count place := CurrentCallInstalledCheckpoint.assemble tracked mode model origins source copyReady output
    tagsDifferent absent separate ids tags initial input.model.noDataRace input.stackReady threads validationFuel dynamicFuel validationEq dynamicEq
  let root := CurrentCallSpatialEntryControl.root initial #[] place input.model.noDataRace
  have rawLocals : root.frame.locals = Array.replicate 25 (⟨.dead, none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have actual := CurrentCallSpatialEntryControl.init_of_copy_protect options limits remaining span #[] root rawLocals {} pointer len count
    source.role.backing.id source.tag (CurrentCallPush.preparedMachine initial #[]) sourceMachine finalMachine
    (({} : FrameState).addProtector source.role.backing.id source.tag) output.id output.node.tag place input.tracker sourceFnTracker sourceFnMachine
    input.runtime.enabled sourceTracked input.model.ghostOff input.model.shallow sourceGhost sourceShallow validationFuel validationEq sourceMachineEq copy
    initial input.model.noDataRace input.model.debugOff input.stackReady rfl rfl protection
  have frameEq : CallEntryFacts.doneRootFrame
      {registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root {} pointer len source.role.backing.id source.tag) count) ⟨601⟩).frame
        (({} : FrameState).addProtector source.role.backing.id source.tag) output.id output.node.tag with location := .unwinding ⟨559⟩} = checkpoint.frame := by
    change _ = PositiveRootInstalledFrame.installed root
      (CurrentCallTypedSourceCopy.value options remaining span source.role.family.value len).imm count {} source.role.backing.id source.tag output.id output.node.tag
    rw [entry_finish_rule ".CurrentCallSpatialEntryFacts.source_root", sourcePointer]
    rfl
  rw [frameEq] at actual
  have machineEq : checkpoint.machine = finalMachine := rfl
  have entry : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining + 1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len), .Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩, initial⟩ : RootState) = .ok () (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) := by
    rw [encoding]
    simpa only [machineEq, DuplicatePrefixSliceArgument.first, DuplicatePrefixSliceArgument.rawValue, CurrentCallTypedSourceCopy.value] using actual
  have dispatchPositive : 0 < limits.callDispatch := by have room := input.resources.executionFuel.1; omega
  have statementPositive : 0 < limits.validation := by have room := input.resources.executionFuel.2.2.2; omega
  obtain ⟨budget, dispatch⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : limits.callDispatch ≠ 0)
  obtain ⟨statementFuel, statementEq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : limits.validation ≠ 0)
  exact CurrentCallCheckpointSafety.invoke checkpoint limits budget dispatch statementFuel statementEq initial argument entry

end
end DuplicatePrefix.CurrentCallOrdinaryPositiveFinish
