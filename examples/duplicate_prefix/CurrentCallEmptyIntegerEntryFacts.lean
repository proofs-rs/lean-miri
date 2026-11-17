import duplicate_prefix.CurrentCallEmptyIntegerCurrent
import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallEmptyIntegerFacts
import duplicate_prefix.CurrentCallSelectedBoolWindow
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
namespace DuplicatePrefix.CurrentCallEmptyIntegerEntryFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
private theorem firstFresh (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615) :
    tracker.global.nextPointerTag.value<18446744073709551615 :=
  UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
theorem of_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (address count : UInt64) (nonzero : address≠0)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (machine : Before) (held : GlobalState) (actualTag : BorTag)
    (entered : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CurrentCallEmptyIntegerFacts.frame options remaining span
          (CurrentCallPush.preparedMachine before frames) tracker (CurrentCallSpatialEntryControl.root before frames place model.noDataRace)
          address count physical.id actualTag) machine))
    (tracked : machine.borrowTracker=some ⟨held,tracker.retagMode⟩) :
    held.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 ∧
    machine.user.payload.payload.user.types=before.user.payload.payload.user.types ∧
    machine.user.addresses=before.user.addresses ∧
    machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras := by
  let fresh:=firstFresh tracker tagRoom
  let next:={tracker with global:=advanced tracker.global fresh}
  obtain ⟨P,output,child,pointerP,allocationP,preciseP,actual,tag,rootTag,⟨witness⟩,updated,finalMachine,
    actualEntry,memory,finalTracked,user,threads,race,live,extra,bytes,length,borrow,returnPlace,maskWF,maskLen,mutable,mutation,snapshot⟩ :=
    CurrentCallEmptyIntegerEntry.invoke options limits remaining span before tracker model enabled frames stackReady address count nonzero place physical
      data owner B pointer allocation runtime binding distinct tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins
  have sameMachine : machine=finalMachine:=congrArg (fun state : RootState=>state.machine) (EStateM.Result.ok.inj (entered.symm.trans actualEntry)).2
  have sameGlobal : held=output.global := congrArg MachineHooks.BorrowState.global (Option.some.inj (tracked.symm.trans (by rw [sameMachine];exact finalTracked)))
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value]
    exact tagRoom
  have literalEq : output=CurrentCallTypedFnEntry.literal P.allocation.extra next.global {} physical.id freshAfter P.pointer.value.provenance physical.offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ freshAfter _ _ _))
  have globalEq : output.global=(registered next.global {} physical.id freshAfter).1 := by rw [literalEq];rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [sameGlobal,globalEq]
    change (TypedRetagEmpty.successorTag next.global.nextPointerTag freshAfter).value.toNat=_
    rw [GenericFunctionEntryNumerics.successor_value]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat+1=_
    rw [GenericFunctionEntryNumerics.successor_value]
  · rw [sameMachine,user];rfl
  · rw [sameMachine,user];rfl
  · rw [sameMachine,user];rfl
end
end DuplicatePrefix.CurrentCallEmptyIntegerEntryFacts
