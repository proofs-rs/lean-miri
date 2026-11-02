import duplicate_prefix.CurrentCallResourceLenFacts
import duplicate_prefix.RootRejectedPrefix
namespace DuplicatePrefix.CurrentCallResourceRejectedPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CurrentCallResourceLenFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
private theorem fetched {frame : CompilerFrameContext.ActualFrame} {index : Nat} {slot : LocalState Provenance LocalLayout}
    (valid : index<frame.locals.size) (eq : frame.locals[index]?=some slot) : frame.locals[index]=slot :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans eq)
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)

theorem invoke (gt : count>len/2) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] result.rootFrame result.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span result.machine)))) ∧
      frame.body=result.rootFrame.body ∧ frame.bodyIdentity=result.rootFrame.bodyIdentity ∧
      frame.functionInstance=result.rootFrame.functionInstance ∧ frame.extra=result.rootFrame.extra ∧
      frame.returnPlace=result.rootFrame.returnPlace ∧ frame.returnContinuation=result.rootFrame.returnContinuation ∧
      frame.vaList=result.rootFrame.vaList ∧ frame.localsIdentity=result.rootFrame.localsIdentity ∧frame.locals.size=25 ∧
      frame.location=.mir ⟨10,0⟩ ∧
      frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate frame := by
  have sz:=size result
  have valid (index : Fin 25) : index.val<result.rootFrame.locals.size := by rw [sz];exact index.isLt
  obtain ⟨value,layout,shared⟩:=shared_slot result
  have s12:=fetched (valid ⟨12,by decide⟩) shared
  have s13:=fetched (valid ⟨13,by decide⟩) (slot13 result)
  have s0:=fetched (valid ⟨0,by decide⟩) (zero_slot result)
  have s7:=fetched (valid ⟨7,by decide⟩) (slot7 result)
  have s8:=fetched (valid ⟨8,by decide⟩) (slot8 result)
  have s9:=fetched (valid ⟨9,by decide⟩) (slot9 result)
  have s10:=fetched (valid ⟨10,by decide⟩) (slot10 result)
  have s11:=fetched (valid ⟨11,by decide⟩) (len_slot result)
  obtain ⟨body,identity,callee,clocks,rest⟩:=root_metadata result
  have model:=CurrentCallResourceLenFacts.model result
  obtain ⟨tracker,tracked,mode⟩:=model.defaultTracker
  exact RootRejectedPrefix.executes options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span result.machine model)
    model.debugOff C.validationFuel C.validationEq result.rootFrame result.machine len count gt sz value
    (congrArg LocalState.value s12) (congrArg LocalState.value s13) (congrArg LocalState.layout s13)
    (congrArg LocalState.value s0) (congrArg LocalState.layout s0) (congrArg LocalState.value s7)
    (congrArg LocalState.value s8) (congrArg LocalState.layout s8)
    (congrArg LocalState.value s9) (congrArg LocalState.layout s9)
    (congrArg LocalState.value s10) (congrArg LocalState.layout s10)
    (congrArg LocalState.value s11) (congrArg LocalState.layout s11)
    body identity callee (location result) (immediate result) clocks tracker tracked mode
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
end
end DuplicatePrefix.CurrentCallResourceRejectedPrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRejectedPrefix" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual rejected prefix dependency {dependency}"
