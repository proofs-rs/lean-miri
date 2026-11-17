import duplicate_prefix.CurrentCallResourceLenReturn
namespace DuplicatePrefix.CurrentCallResourceLenFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open LenUncachedFrontend
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
private theorem written_other (frame : CompilerFrameContext.ActualFrame) (source dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) (different : source≠dest) :
    (ActualLocalCopy.written frame dest layout valid value).locals[source]?=frame.locals[source]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]
private theorem finish_other (frame : CompilerFrameContext.ActualFrame) (v : 11<frame.locals.size)
    (value : Immediate Provenance) (index : MIR.LocalId) (different : index≠11) :
    ({PtrMetadataExecution.writeFrame (cachedCaller frame v) 11 value (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using v)
      with location:=.mir ⟨3,0⟩} : CompilerFrameContext.ActualFrame).locals[index]?=frame.locals[index]? := by
  simp [PtrMetadataExecution.writeFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Ne.symm different]
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)

theorem size : result.rootFrame.locals.size=25 := by
  rw [result.rootEq]
  simpa only [PtrMetadataExecution.writeFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set,
    CurrentCallResourceLenInvoke.sharedFrame,CurrentCallResourceSharedStage.afterFrame,CopyHelperSteps.advance,
    ActualLocalCopy.written] using result.shape.size

theorem other (index : MIR.LocalId) (notLen : index≠11) (notShared : index≠12) :
    result.rootFrame.locals[index]?=result.callerFrame.locals[index]? := by
  rw [result.rootEq]
  exact (finish_other _ _ _ index notLen).trans
    (written_other result.callerFrame index (RootReferenceFacts.destination true) _ _ _ notShared)

theorem len_slot : result.rootFrame.locals[11]?=some
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ := by
  rw [result.rootEq]
  simp only [PtrMetadataExecution.writeFrame,Array.getElem?_set_self,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]

theorem location : result.rootFrame.location=.mir ⟨3,0⟩ := by rw [result.rootEq]

theorem metadata : result.rootFrame.body=result.callerFrame.body ∧
    result.rootFrame.bodyIdentity=result.callerFrame.bodyIdentity ∧
    result.rootFrame.functionInstance=result.callerFrame.functionInstance ∧
    result.rootFrame.extra=result.callerFrame.extra ∧
    result.rootFrame.returnPlace=result.callerFrame.returnPlace ∧
    result.rootFrame.returnContinuation=result.callerFrame.returnContinuation ∧
    result.rootFrame.vaList=result.callerFrame.vaList := by
  rw [result.rootEq]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem finish_immediate (frame : CompilerFrameContext.ActualFrame) (v : 11<frame.locals.size)
    (value : Immediate Provenance) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate ({PtrMetadataExecution.writeFrame (cachedCaller frame v) 11 value
      (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using v) with location:=.mir ⟨3,0⟩} : CompilerFrameContext.ActualFrame) := by
  apply CopyHelperCleanup.all_immediate_set _ _ _ (by simpa only [LocalPlaces.cachePlaceLayout,Array.size_set] using v) (CopyHelperCleanup.all_immediate_cache frame 11 _ v all)
  intro memory
  simp

theorem immediate : CopyHelperCleanup.AllImmediate result.rootFrame := by
  rw [result.rootEq]
  apply finish_immediate
  exact CopyHelperCleanup.all_immediate_written _ _ _ _ _ result.shape.immediate

private theorem written_slot (frame : CompilerFrameContext.ActualFrame) (dest : MIR.LocalId)
    (layout : LocalLayout) (valid : dest<frame.locals.size) (value : Immediate Provenance) :
    (ActualLocalCopy.written frame dest layout valid value).locals[dest]?=some ⟨.live (.immediate value),some layout⟩ := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

theorem shared_slot : ∃ value : Immediate Provenance, ∃ layout : LocalLayout,
    result.rootFrame.locals[12]?=some ⟨.live (.immediate value),some layout⟩ := by
  rw [result.rootEq,finish_other _ _ _ 12 (by decide)]
  exact ⟨_,_,written_slot _ _ _ _ _⟩

theorem model : DuplicatePrefixCallModel.Model options remaining span result.machine := by
  obtain ⟨old,enabled,mode⟩ := C.model.defaultTracker
  have equal : old=tracker := Option.some.inj (enabled.symm.trans C.state.enabled)
  subst old
  refine ⟨C.model.debugOff,C.model.preciseOff,C.model.implicitOff,result.flags.ghost,result.flags.shallow,
    ⟨_,result.tracked,mode⟩,result.flags.race,result.flags.backend,?_,result.flags.fixed,
    result.flags.unchecked,result.flags.noGc,C.model.nullComparator,C.model.sourceMatches⟩
  rw [result.flags.types,result.helper.types]
  exact (CurrentCallResourceSharedStage.model out).metadata

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins result.machine.user.payload.payload.user.types := by
  rw [result.flags.types,result.helper.types]
  exact CurrentCallResourceSharedStage.origins out

theorem zero_slot : result.rootFrame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩ := by
  rw [other result 0 (by decide) (by decide),result.shape.slot0]
  simpa using CurrentCallResourceEntryFacts.slots out ⟨0,by decide⟩

theorem unused (index : Fin 25) (lower : 13≤index.val)
    (not13 : index.val≠13) (not14 : index.val≠14) :
    result.rootFrame.locals[index.val]?=some ⟨.dead,none⟩ := by
  have n11 : index.val≠11 := by omega
  have n12 : index.val≠12 := by omega
  rw [other result index.val n11 n12,result.shape.keep index.val lower]
  simpa [show ¬14=index.val by omega,show ¬13=index.val by omega,show ¬6=index.val by omega,
    show ¬0=index.val by omega,show ¬2=index.val by omega,show ¬1=index.val by omega] using
    CurrentCallResourceEntryFacts.slots out index

 theorem root_metadata : result.rootFrame.body=RootBody.reflected.body.body ∧
    result.rootFrame.bodyIdentity=RootBody.reflected.body.identity ∧
    result.rootFrame.functionInstance=RootBody.reflected.functionInstance ∧
    result.rootFrame.extra.dataRace=none ∧
    result.rootFrame.returnPlace=root.frame.returnPlace ∧
    result.rootFrame.returnContinuation=root.frame.returnContinuation ∧
    result.rootFrame.vaList=root.frame.vaList := by
  obtain ⟨body,identity,callee,extra,destination,continuation,varargs⟩ := metadata result
  obtain ⟨oldBody,oldIdentity,oldCallee,oldContinuation,oldDestination,oldVarargs,clocks,rest⟩ := CurrentCallResourceEntryFacts.metadata out
  exact ⟨body.trans (result.shape.body.trans (oldBody.trans root.body)),
    identity.trans (result.shape.identity.trans (oldIdentity.trans root.identity)),
    callee.trans (result.shape.callee.trans (oldCallee.trans root.callee)),
    (congrArg (fun e=>e.dataRace) extra).trans ((congrArg (fun e=>e.dataRace) result.shape.extra).trans (clocks.trans root.noClocks)),
    destination.trans (result.shape.returnPlace.trans oldDestination),
    continuation.trans (result.shape.continuation.trans oldContinuation),
    varargs.trans (result.shape.vaList.trans oldVarargs)⟩

theorem slot13 : result.rootFrame.locals[13]?=some ⟨.live (.immediate .uninit),none⟩ := by
  rw [other result 13 (by decide) (by decide),result.shape.keep 13 (by decide)]
  simpa using CurrentCallResourceEntryFacts.slots out ⟨13,by decide⟩

theorem slot7 : result.rootFrame.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other result 7 (by decide) (by decide)).trans result.shape.slot7
 theorem slot8 : result.rootFrame.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other result 8 (by decide) (by decide)).trans result.shape.slot8
 theorem slot9 : result.rootFrame.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
  (other result 9 (by decide) (by decide)).trans result.shape.slot9
 theorem slot10 : result.rootFrame.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ :=
  (other result 10 (by decide) (by decide)).trans result.shape.slot10

end
end DuplicatePrefix.CurrentCallResourceLenFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenFacts" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len facts dependency {dependency}"
