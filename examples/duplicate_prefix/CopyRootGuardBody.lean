import duplicate_prefix.CopyRootGuardState
import duplicate_prefix.LanguageGuardBody
import duplicate_prefix.CopyRootComplete
import duplicate_prefix.CopyRootOutput

/-! The actual language guard reached by the root's copy call. The runtime
cache metadata is derived from its real push; no guard trace is assumed. -/
namespace DuplicatePrefix.CopyRootGuardBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (input : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)

private theorem prepared_fifth (original : CompilerFrameContext.ActualFrame)
    (valid4 : (4 : MIR.LocalId) < original.locals.size)
    (valid5 : (5 : MIR.LocalId) < original.locals.size) :
    let first := SourceSteps.liveFrame original ⟨0,0⟩ 4 valid4
    let ready := SourceSteps.liveFrame first ⟨0,1⟩ 5 (by simpa only [first,SourceSteps.liveFrame,Array.size_set] using valid5)
    let result := LanguageZeroUncached.cachedCaller ready (by simpa only [ready,first,SourceSteps.liveFrame,Array.size_set] using valid5)
    ∃ resultValid : (5 : MIR.LocalId) < result.locals.size,
      (result.locals[5]'resultValid).value = .live (.immediate .uninit) ∧
      (result.locals[5]'resultValid).layout = some RootCompilerFacts.boolLayout := by
  dsimp only
  refine ⟨by simpa only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.size_set] using valid5,?_,?_⟩
  · simp only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.getElem_set_self]
  · simp only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.getElem_set_self]

private theorem four_push_lookup {α : Type} (xs : Array α) (a b c d : α) :
    ((((xs.push a).push b).push c).push d)[xs.size+2]? = some c ∧
    ((((xs.push a).push b).push c).push d)[xs.size]? = some a := by
  constructor <;> simp [Array.getElem_push,Nat.add_assoc]

noncomputable def copyCaller := LanguageZeroUncached.cachedCaller
  (CopyRootGuardEntry.prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input)
  (by rw [CopyRootGuardEntry.prepared_size]; decide)

theorem copy_size : (copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size = 17 := by
  simp only [copyCaller,LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  exact CopyRootGuardEntry.prepared_size options limits remaining span frames caller machine sourcePointer destinationPointer n input

noncomputable def returnedCopy := ParentFalseReturn.returnedCallerFrame
  (copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input)
  (by rw [copy_size]; decide) 1

theorem returned_locals :
    (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals =
      #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩ := by
  have locals := CopyEntryShape.locals
    (Storage.withCurrent frames
      (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input)
      (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size
      (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input)
      18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  simp only [returnedCopy,ParentFalseReturn.returnedCallerFrame,copyCaller,LanguageZeroUncached.cachedCaller,
    CopyRootGuardEntry.prepared,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout]
  change (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals = _ at locals
  simp [locals]
  rfl

private theorem returned_slots (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
    (xs : Array (LocalState Provenance LocalLayout))
    (rows : xs = #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩) :
    ∃ (v0 : (0 : MIR.LocalId) < xs.size) (v1 : (1 : MIR.LocalId) < xs.size) (v2 : (2 : MIR.LocalId) < xs.size) (v3 : (3 : MIR.LocalId) < xs.size) (v4 : (4 : MIR.LocalId) < xs.size) (v5 : (5 : MIR.LocalId) < xs.size) (v14 : (14 : MIR.LocalId) < xs.size) (v15 : (15 : MIR.LocalId) < xs.size) (v16 : (16 : MIR.LocalId) < xs.size),
      xs[0]'v0 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[1]'v1 = ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      xs[2]'v2 = ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      xs[3]'v3 = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      xs[4]'v4 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[5]'v5 = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      xs[14]'v14 = ⟨.dead,none⟩ ∧
      xs[15]'v15 = ⟨.dead,none⟩ ∧
      xs[16]'v16 = ⟨.dead,none⟩ := by
  subst xs
  exact ⟨by change 0 < 17; decide,by change 1 < 17; decide,by change 2 < 17; decide,by change 3 < 17; decide,by change 4 < 17; decide,by change 5 < 17; decide,by change 14 < 17; decide,by change 15 < 17; decide,by change 16 < 17; decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem returned_metadata :
    let result := returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input
    let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
    result.body = HelperCompilerFacts.copyBody.body ∧
    result.bodyIdentity = HelperCompilerFacts.copyBody.identity ∧
    result.functionInstance = HelperCompilerFacts.copyCall.callee ∧
    result.location = .mir ⟨1,0⟩ ∧ result.locals.size = 17 ∧
    result.returnPlace = (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView ∧
    result.returnContinuation = .goto (some 9) .Continue ∧ result.vaList = #[] ∧
    result.extra.dataRace = none ∧ result.extra.borrowTracker = some ({} : FrameState) := by
  dsimp only
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let state := Storage.withCurrent frames root (CopyCallStep.accountedMachine options remaining span machine)
  let destination := (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView
  obtain ⟨body,identity,callee,location,place,continuation,varargs,track⟩ :=
    CopyEntryShape.control state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  refine ⟨body,identity,callee,rfl,?_,place,continuation,varargs,?_,?_⟩
  · simpa only [returnedCopy,ParentFalseReturn.returnedCallerFrame,Array.size_set] using
      copy_size options limits remaining span frames caller machine sourcePointer destinationPointer n input
  · exact CopyEntryShape.no_clocks state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  · exact CopyEntryShape.borrow state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
      input.tracker input.tracked

theorem returned_all_immediate : CopyHelperCleanup.AllImmediate
    (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) := by
  intro slot member memory
  rw [returned_locals] at member
  simp [Array.mem_def] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem pushed_active
    (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (current : CompilerFrameContext.ActualFrame)
    (thread : Miri.Concurrency.ThreadRecord) (active : state.machine.threads.activeThread? = some thread) :
    (LanguageZeroEntry.pushedMachine options state destination current).threads.activeThread? =
      some (PushThread.after thread state.stack.frames.size
        (LanguageZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance) := by
  exact PushThread.active_after (CallEntryFacts.freshRoot state.machine).1 thread state.stack.frames.size
    (LanguageZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance active

private theorem accounted_control (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let h := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    h.getControl (LanguageZeroStep.accountedMachine options remaining span machine).user =
      TerminatorClock.advance (h.getControl machine.user) := by
  dsimp only
  unfold LanguageZeroStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem from_copy
    (statementFuel : limits.validation = input.fuel+1)
    (mode : input.tracker.retagMode = .Default) :
    ∃ finalMachine,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (CopyRootEntry.entered options limits remaining span frames caller machine sourcePointer destinationPointer n input)
        (Storage.withCurrent
          (frames.push (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
          (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine finalMachine ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let copy := copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let state := CopyRootGuardEntry.languageState options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let destination := CopyRootGuardEntry.languageDestination options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let frame := LanguageZeroInstalled.frame options state destination
  let pushed := LanguageZeroEntry.pushedMachine options state destination root
  let copyMachine := CopyPushPreserves.post options remaining span machine
  obtain ⟨cm,ct,cth,cr,ca,cg,cv,cb,ce,cty⟩ := CopyPushPreserves.fields options remaining span machine
  obtain ⟨am,atracker,ath,ar,aa,ag,av,ab,ae,aty⟩ := CopyRootGuardState.accounted_fields options remaining span copyMachine
  obtain ⟨pm,pt,pr,pa,pg,pv,pb,pe,pty,pf⟩ := CopyRootGuardState.language_push_fields options state destination root
  have stateTracked : state.machine.borrowTracker = some input.tracker := atracker.trans (ct.trans input.tracked)
  have stateRace : state.machine.dataRace = none := ar.trans (cr.trans input.noRace)
  have stateActive : state.machine.threads.activeThread? = some input.thread := by
    change (LanguageZeroStep.accountedMachine options remaining span copyMachine).threads.activeThread? = _
    rw [ath,cth]
    exact input.active
  have pushedTracked : pushed.borrowTracker = some input.tracker := pt.trans stateTracked
  have pushedRace : pushed.dataRace = none := pr.trans stateRace
  have pushedBackend : pushed.user.payload.payload.user.backend = .none := pb.trans (ab.trans (cb.trans input.backend))
  have pushedGhost : pushed.user.payload.ghost = false := pg.trans (ag.trans (cg.trans input.ghost))
  have pushedValidation : pushed.user.payload.validation = .Shallow := pv.trans (av.trans (cv.trans input.shallow))
  have pushedPreserves : LanguageGuardReturn.Preserves options remaining span machine pushed := {
    memory := pm.trans (am.trans cm),tracker := pt.trans (atracker.trans ct),race := pr.trans (ar.trans cr),
    addresses := pa.trans (aa.trans ca),ghost := pg.trans (ag.trans cg),validation := pv.trans (av.trans cv),
    backend := pb.trans (ab.trans cb),extras := pe.trans (ae.trans ce),types := pty.trans (aty.trans cty),
    fixed := pf.trans (by change (LanguageZeroStep.accountedMachine options remaining span copyMachine).threads.fixedScheduling = _; rw [ath,cth]),
    unchecked := by
      change (config.terminators.getControl (LanguageZeroEntry.pushedMachine options state destination root).user).checkedArithmetic = _
      rw [CopyRootGuardState.language_push_control]
      change (config.terminators.getControl (LanguageZeroStep.accountedMachine options remaining span copyMachine).user).checkedArithmetic = _
      rw [accounted_control,CopyPushPreserves.control]
      rfl,
    noGc := by
      change (config.terminators.getControl (LanguageZeroEntry.pushedMachine options state destination root).user).gcInterval = _
      rw [CopyRootGuardState.language_push_control]
      change (config.terminators.getControl (LanguageZeroStep.accountedMachine options remaining span copyMachine).user).gcInterval = _
      rw [accounted_control,CopyPushPreserves.control]
      rfl }
  have pushedUnchecked : (config.terminators.getControl pushed.user).checkedArithmetic = false := pushedPreserves.unchecked.trans input.unchecked
  have pushedGc : (config.terminators.getControl pushed.user).gcInterval = 0 := pushedPreserves.noGc.trans input.noGc
  have pushedFixed : pushed.threads.fixedScheduling = true := pushedPreserves.fixed.trans input.fixed
  obtain ⟨body,identity,callee,location,track,continuation,varargs⟩ := LanguageZeroInstalled.metadata options state destination
  have size : frame.locals.size = 3 := LanguageZeroInstalled.locals_size options state destination
  have v0 : (0 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v1 : (1 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v2 : (2 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  obtain ⟨live0,cache0,dead1,cache1,dead2,cache2⟩ := LanguageZeroInstalled.slots options state destination
  change frame.locals[0]?.map (·.value) = some (.live (.immediate .uninit)) at live0
  change frame.locals[0]?.map (·.layout) = some none at cache0
  simp only [Array.getElem?_eq_getElem v0,Option.map_some,Option.some.injEq] at live0 cache0
  change frame.locals[1]?.map (·.value) = some (.dead) at dead1
  change frame.locals[1]?.map (·.layout) = some none at cache1
  simp only [Array.getElem?_eq_getElem v1,Option.map_some,Option.some.injEq] at dead1 cache1
  change frame.locals[2]?.map (·.value) = some (.dead) at dead2
  change frame.locals[2]?.map (·.layout) = some none at cache2
  simp only [Array.getElem?_eq_getElem v2,Option.map_some,Option.some.injEq] at dead2 cache2
  have clocks : frame.extra.dataRace = none := CopyRootGuardState.language_frame_clocks options state destination stateRace
  have borrow : frame.extra.borrowTracker = some ({} : FrameState) :=
    CopyRootGuardState.language_frame_borrow options state destination input.tracker stateTracked
  have original4 : (4 : MIR.LocalId) < (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size := by
    rw [CopyRootGuardEntry.copy_size];decide
  have original5 : (5 : MIR.LocalId) < (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size := by
    rw [CopyRootGuardEntry.copy_size];decide
  obtain ⟨copyValid5,copyLive5,copyCache5⟩ := prepared_fifth
    (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input) original4 original5
  have copyClocks : copy.extra.dataRace = none := CopyEntryShape.no_clocks
    (Storage.withCurrent frames root (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView
    (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  have frameDestination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace (frames.push root).size copy 5 RootCompilerFacts.boolLayout := by rfl
  let ready := ParentUnitPrelude.afterPrelude frame v1 v2
  have readyValid : (1 : MIR.LocalId) < ready.locals.size := by
    simpa [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout] using v1
  let runtimeCaller := RuntimeZeroUncached.cachedCaller ready readyValid
  let runtimeState := Storage.withCurrent ((frames.push root).push copy) runtimeCaller
    (RuntimeZeroStep.accountedMachine options remaining span pushed)
  let runtimeDestination := RuntimeZeroEntry.destination ((frames.push root).push copy) ready
  have pushedSize : state.stack.frames.size = frames.size+2 := by
    simp only [state,CopyRootGuardEntry.languageState,Storage.withCurrent,Array.size_push]
  have pushedActive : pushed.threads.activeThread? = some
      (PushThread.after input.thread (frames.size+2) (LanguageZeroEntryFacts.rank options.userRelevantCrates) root.extra.userRelevance) := by
    have active := pushed_active options state destination root input.thread stateActive
    simpa only [pushedSize] using active
  have runtimeMetadata : ∃ (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame),
      pushed.threads.activeThread? = some thread ∧
      FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates runtimeState runtimeDestination).stack
        thread.topUserRelevantFrame = some index ∧
      (RuntimeZeroEntryFacts.pushed options.userRelevantCrates runtimeState runtimeDestination).stack.frames[index]? = some current := by
    by_cases rank : LanguageZeroEntryFacts.rank options.userRelevantCrates >= root.extra.userRelevance
    · refine ⟨{input.thread with topUserRelevantFrame := some (frames.size+2)},frames.size+2,runtimeCaller,?_,?_,?_⟩
      · simpa only [PushThread.after,rank,ite_true] using pushedActive
      · simp [FrameRelevance.top]
      · dsimp only [RuntimeZeroEntryFacts.pushed,runtimeState,Storage.withCurrent]
        exact (four_push_lookup frames root copy runtimeCaller _).1
    · refine ⟨input.thread,frames.size,root,?_,?_,?_⟩
      · simpa only [PushThread.after,rank,ite_false] using pushedActive
      · simp [FrameRelevance.top,input.top]
      · dsimp only [RuntimeZeroEntryFacts.pushed,runtimeState,Storage.withCurrent]
        exact (four_push_lookup frames root copy runtimeCaller _).2
  obtain ⟨thread,index,current,active,top,present⟩ := runtimeMetadata
  obtain ⟨finalMachine,bodyTrace,preserved,finalActive,safe⟩ := LanguageGuardBody.from_entry
    options limits remaining input.budget input.fuel input.budgetEq input.validationFuel statementFuel
    span input.source input.cmp input.debug (frames.push root) copy frame pushed body identity callee location size
    v0 live0 cache0 v1 dead1 cache1 v2 dead2 cache2 clocks pushedRace pushedBackend pushedGhost pushedValidation
    input.tracker pushedTracked mode thread index current active top present pushedUnchecked pushedGc pushedFixed
    copyValid5 copyLive5 copyCache5 copyClocks frameDestination 1 .Continue continuation varargs ({} : FrameState) borrow rfl
  have finalPreserves : LanguageGuardReturn.Preserves options remaining span machine finalMachine := {
    memory := preserved.memory.trans pushedPreserves.memory,tracker := preserved.tracker.trans pushedPreserves.tracker,
    race := preserved.race.trans pushedPreserves.race,addresses := preserved.addresses.trans pushedPreserves.addresses,
    ghost := preserved.ghost.trans pushedPreserves.ghost,validation := preserved.validation.trans pushedPreserves.validation,
    backend := preserved.backend.trans pushedPreserves.backend,extras := preserved.extras.trans pushedPreserves.extras,
    types := preserved.types.trans pushedPreserves.types,fixed := preserved.fixed.trans pushedPreserves.fixed,
    unchecked := preserved.unchecked.trans pushedPreserves.unchecked,noGc := preserved.noGc.trans pushedPreserves.noGc }
  refine ⟨finalMachine,?_,finalPreserves,finalActive⟩
  exact SuccessfulTrace.append
    (CopyRootGuardEntry.from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input) bodyTrace

theorem run
    (statementFuel : limits.validation = input.fuel+1)
    (mode : input.tracker.retagMode = .Default) :
    ∃ finalMachine,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller machine)
        (Storage.withCurrent
          (frames.push (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
          (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine finalMachine ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  obtain ⟨finalMachine,trace,preserved,active⟩ := from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input statementFuel mode
  exact ⟨finalMachine,SuccessfulTrace.append (CopyRootEntry.trace options limits remaining span frames caller machine sourcePointer destinationPointer n input) trace,preserved,active⟩

set_option autoImplicit false in
/-- Data needed for the actual copy after the language/runtime guard returns.
Every field describes inputs, allocation contents or the fixed configuration;
no successful interpreter operation is an input field. -/
structure CopyData (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) where
  id : AllocId
  tag : BorTag
  tags : Fin 6 → BorTag
  base : UInt64
  offset : UInt64
  sliceLen : UInt64
  kind : MemoryKind MiriMemoryKind
  allocation : Allocation Provenance BorrowTree
  positive : 0 < n
  sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat
  copyBounds : n.toNat+n.toNat ≤ sliceLen.toNat
  storage : allocation.len = allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed allocation.initializationMask
  maskLen : allocation.initializationMask.len = allocation.byteSize
  initialized : InitMaskCopy.InitializedOn allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+n))
  valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len
  storageFits : allocation.len+64 < 18446744073709551616
  mutable : allocation.mutability = .Mut
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  live : machine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,allocation⟩)
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  distinct : Function.Injective tags
  tagAt : tag = tags 5
  tree : allocation.extra = NestedBorrowAccess.nestedTree tags
    (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset+sliceLen)
      BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
  protectionMask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false
  bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes
  source : sourcePointer = Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))
  destination : destinationPointer = Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))

/-- Execute the real root copy call, both guards, and the copy helper return.
The previously internal guard-prefix premise is discharged by `from_copy`. -/
theorem complete
    (statementFuel : limits.validation = input.fuel+1)
    (mode : input.tracker.retagMode = .Default)
    (data : CopyData options remaining span machine input.tracker sourcePointer destinationPointer n) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let readAccess := data.allocation.extra.performBorrowAccessRange (.concrete data.tag)
      (Size.ofBytes data.offset) (Size.ofBytes n) .Read input.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete data.tag)
      (Size.ofBytes (data.offset+n)) (Size.ofBytes n) .Write input.tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (CopyRootOutput.caller caller input.valid) finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == data.id) = some (data.id,⟨data.kind,result⟩) ∧
      result.byteSize = data.allocation.byteSize ∧ result.len = data.allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot data.allocation).extract 0 (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract data.offset.toNat (data.offset+n).toNat ++
        (AllocationCopy.snapshot data.allocation).extract (data.offset+n+n).toNat data.allocation.len ∧
      finalMachine.memory = CopyHelperCall.memoryAfter machine.memory data.id data.kind result ∧
      finalMachine.borrowTracker = some input.tracker ∧
      finalMachine.dataRace = none ∧ finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      (config.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (config.terminators.getControl finalMachine.user).gcInterval = 0 ∧ finalMachine.threads.fixedScheduling = true ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by
  dsimp only
  obtain ⟨guardMachine,guardTrace,preserved,guardThread,guardActive⟩ :=
    from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input statementFuel mode
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let after := returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input
  obtain ⟨body,identity,callee,location,size,returnPlace,continuation,varargs,noClocks,borrow⟩ :=
    returned_metadata options limits remaining span frames caller machine sourcePointer destinationPointer n input
  have rows := returned_locals options limits remaining span frames caller machine sourcePointer destinationPointer n input
  obtain ⟨v0,v1,v2,v3,v4,v5,v14,v15,v16,cell0,cell1,cell2,cell3,cell4,cell5,cell14,cell15,cell16⟩ :=
    returned_slots sourcePointer destinationPointer n after.locals rows
  have rootValid : (18 : MIR.LocalId) < root.locals.size := by
    simpa only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.size_set] using input.valid
  have rootLive : (root.locals[18]'rootValid).value = .live (.immediate input.old) := by
    simpa only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using input.live
  have rootCached : (root.locals[18]'rootValid).layout = some CopyHelperUnit.layout := by
    simp only [root,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have rootClocks : root.extra.dataRace = none := input.noClocks
  have destination : after.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout := by rw [returnPlace];rfl
  obtain ⟨result,finalMachine,trace,lookup,bytes,len,tree,snapshot,memory,tracked,race,ghost,shallow,unchecked,noGc,fixed,
      addresses,types,backend,extras,active⟩ := CopyRootComplete.of_guard_prefix
    options limits remaining span input.source input.debug input.fuel input.validationFuel frames root after guardMachine
    body identity callee location size input.tracker data.id data.tag data.tags data.base data.offset data.sliceLen n data.kind data.allocation
    data.positive data.sliceBounds data.copyBounds data.storage data.maskValid data.maskLen data.initialized data.valid data.storageFits data.mutable
    (preserved.race.trans input.noRace) (preserved.backend.trans input.backend) (preserved.tracker.trans input.tracked)
    (by rw [preserved.extras];exact data.extras) (by rw [preserved.memory];exact data.live)
    (by rw [preserved.addresses];exact data.cached) data.distinct data.tagAt data.tree data.protectionMask data.bounded
    (by simp only [cell1]; exact congrArg (fun value => LocalValue.live (.immediate (.scalar value))) data.source) (by simp only [cell2]; exact congrArg (fun value => LocalValue.live (.immediate (.scalar value))) data.destination) (by rw [cell3])
    (by rw [cell1]) (by rw [cell2]) (by rw [cell3])
    (by rw [cell4]) (by rw [cell4]) (by rw [cell5]) (by rw [cell5])
    (by rw [cell14]) (by rw [cell14]) (by rw [cell15]) (by rw [cell15]) (by rw [cell16]) (by rw [cell16])
    (returned_all_immediate options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    noClocks mode (preserved.unchecked.trans input.unchecked) (preserved.noGc.trans input.noGc)
    (preserved.fixed.trans input.fixed) (preserved.ghost.trans input.ghost) (preserved.validation.trans input.shallow)
    (by rw [cell0]) (by rw [cell0]) varargs ({} : FrameState) borrow rfl guardThread guardActive
    18 rootValid input.old rootLive rootCached rootClocks destination 9 .Continue continuation
    caller machine sourcePointer destinationPointer input guardTrace
  refine ⟨result,finalMachine,?_,lookup,bytes,len,tree,snapshot,?_,?_,race,ghost,shallow,unchecked,noGc,fixed,
    addresses.trans preserved.addresses,types.trans preserved.types,backend.trans preserved.backend,extras.trans preserved.extras,active⟩
  · exact trace
  · exact memory.trans (congrArg (fun before => CopyHelperCall.memoryAfter before data.id data.kind result) preserved.memory)
  · simpa only [GlobalState.endCall,Array.foldl_empty] using tracked

end DuplicatePrefix.CopyRootGuardBody
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyRootGuardBody.returned_locals,
      ``DuplicatePrefix.CopyRootGuardBody.returned_metadata,``DuplicatePrefix.CopyRootGuardBody.returned_all_immediate,
      ``DuplicatePrefix.CopyRootGuardBody.from_copy,``DuplicatePrefix.CopyRootGuardBody.run,
      ``DuplicatePrefix.CopyRootGuardBody.complete] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved concrete copy guard body dependency {dependency}"
