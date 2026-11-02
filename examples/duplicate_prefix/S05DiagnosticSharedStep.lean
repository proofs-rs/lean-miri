import duplicate_prefix.S05DiagnosticEntryPrefix
import duplicate_prefix.S05DiagnosticSharedExpression
namespace DuplicatePrefix.S05DiagnosticSharedStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments S05DiagnosticFnEntryScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The count-one diagnostic's actual call through its first shared Ref statement. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : entry.allocation.extra = S05DiagnosticFnEntryRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 6)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 8)
    (protectedEq : tracker.global.protectedTags = ({} : ProtectedTags))
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (source : PreparedContracts.SourceComparator)
    (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
    ∃ (frame result : CompilerFrameContext.ActualFrame) (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second 1)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
          .ok () (Storage.withCurrent #[] frame machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result post) ∧ result.location = .mir ⟨2,12⟩ ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧ result.locals.size = 25 ∧ result.extra.dataRace = none ∧
      result.locals[12]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue
        (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 10)) (Size.ofBytes base)) 2
        (RootReferenceInfo.layout true)).imm),some (RootReferenceInfo.layout true)⟩ ∧
      result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      let entered := {entry with allocation := entry.allocation.setExtra (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}
      let protections := (({} : ProtectedTags).insert (S05DiagnosticFnEntryRead.tag 8) .StrongProtector).insert
        (S05DiagnosticFnEntryRead.tag 9) .StrongProtector
      post.memory.live.find? (fun row => row.1 == id) = some (id,{entered with allocation := entered.allocation.setExtra (S05DiagnosticSharedExpression.child entered.allocation.extra protections (S05DiagnosticFnEntryRead.tag 8)
          (S05DiagnosticFnEntryRead.tag 10) 0 2 .VisitChildrenOfAccessed).tree}) ∧
      post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      post.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
      post.dataRace = none ∧ post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧
      post.user.payload.payload.user.backend = .none ∧
      post.threads = (RawRootInvocation.machine #[] before).threads ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      ∃ postTracker, post.borrowTracker = some postTracker ∧ postTracker.retagMode = .Default ∧
        postTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 11 ∧
        postTracker.global.protectedTags = protections ∧
        ∃ (site : CompilerFrameContext.ActualFrame) (siteShape : GenericFunctionEntryPrefix.Shape frame site 1),
          result = CopyHelperSteps.advance (ActualLocalCopy.written site 12 (RootReferenceInfo.layout true)
            (by rw [siteShape.size];decide) (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 10)) (Size.ofBytes base)) 2 (RootReferenceInfo.layout true)).imm) ⟨2,11⟩ ∧
          frame = PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race)
            (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
            1 {} id tracker.global.nextPointerTag slotId (TypedRetagGeneric.protectedGlobal tracker.global fresh).nextPointerTag := by
  dsimp only
  obtain ⟨frame,site,machine,actual,pureTrace,shape,sourceSlot,destSlot,live,cached,types,typesEq,racePost,ghostPost,shallowPost,
    sharedTracker,tracked,defaultMode,next10,protectionsEq⟩ :=
    S05DiagnosticEntryPrefix.reaches_shared_site options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base 1 nonzero entry bounds before ghost shallow cachedAddress present enabled fresh tree parentEq nextEq protectedEq
      race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
      source (by decide) mode unchecked noGc fixed
  obtain ⟨updated,actual2,_⟩ := S05DiagnosticRootInvocation.enters options limits remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base 1 nonzero entry bounds before ghost shallow
    cachedAddress present enabled fresh tree parentEq nextEq protectedEq race metadata notConstructed retagCtx place layout
    slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh
    slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let raw := RawRootInvocation.root before place race
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
  let installed := PositiveRootInstalledFrame.installed raw adjusted 1 {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have frameEq : frame = installed := by
    have same := (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
    have rows := congrArg (fun s : RootState => s.stack.frames[0]?) same
    change some frame = some installed at rows
    exact Option.some.inj rows
  have installedShape := PositiveRootInstalledFrame.metadata raw adjusted 1 {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have body : site.body = RootBody.reflected.body.body := shape.body.trans (by rw [frameEq]; exact installedShape.1.trans raw.body)
  have identity : site.bodyIdentity = RootBody.reflected.body.identity := shape.identity.trans (by rw [frameEq]; exact installedShape.2.1.trans raw.identity)
  have callee : site.functionInstance = RootBody.reflected.functionInstance := shape.callee.trans (by rw [frameEq]; exact installedShape.2.2.1.trans raw.callee)
  have clocks : site.extra.dataRace = none := by
    rw [shape.extra,frameEq]
    exact installedShape.2.2.2.2.2.2.1.trans raw.noClocks
  let current := RootZeroCompleteState.tick options remaining span machine
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}
  have sourceTree : sourceEntry.allocation.extra = S05DiagnosticSharedRead.tree := by
    change S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2 = _
    rw [tree,parentEq]
    exact S05DiagnosticSharedRead.finalTree_eq tracker nextEq protectedEq
  have v1 : (1 : MIR.LocalId) < site.locals.size := by rw [shape.size]; decide
  have v12 : (12 : MIR.LocalId) < site.locals.size := by rw [shape.size]; decide
  have sourceCell := Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans sourceSlot)
  have destCell := Option.some.inj ((Array.getElem?_eq_getElem v12).symm.trans destSlot)
  have srcLive : site.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+0))) 2 ActualReferenceMetadata.reference).imm) := by
    rw [sourceCell]
    simp only [UInt64.add_zero]
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have room : sharedTracker.global.nextPointerTag.value < 18446744073709551615 := by rw [next10]; decide
  have query := RootReferenceFacts.compute_destination #[] site current body identity callee true
  have expression := S05DiagnosticSharedExpression.positive_rvalue options limits remaining span ctx debugOff cmp .Erased
    dynamicFuel validityFuel fuelEq validationEq base 0 2 id sourceEntry (by decide) (by simpa only [UInt64.add_zero] using nonzero)
    (by decide) #[] site current sharedTracker tracked defaultMode room tracker.global.nextPointerTag sourceTree nextEq next10
    protectionsEq rfl rfl bounds 12 rfl v1 v12 srcLive (by rw [sourceCell]) (by rw [destCell]) (by rw [destCell])
    query clocks ghostPost shallowPost cached live racePost types (by change (current.user.payload.payload.user.types.entries.any (·.value.ty == 4)) = false; rw [typesEq]; exact notConstructed)
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id sharedTracker.global.nextPointerTag) (Size.ofBytes (base+0))) 2 (RootReferenceInfo.layout true)
  let post := {ReferenceBorrowDriver.allocatedMachine current sharedTracker room with
    memory := RetagEntry.updatedMemory current.memory id sourceEntry (S05DiagnosticSharedExpression.child sourceEntry.allocation.extra
      sharedTracker.global.protectedTags tracker.global.nextPointerTag sharedTracker.global.nextPointerTag 0 2 .VisitChildrenOfAccessed).tree}
  let written := ActualLocalCopy.written site 12 (RootReferenceInfo.layout true) v12 value.imm
  have step := CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits
    #[] site written current post ⟨2,11⟩ ⟨12,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) shape.location
    (by simpa only [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using shape.location)
    (by rw [body]; exact RootReferenceFacts.statement true) expression
  have backend : machine.user.payload.payload.user.backend = .none := by
    have same := (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
    have userEq := congrArg (fun s : RootState => s.machine.user.payload.payload.user.backend) same
    exact userEq.trans (((RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.1).trans noBackend)
  have same := (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
  have machineUser : machine.user = (RawRootInvocation.machine #[] before).user :=
    congrArg (fun s : RootState => s.machine.user) same
  have machineThreads : machine.threads = (RawRootInvocation.machine #[] before).threads :=
    congrArg (fun s : RootState => s.machine.threads) same
  have postThreads : post.threads = (RawRootInvocation.machine #[] before).threads :=
    (RootZeroInvocationState.tick_fields options remaining span machine).2.2.2.1.trans machineThreads
  have postUnchecked : ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false := by
    unfold post current RootZeroCompleteState.tick SourceControl.accounted
    change ((config options (remaining+1) span).terminators.getControl
      ((config options (remaining+1) span).terminators.setControl
        (TerminatorClock.advance ((config options (remaining+1) span).terminators.getControl machine.user)) machine.user)).checkedArithmetic = false
    rw [CanonicalConfigFacts.actual_term_get_set]
    change ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
    rw [machineUser,RootZeroInvocationState.raw_control]
    exact unchecked
  have postNoGc : ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 := by
    unfold post current RootZeroCompleteState.tick SourceControl.accounted
    change ((config options (remaining+1) span).terminators.getControl
      ((config options (remaining+1) span).terminators.setControl
        (TerminatorClock.advance ((config options (remaining+1) span).terminators.getControl machine.user)) machine.user)).gcInterval = 0
    rw [CanonicalConfigFacts.actual_term_get_set]
    change ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
    rw [machineUser,RootZeroInvocationState.raw_control]
    exact noGc
  have postFixed : post.threads.fixedScheduling = true := by
    rw [postThreads]
    exact fixed
  have currentBackend : current.user.payload.payload.user.backend = .none := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have committed := StackPopRelease.lookup_commit_same current.memory id sourceEntry
    (S05DiagnosticSharedExpression.child sourceEntry.allocation.extra sharedTracker.global.protectedTags
      tracker.global.nextPointerTag sharedTracker.global.nextPointerTag 0 2 .VisitChildrenOfAccessed).tree
  refine ⟨frame,CopyHelperSteps.advance written ⟨2,11⟩,machine,post,actual,
    SuccessfulTrace.append pureTrace (.next step (.refl _)),rfl,body,identity,callee,?_,clocks,?_,?_,?_,cached,typesEq,
    racePost,ghostPost,shallowPost,currentBackend,postThreads,postUnchecked,postNoGc,postFixed,allocatedTracker sharedTracker room,rfl,defaultMode,?_,protectionsEq,site,shape,?_,frameEq⟩
  · simpa only [CopyHelperSteps.advance,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using shape.size
  · simp only [CopyHelperSteps.advance,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Array.getElem_set,ite_true]
    simp only [value,next10,UInt64.add_zero]
  · simpa only [CopyHelperSteps.advance,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Array.getElem_set,Nat.reduceEqDiff,ite_false] using shape.slot11
  · change (RetagEntry.updatedMemory current.memory id sourceEntry _).live.find? _ = _
    simpa only [StackPopRelease.commitTree,RetagEntry.updatedMemory,sourceEntry,nextEq,next10,protectionsEq] using committed
  · change TypedRetagEmpty.successorTag sharedTracker.global.nextPointerTag room = _
    simp only [TypedRetagEmpty.successorTag,next10,S05DiagnosticFnEntryRead.tag]
    rfl
  · simp only [written,value,next10,UInt64.add_zero]
end
end DuplicatePrefix.S05DiagnosticSharedStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S05DiagnosticSharedStep.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved diagnostic shared statement dependency {dependency}"
