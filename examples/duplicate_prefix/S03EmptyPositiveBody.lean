import duplicate_prefix.S03EmptySharedPrefix
import duplicate_prefix.S03EmptyNextLenInput
import duplicate_prefix.S03EmptyLenToReturn

namespace DuplicatePrefix.S03EmptyPositiveBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootReferenceInfo
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual positive-count empty body reaches block10 via Shared, len
FnEntry/body/pop and rejection. The second allocator Input and all post-call
permission/runtime facts are derived from initial data and numeric resources. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (parentTag newTag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset count : UInt64) (nonzero : base+offset≠0) (countNonzero : count≠0)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (cache4 : (frame.locals[4]'(by omega)).layout=none) (cache5 : (frame.locals[5]'(by omega)).layout=none)
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false)
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (ownerSource ownerSelected : Option UniIndex) (ownerMaximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (ownerPositive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      ownerSource ownerSelected ownerMaximum ownerOffset ownerLen)
    (owner : UniIndex)
    (ownerActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra owner .Write ownerOffset (ownerOffset+ownerLen))
    (zero : UniIndex) (zeroQuiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra zero)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (nodeRoomTwo : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (cache0 : (frame.locals[0]'(by omega)).layout = none)
    (live13 : (frame.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (cache13 : (frame.locals[13]'(by omega)).layout = none) :
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTree : BorrowTree, ∃ finalTracker : MachineHooks.BorrowState,
      finalTree = (S03EmptyNextLenInput.form entry.allocation.extra tracker.global borrowRuntime parentTag
        (nextTag.symm ▸ input) fresh nodeRoomTwo).after ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra finalTree}) ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree finalTracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree finalTracker.global.protectedTags
        ownerSource ownerSelected ownerMaximum ownerOffset ownerLen) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree owner .Write ownerOffset (ownerOffset+ownerLen) ∧
      S04ReturnReleaseInactive.Quiescent finalTree zero := by
  cases nextTag
  obtain ⟨p,⟨firstTrace,pb,pi,pfn,pex,prp,prc,pva,pli,psz,ploc,p0,p1,p2,p7,p8,p9,p10,p11,p12,p13,pAll⟩,
      exprRuntime,⟨exprPositive⟩,exprActive,exprQuiet⟩ := S03EmptySharedPrefix.with_observer
    options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
    frame machine parentTag tracker.global.nextPointerTag id entry base offset count nonzero countNonzero input size
    source1 cache1 live2 cache2 dead3 cache3 dead4 dead5 cache4 cache5 unused body identity callee location noClocks all tracker tracked mode
    rfl fresh cachedAddress present ghost shallow unchecked noGc fixed metadata notConstructed borrowRuntime nodeRoom
    ownerSource ownerSelected ownerMaximum ownerOffset ownerLen ownerPositive owner ownerActive zero zeroQuiet
  let exprTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let exprMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
    {ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span machine) tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry input.after}
  let exprEntry := {entry with allocation := entry.allocation.setExtra input.after}
  let input2 := S03EmptyNextLenInput.form entry.allocation.extra tracker.global borrowRuntime parentTag input fresh nodeRoomTwo
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  have fresh2 : exprTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
    rw [successor]
    exact tagRoomNext
  have room2 : exprEntry.allocation.extra.nodes.size+1 ≤ 4294967295 := by
    have growth := EmptyForestSharedPoolNext.node_size input
    have bound : EmptyForestSharedPoolNext.growth input ≤ 1 := by cases chosen : input.slot <;> simp only [EmptyForestSharedPoolNext.growth,chosen] <;> decide
    change input.after.nodes.size+1 ≤ _
    omega
  have pv (i : Fin 25) : i.val < p.locals.size := by rw [psz];exact i.isLt
  have fv (i : Fin 25) : i.val < frame.locals.size := by rw [size];exact i.isLt
  have p0eq : p.locals[0]'(pv ⟨0,by decide⟩) = frame.locals[0]'(fv ⟨0,by decide⟩) :=
    Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨0,by decide⟩)).symm.trans (p0.trans (Array.getElem?_eq_getElem (fv ⟨0,by decide⟩))))
  have p13eq : p.locals[13]'(pv ⟨13,by decide⟩) = frame.locals[13]'(fv ⟨13,by decide⟩) :=
    Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨13,by decide⟩)).symm.trans (p13.trans (Array.getElem?_eq_getElem (fv ⟨13,by decide⟩))))
  have cell7 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨7,by decide⟩)).symm.trans p7)
  have cell8 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨8,by decide⟩)).symm.trans p8)
  have cell9 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨9,by decide⟩)).symm.trans p9)
  have cell10 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨10,by decide⟩)).symm.trans p10)
  have cell11 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨11,by decide⟩)).symm.trans p11)
  have cell12 := Option.some.inj ((Array.getElem?_eq_getElem (pv ⟨12,by decide⟩)).symm.trans p12)
  have types : exprMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
    unfold exprMachine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have addresses : exprMachine.user.addresses = machine.user.addresses := by
    unfold exprMachine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : exprMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold exprMachine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have exprBackend : exprMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
    unfold exprMachine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  obtain ⟨result,finalMachine,rest,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,rAll,memoryEq,finalTracked,
      fg,fsh,fr,ff,fu,fnc,fa,ft,fb,fe,finalThread,finalRuntime,finalPositive,finalActive,finalQuiet⟩ :=
    S03EmptyLenToReturn.to_return options limits remaining budget dispatchFuel span ctx debug cmp dynamicFuel validityFuel dynamicEq validityEq
      tracker.global.nextPointerTag exprTracker.global.nextPointerTag id exprEntry base offset input2 nonzero p exprMachine exprTracker rfl rfl
      mode fresh2 (pv ⟨11,by decide⟩) (by rw [cell11]) (by rw [cell11]) (by rw [pex];exact noClocks)
      ((RootZeroCompleteState.tick_ghost options remaining span machine).trans ghost)
      ((RootZeroCompleteState.tick_shallow options remaining span machine).trans shallow)
      (by rw [addresses];exact cachedAddress) (MemoryCopyBridge.live_lookup_replaced machine.memory id exprEntry)
      race thread activeThread topZero (by rw [types];exact metadata) (by rw [types];exact notConstructed)
      (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc source (pv ⟨12,by decide⟩)
      (by rw [cell12]) (by rw [cell12]) (exprBackend.trans backend)
      ((RootZeroCompleteState.tick_flags options remaining span machine).1.trans unchecked)
      ((RootZeroCompleteState.tick_flags options remaining span machine).2.trans noGc) fixed
      exprRuntime room2 ownerSource ownerSelected ownerMaximum ownerOffset ownerLen exprPositive owner exprActive zero exprQuiet
      count countNonzero psz pAll (by rw [p0eq];exact live0) (by rw [p0eq];exact cache0)
      (by rw [cell7]) (by rw [cell8]) (by rw [cell8]) (by rw [cell9]) (by rw [cell9])
      (by rw [cell10]) (by rw [cell10]) (by rw [p13eq];exact live13) (by rw [p13eq];exact cache13)
  let finalTracker := PositiveLenPost.trackerAfter exprTracker fresh2 id
  refine ⟨result,finalMachine,input2.after,finalTracker,rfl,SuccessfulTrace.append firstTrace rest,
    rb.trans pb,ri.trans pi,rfn.trans pfn,re.trans pex,rrp.trans prp,rrc.trans prc,rva.trans pva,rli.trans pli,rsz,rloc,r0,rAll,
    ?_,finalTracked,rfl,fg,fsh,fr,ff,fu,fnc,fa.trans addresses,ft.trans types,fb.trans exprBackend,fe.trans extras,
    finalThread,finalRuntime,finalPositive,finalActive,finalQuiet⟩
  rw [memoryEq]
  exact MemoryCopyBridge.live_lookup_replaced _ id {entry with allocation := entry.allocation.setExtra input2.after}

end
end DuplicatePrefix.S03EmptyPositiveBody
