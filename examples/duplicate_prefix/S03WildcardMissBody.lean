import duplicate_prefix.S03WildcardMissEmptyRootSafetyToLen
import duplicate_prefix.S03WildcardMissLenToReturn
import duplicate_prefix.GenericFunctionEntryNumerics

namespace DuplicatePrefix.S03WildcardMissBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootReferenceInfo
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual positive-count wildcard lookup-miss empty body reaches block10 via
Shared, len FnEntry/body/pop and rejection. Memory and every protector entry
are unchanged; exactly two fresh tags are consumed. Arbitrary return-place
borrow facts therefore retain the same trees and protector table. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (address count : UInt64) (nonzero : address≠0) (countNonzero : count≠0)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm))
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
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (cache0 : (frame.locals[0]'(by omega)).layout = none)
    (live13 : (frame.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (cache13 : (frame.locals[13]'(by omega)).layout = none) :
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTracker : MachineHooks.BorrowState,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      finalTracker.global = {tracker.global with nextPointerTag := finalTracker.global.nextPointerTag} ∧
      finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  obtain ⟨p,firstTrace,pb,pi,pfn,pex,prp,prc,pva,pli,psz,ploc,p0,p1,p2,p7,p8,p9,p10,p11,p12,p13,pAll⟩ :=
    S03WildcardMissEmptyRootSafetyToLen.executes options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
      frame machine address count nonzero countNonzero size source1 cache1 live2 cache2 dead3 cache3 dead4 dead5 cache4 cache5 unused
      body identity callee location noClocks all tracker tracked mode fresh ghost shallow unchecked noGc fixed addressMode miss metadata notConstructed
  let exprTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let exprMachine := ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span machine) tracker fresh
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  have fresh2 : exprTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
    rw [successor]
    exact tagRoomNext
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
      fg,fsh,fr,ff,fu,fnc,fa,ft,fb,fe,finalThread⟩ :=
    S03WildcardMissLenToReturn.to_return options limits remaining budget dispatchFuel span ctx debug cmp dynamicFuel validityFuel dynamicEq validityEq
      address nonzero p exprMachine exprTracker rfl mode fresh2 (pv ⟨11,by decide⟩) (by rw [cell11]) (by rw [cell11])
      (by rw [pex];exact noClocks)
      ((RootZeroCompleteState.tick_ghost options remaining span machine).trans ghost)
      ((RootZeroCompleteState.tick_shallow options remaining span machine).trans shallow)
      race thread activeThread topZero (by rw [addresses]; exact addressMode) (by
        have mem : exprMachine.memory = machine.memory := rfl
        rw [addresses,mem]; exact miss) (by rw [types];exact metadata) (by rw [types];exact notConstructed)
      (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc source (pv ⟨12,by decide⟩)
      (by rw [cell12]) (by rw [cell12]) (exprBackend.trans backend)
      ((RootZeroCompleteState.tick_flags options remaining span machine).1.trans unchecked)
      ((RootZeroCompleteState.tick_flags options remaining span machine).2.trans noGc) fixed
      count countNonzero psz pAll (by rw [p0eq];exact live0) (by rw [p0eq];exact cache0)
      (by rw [cell7]) (by rw [cell8]) (by rw [cell8]) (by rw [cell9]) (by rw [cell9])
      (by rw [cell10]) (by rw [cell10]) (by rw [p13eq];exact live13) (by rw [p13eq];exact cache13)
  let finalTracker := ReferenceBorrowDriver.allocatedTracker exprTracker fresh2
  have counter : finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 := by
    have second := GenericFunctionEntryNumerics.successor_value exprTracker.global.nextPointerTag fresh2
    change (TypedRetagEmpty.successorTag exprTracker.global.nextPointerTag fresh2).value.toNat = _
    change exprTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at successor
    omega
  refine ⟨result,finalMachine,finalTracker,SuccessfulTrace.append firstTrace rest,
    rb.trans pb,ri.trans pi,rfn.trans pfn,re.trans pex,rrp.trans prp,rrc.trans prc,rva.trans pva,rli.trans pli,rsz,rloc,r0,rAll,
    memoryEq,finalTracked,rfl,rfl,counter,fg,fsh,fr,ff,fu,fnc,fa.trans addresses,ft.trans types,fb.trans exprBackend,fe.trans extras,finalThread⟩

end
end DuplicatePrefix.S03WildcardMissBody
