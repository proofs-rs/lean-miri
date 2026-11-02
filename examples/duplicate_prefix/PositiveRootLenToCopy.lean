import duplicate_prefix.PositiveRootLenCall
import duplicate_prefix.PositiveRootSuccessToCopy
import duplicate_prefix.PositiveRootSuccessMasks
import duplicate_prefix.LenCallReturn
import duplicate_prefix.LenPushFacts
namespace DuplicatePrefix.PositiveRootLenToCopy
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend LenCallReturn NestedConstruction BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location3 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (cachedAddress : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : beforeMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : beforeMachine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread?=some thread) (cachedThread : thread.topUserRelevantFrame=some 0)
    (metadata : beforeMachine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty==4)=false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (count : UInt64) (countPositive : (0:UInt64)<count) (within : count≤len/2) (size : caller.locals.size=25)
    (source1 : (caller.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (caller.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (source2 : (caller.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (caller.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live0 : (caller.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (caller.locals[0]'(by omega)).layout=none)
    (live7 : (caller.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (caller.locals[7]'(by omega)).layout=none)
    (live8 : (caller.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (caller.locals[8]'(by omega)).layout=none)
    (live9 : (caller.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (caller.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (caller.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (caller.locals[10]'(by omega)).layout=none)
    (live13 : (caller.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (caller.locals[13]'(by omega)).layout=none)
    (dead15 : (caller.locals[15]'(by omega)).value=.dead) (cache15 : (caller.locals[15]'(by omega)).layout=none)
    (dead16 : (caller.locals[16]'(by omega)).value=.dead) (cache16 : (caller.locals[16]'(by omega)).layout=none)
    (unused : ∀i(v:i<caller.locals.size),17≤i→i≤24→(caller.locals[i]'v)=⟨.dead,none⟩)
    (trackNone : caller.trackCallerArg=none) (relevant : caller.extra.userRelevance>0) (all : CopyHelperCleanup.AllImmediate caller)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (free4 : tracker.global.protectedTags.contains (tags 4)=false)
    (next4 : TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh=tags 4)
    (fresh4 : (PositiveLenPost.trackerAfter tracker fresh id).global.nextPointerTag.value<18446744073709551615)
    (next5 : TypedRetagEmpty.successorTag (PositiveLenPost.trackerAfter tracker fresh id).global.nextPointerTag fresh4=tags 5)
    (fresh5 : (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh4).global.nextPointerTag.value<18446744073709551615) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
    let destinationValue : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))
    let finalTracker := AsMutRootOutput.held (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter tracker fresh id) fresh4) fresh5 id
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller beforeMachine) (Storage.withCurrent #[] result finalMachine) ∧
      PositiveRootSuccessProfile.FrameShape caller result pointer destinationValue count ∧
      PositiveRootSuccessProfile.MachineShape options remaining span beforeMachine finalMachine finalTracker thread tags id entry capacity offset len := by
  dsimp only
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨lm,lt,lmem,lborrow,lghost,lshallow,lrace,lfixed,lunchecked,lgc,laddr,ltypes,lbackend,lextras,lactive⟩ :=
    PositiveRootLenCall.returns_len options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds caller beforeMachine tracker enabled mask nextTag defaultMode fresh
      valid live uncached noClocks ghost shallow cachedAddress present race thread active cachedThread metadata notConstructed sourceBody identity callee located source
      sourceValid sourceLive sourceCached backend unchecked noGc fixed
  let lf := LenCallResultFrame.resultFrame caller valid len
  let ltracker := PositiveLenPost.trackerAfter tracker fresh id
  let inside := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))
  let afterTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 true))
  let le := {entry with allocation:=entry.allocation.setExtra afterTree}
  have lsz : lf.locals.size=25 := (LenCallResultFrame.size caller valid len).trans size
  have lv (i : Fin 25) : i.val<lf.locals.size := by rw [lsz];exact i.isLt
  have cv (i : Fin 25) : i.val<caller.locals.size := by rw [size];exact i.isLt
  have same (i : Fin 25) (different : i.val≠11) : (lf.locals[i.val]'(lv i))=(caller.locals[i.val]'(cv i)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (lv i)).symm.trans ((LenCallResultFrame.other caller valid len i.val different).trans (Array.getElem?_eq_getElem (cv i))))
  have cell11 : (lf.locals[11]'(lv ⟨11,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (lv ⟨11,by decide⟩)).symm.trans (LenCallResultFrame.value caller valid len))
  obtain ⟨lb,li,lfn,lex,lli,lrp,lrc,ltrack,lva,lloc⟩ := LenCallResultFrame.attributes caller valid len
  have lPresent : lm.memory.live.find? (fun row=>row.1==id)=some (id,le) := by
    rw [lmem]
    exact PositiveLenPost.buffer_lookup beforeMachine.memory id entry inside afterTree
  have lu : ∀i(v:i<lf.locals.size),17≤i→i≤24→(lf.locals[i]'v)=⟨.dead,none⟩ := by
    intro i good lower upper
    have old : i<caller.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem good,LenCallResultFrame.other caller valid len i (by omega),Array.getElem?_eq_getElem old,unused i old lower upper]
  obtain ⟨r,fm,st,sf,sm⟩ := PositiveRootSuccessToCopy.executes options limits remaining span source debugOff validityFuel validationEq lf lm len count within lsz
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    (by rw [same ⟨12,by decide⟩ (by decide)];exact sourceLive)
    (by rw [same ⟨13,by decide⟩ (by decide)];exact live13) (by rw [same ⟨13,by decide⟩ (by decide)];exact cache13)
    (by rw [same ⟨0,by decide⟩ (by decide)];exact live0) (by rw [same ⟨0,by decide⟩ (by decide)];exact cache0)
    (by rw [same ⟨7,by decide⟩ (by decide)];exact live7) (by rw [same ⟨7,by decide⟩ (by decide)];exact cache7)
    (by rw [same ⟨15,by decide⟩ (by decide)];exact dead15) (by rw [same ⟨15,by decide⟩ (by decide)];exact cache15)
    (by rw [same ⟨16,by decide⟩ (by decide)];exact dead16) (by rw [same ⟨16,by decide⟩ (by decide)];exact cache16)
    (by rw [same ⟨8,by decide⟩ (by decide)];exact live8) (by rw [same ⟨8,by decide⟩ (by decide)];exact cache8)
    (by rw [same ⟨9,by decide⟩ (by decide)];exact live9) (by rw [same ⟨9,by decide⟩ (by decide)];exact cache9)
    (by rw [same ⟨10,by decide⟩ (by decide)];exact live10) (by rw [same ⟨10,by decide⟩ (by decide)];exact cache10)
    (by rw [cell11]) (by rw [cell11]) (lb.trans sourceBody) (li.trans identity) (lfn.trans callee) lloc
    (LenCallResultFrame.all_immediate caller valid len all) (by rw [lex];exact noClocks) ltracker lborrow defaultMode
    lghost lshallow lunchecked lgc lfixed precise implicitWrites cmp dynamicFuel fuelEq tags distinct capacity base offset id le allocationSize rfl positive nonzero signedFits bounds
    (PositiveRootSuccessMasks.after_len_stage5 tags distinct tracker fresh id nextTag mask free4) next4 fresh4
    (by rw [same ⟨1,by decide⟩ (by decide)];exact source1) (by rw [same ⟨1,by decide⟩ (by decide)];exact cache1)
    (by rw [laddr];exact cachedAddress) lPresent lrace (ltypes ▸ metadata) (ltypes ▸ notConstructed) next5 fresh5 countPositive
    (by rw [same ⟨2,by decide⟩ (by decide)];exact source2) (by rw [same ⟨2,by decide⟩ (by decide)];exact cache2)
    lu (ltrack.trans trackNone) (by rw [lex];exact relevant) thread lactive cachedThread budget dispatchFuel (lbackend.trans backend)
  have frameShape : PositiveRootSuccessProfile.FrameShape caller r
      (Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset))))
      (Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))) count := {
    body:=sf.body.trans lb,identity:=sf.identity.trans li,callee:=sf.callee.trans lfn,extra:=sf.extra.trans lex,
    destination:=sf.destination.trans lrp,continuation:=sf.continuation.trans lrc,varargs:=sf.varargs.trans lva,
    localsIdentity:=sf.localsIdentity.trans lli,trackedCaller:=sf.trackedCaller.trans ltrack,size:=sf.size,location:=sf.location,
    slot0:=sf.slot0.trans (LenCallResultFrame.other caller valid len 0 (by decide)),
    slot1:=sf.slot1.trans (LenCallResultFrame.other caller valid len 1 (by decide)),
    slot2:=sf.slot2.trans (LenCallResultFrame.other caller valid len 2 (by decide)),
    slot13:=sf.slot13,slot15:=sf.slot15,slot17:=sf.slot17,slot18:=sf.slot18,slot19:=sf.slot19,slot21:=sf.slot21,slot24:=sf.slot24,immediate:=sf.immediate }
  have machineShape : PositiveRootSuccessProfile.MachineShape options remaining span beforeMachine fm
      (AsMutRootOutput.held (ReferenceBorrowDriver.allocatedTracker ltracker fresh4) fresh5 id) thread tags id entry capacity offset len := by
    refine {
      tracked:=sm.tracked,mask:=sm.mask,buffer:=?_,other:=?_,addresses:=sm.addresses.trans laddr,types:=sm.types.trans ltypes,
      backend:=sm.backend.trans lbackend,extras:=sm.extras.trans lextras,ghost:=sm.ghost,shallow:=sm.shallow,race:=sm.race,
      fixed:=sm.fixed,unchecked:=sm.unchecked,noGc:=sm.noGc,active:=sm.active }
    · simpa only [le,AllocationCopy.set_extra_twice] using sm.buffer
    · intro other otherEntry different initialPresent
      apply sm.other other otherEntry different
      rw [lmem]
      exact PositiveLenPost.other_lookup beforeMachine.memory id other entry otherEntry inside afterTree different initialPresent
  exact ⟨r,fm,SuccessfulTrace.append lt st,frameShape,machineShape⟩

#print axioms executes
end
end DuplicatePrefix.PositiveRootLenToCopy
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootLenToCopy.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual positive len-to-copy dependency {dependency}"
