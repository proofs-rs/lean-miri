import duplicate_prefix.AsMutRootOutput
import duplicate_prefix.PositiveRootAddToCopy
namespace DuplicatePrefix.PositiveRootAsMutToCopy
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (cachedAddress : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : beforeMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : beforeMachine.dataRace = none)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller beforeMachine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller beforeMachine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread? = some thread)
    (cachedThread : thread.topUserRelevantFrame = some 0)
    (size : caller.locals.size=25) (count : UInt64) (countPositive : (0:UInt64)<count) (within : count≤len/2)
    (live2 : (caller.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (caller.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (unused : ∀i(v:i<caller.locals.size),17≤i→i≤24→(caller.locals[i]'v)=⟨.dead,none⟩)
    (trackNone : caller.trackCallerArg=none) (relevant : caller.extra.userRelevance>0)
    (all : CopyHelperCleanup.AllImmediate caller) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
    let resultValue : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))
    ∃ helperDone result,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[] result
          (AddOutput.machine options remaining span (AsMutRootOutput.machine options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len helperDone thread))) ∧
      result.body=caller.body ∧ result.bodyIdentity=caller.bodyIdentity ∧ result.functionInstance=caller.functionInstance ∧
      result.extra=caller.extra ∧ result.returnPlace=caller.returnPlace ∧ result.returnContinuation=caller.returnContinuation ∧
      result.vaList=caller.vaList ∧ result.localsIdentity=caller.localsIdentity ∧ result.trackCallerArg=caller.trackCallerArg ∧
      result.locals.size=25 ∧ result.location=.mir ⟨8,4⟩ ∧
      result.locals[15]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]?=some ⟨.live (.immediate (.scalar resultValue)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀i,i<15∨24<i→result.locals[i]?=caller.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result := by
  dsimp only
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
  obtain ⟨helperDone,asmutTrace⟩ := AsMutRootOutput.run options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds caller beforeMachine tracker enabled defaultMode mask nextTag fresh
    body identity callee located source valid16 value16 cached16 destValid destLive uncached callerClocks ghost shallow cachedAddress present race backend metadata notConstructed
    unchecked noGc fixed thread active cachedThread
  let a := AsMutRootOutput.caller caller destValid pointer
  let am := AsMutRootOutput.machine options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len helperDone thread
  let heldTracker := AsMutRootOutput.held tracker fresh id
  let finalTree := NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
  let newEntry := {entry with allocation:=entry.allocation.setExtra finalTree}
  have fields := AsMutRootOutput.preserved options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len helperDone thread
  obtain ⟨ab,ai,afn,aex,arc,arp,ava,ali,asz,aloc⟩ := AsMutRootOutput.caller_metadata caller destValid pointer
  have aSize : a.locals.size=25 := asz.trans size
  have av (i : Fin 25) : i.val<a.locals.size := by rw [aSize];exact i.isLt
  have cv (i : Fin 25) : i.val<caller.locals.size := by rw [size];exact i.isLt
  have same (n : Fin 25) (different : n.val≠15) : (a.locals[n.val]'(av n))=(caller.locals[n.val]'(cv n)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (av n)).symm.trans ((AsMutRootOutput.caller_other caller destValid pointer n.val different).trans (Array.getElem?_eq_getElem (cv n))))
  have source15 : (a.locals[15]'(av ⟨15,by decide⟩))=⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ :=
    AsMutRootOutput.caller_slot caller destValid pointer
  have activeAfter : am.threads.activeThread?=some thread := AsMutRootOutput.active options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len helperDone thread active cachedThread
  have amUnchecked : (cfg.terminators.getControl am.user).checkedArithmetic=false := by
    rw [AsMutRootOutput.control];exact unchecked
  have amNoGc : (cfg.terminators.getControl am.user).gcInterval=0 := by
    rw [AsMutRootOutput.control];exact noGc
  have unusedA : ∀i(v:i<a.locals.size),17≤i→i≤24→(a.locals[i]'v)=⟨.dead,none⟩ := by
    intro i valid lower upper
    have old : i<caller.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,AsMutRootOutput.caller_other caller destValid pointer i (by omega),Array.getElem?_eq_getElem old,unused i old lower upper]
  obtain ⟨r,rt,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r17,r18,r19,r21,r24,rkeep,ra⟩ :=
    PositiveRootAddToCopy.executes options limits remaining span debugOff validityFuel validationEq #[] a am pointer count
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
      aSize (by rw [source15]) (by rw [source15]) (by rw [same ⟨16,by decide⟩ (by decide)];exact value16)
      (by rw [same ⟨2,by decide⟩ (by decide)];exact live2) (by rw [same ⟨2,by decide⟩ (by decide)];exact cache2) unusedA
      (ab.trans body) (ai.trans identity) (afn.trans callee) aloc (by rw [aex];exact callerClocks) heldTracker fields.1 defaultMode
      (fields.2.2.2.2.1.trans ghost) (fields.2.2.2.2.2.1.trans shallow) (AsMutRootOutput.all_immediate caller destValid pointer all)
      ((AsMutRootOutput.caller_track caller destValid pointer).trans trackNone) (by rw [aex];exact relevant)
      thread activeAfter cachedThread budget dispatchFuel (fields.2.2.2.2.2.2.2.1.trans backend) (fields.2.1.trans race)
      amUnchecked amNoGc (fields.2.2.1.trans fixed) id (tags 5) base offset len newEntry rfl
      (by rw [fields.2.2.2.1];exact cachedAddress)
      (AsMutRootOutput.buffer_lookup options remaining span caller destValid beforeMachine tracker fresh id entry tags capacity offset len helperDone thread)
      countPositive within (by change offset.toNat+len.toNat≤entry.allocation.byteSize.bytes.toNat;rw [allocationSize];exact bounds) source cmp
  refine ⟨helperDone,r,SuccessfulTrace.append asmutTrace rt,rb.trans ab,ri.trans ai,rfn.trans afn,rex.trans aex,
    rrp.trans arp,rrc.trans arc,rva.trans ava,rli.trans ali,rtrack.trans (AsMutRootOutput.caller_track caller destValid pointer),rsz,rloc,?_,r17,r18,r19,r21,r24,?_,ra⟩
  · exact (rkeep 15 (Or.inl (by decide))).trans ((Array.getElem?_eq_getElem (av ⟨15,by decide⟩)).trans (congrArg some source15))
  · intro i outside
    exact (rkeep i (by omega)).trans (AsMutRootOutput.caller_other caller destValid pointer i (by omega))

#print axioms executes
end
end DuplicatePrefix.PositiveRootAsMutToCopy
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootAsMutToCopy.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual asmut-to-copy dependency {dependency}"
