import duplicate_prefix.RootAddPreparation
import duplicate_prefix.AddOutput
import duplicate_prefix.RootCopyPreparation
import duplicate_prefix.PositiveRootCopyBounds
import duplicate_prefix.RootAddPreparationEnd
import duplicate_prefix.RootPointerAssignment
import duplicate_prefix.RootPointerCastAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.PositiveRootAddToCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (count : UInt64) (temp16 : Immediate Provenance)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live16 : (frame.locals[16]'(by omega)).value=.live (.immediate temp16))
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤24→(frame.locals[i]'v)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨7,0⟩)
    (noClocks : frame.extra.dataRace=none) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (mode : tracker.retagMode=.Default) (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (all : CopyHelperCleanup.AllImmediate frame)
    (trackNone : frame.trackCallerArg=none) (relevant : frame.extra.userRelevance>0)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread)
    (top : thread.topUserRelevantFrame=some frames.size)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (backend : machine.user.payload.payload.user.backend=.none) (race : machine.dataRace=none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (raw : pointer=Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (positive : (0:UInt64)<count) (within : count≤len/2)
    (sliceBounds : offset.toNat+len.toNat≤entry.allocation.byteSize.bytes.toNat)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let resultValue : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+count)))
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine)
        (Storage.withCurrent frames result (AddOutput.machine options remaining span machine)) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧
      result.locals.size=25 ∧ result.location=.mir ⟨8,4⟩ ∧
      result.locals[17]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]?=some ⟨.live (.immediate (.scalar resultValue)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀i,i<16∨24<i→result.locals[i]?=frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result := by
  dsimp only
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨p,pt,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,ploc,p17,p18,p19,p21,p22,p23,pkeep,pa⟩ :=
    RootAddPreparation.executes_tracked options limits remaining span debugOff fuel validationFuel frames frame machine pointer count temp16 size
      live15 cache15 live16 live2 cache2 (by intro i valid lower upper;exact unused i valid lower (by omega))
      body identity callee location noClocks tracker tracked mode ghost shallow all
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have cell (n : Fin 25) {row : LocalState Provenance LocalLayout} (known : p.locals[n.val]?=some row) : (p.locals[n.val]'(vp n))=row :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp n)).symm.trans known)
  have cell21 := cell ⟨21,by decide⟩ p21
  have cell22 := cell ⟨22,by decide⟩ p22
  have cell23 := cell ⟨23,by decide⟩ p23
  have indexCount : RootCallerLocation.statementCount 7=13 := by with_unfolding_all rfl
  have protectedBounds := PositiveRootCopyBounds.guarded len count offset entry.allocation.byteSize.bytes within sliceBounds
  have addTrace := AddRootComplete.run options limits remaining span debugOff frames p machine tracker tracked pointer count (vp ⟨21,by decide⟩)
    (by rw [cell21]) (by rw [cell21]) (by rw [pex];exact noClocks) race (pb.trans body) (pi.trans identity) (pfn.trans callee)
    (ptrack.trans trackNone) (by simpa only [indexCount] using ploc) fuel validationFuel ghost shallow thread active top
    (by rw [pex];exact relevant) budget dispatch backend unchecked noGc fixed mode id tag base offset entry raw cached present
    (by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive) protectedBounds.1 protectedBounds.2.2.1 source cmp
    (vp ⟨22,by decide⟩) (vp ⟨23,by decide⟩) (by rw [cell22]) (by rw [cell22]) (by rw [cell23]) (by rw [cell23])
  let addedValue : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+count)))
  let added := AddOutput.caller p (vp ⟨21,by decide⟩) addedValue
  let am := AddOutput.machine options remaining span machine
  obtain ⟨ab,ai,afn,aex,arc,arp,ava,ali,asz,aloc⟩ := AddOutput.metadata p (vp ⟨21,by decide⟩) addedValue
  have addedSize : added.locals.size=25 := asz.trans psz
  have av (i : Fin 25) : i.val<added.locals.size := by rw [addedSize];exact i.isLt
  have same (n : Fin 25) (different : n.val≠21) : (added.locals[n.val]'(av n))=(p.locals[n.val]'(vp n)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (av n)).symm.trans ((AddOutput.other p _ addedValue n.val different).trans (Array.getElem?_eq_getElem (vp n))))
  have same2 : (p.locals[2]'(vp ⟨2,by decide⟩))=(frame.locals[2]'(vo ⟨2,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨2,by decide⟩)).symm.trans ((pkeep 2 (Or.inl (by decide))).trans (Array.getElem?_eq_getElem (vo ⟨2,by decide⟩))))
  have same24 : (p.locals[24]'(vp ⟨24,by decide⟩))=(frame.locals[24]'(vo ⟨24,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨24,by decide⟩)).symm.trans ((pkeep 24 (Or.inr (by decide))).trans (Array.getElem?_eq_getElem (vo ⟨24,by decide⟩))))
  have afterFields := AddOutput.preserved options remaining span machine
  obtain ⟨r,rt,shape⟩ := RootCopyPreparation.executes options limits remaining span debugOff fuel validationFuel frames added am count
    (.scalar pointer) (.scalar (.fromScalarInt (.ofUInt64 count))) addedSize
    (by rw [same ⟨2,by decide⟩ (by decide),same2];exact live2) (by rw [same ⟨2,by decide⟩ (by decide),same2];exact cache2)
    (by rw [same ⟨22,by decide⟩ (by decide),cell22]) (by rw [same ⟨23,by decide⟩ (by decide),cell23])
    (by rw [same ⟨24,by decide⟩ (by decide),same24,unused 24 (vo ⟨24,by decide⟩) (by decide) (by decide)])
    (by rw [same ⟨24,by decide⟩ (by decide),same24,unused 24 (vo ⟨24,by decide⟩) (by decide) (by decide)])
    (ab.trans (pb.trans body)) (ai.trans (pi.trans identity)) (afn.trans (pfn.trans callee)) aloc
    (by rw [aex,pex];exact noClocks) tracker (afterFields.2.1.trans tracked) mode
    (afterFields.2.2.2.2.2.1.trans ghost) (afterFields.2.2.2.2.2.2.1.trans shallow)
  have composed : SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames r am) :=
    SuccessfulTrace.append pt (SuccessfulTrace.append addTrace rt)
  have added21 : added.locals[21]?=some ⟨.live (.immediate (.scalar addedValue)),some CopyCompilerFacts.destPointerLayout⟩ :=
    (Array.getElem?_eq_getElem (av ⟨21,by decide⟩)).trans (congrArg some (AddOutput.slot21 p _ addedValue))
  refine ⟨r,composed,shape.body.trans (ab.trans pb),shape.identity.trans (ai.trans pi),shape.callee.trans (afn.trans pfn),
    shape.extra.trans (aex.trans pex),shape.destination.trans (arp.trans prp),shape.continuation.trans (arc.trans prc),
    shape.varargs.trans (ava.trans pva),shape.localsIdentity.trans (ali.trans pli),
    shape.trackedCaller.trans ((AddOutput.tracked_caller p _ addedValue).trans ptrack),shape.size,shape.location,?_,?_,?_,?_,shape.count,?_,
    shape.immediate (AddOutput.all_immediate p _ addedValue pa)⟩
  · exact (shape.kept 17 (by decide) (by decide) (by decide)).trans ((AddOutput.other p _ addedValue 17 (by decide)).trans p17)
  · exact (shape.kept 18 (by decide) (by decide) (by decide)).trans ((AddOutput.other p _ addedValue 18 (by decide)).trans p18)
  · exact (shape.kept 19 (by decide) (by decide) (by decide)).trans ((AddOutput.other p _ addedValue 19 (by decide)).trans p19)
  · exact (shape.kept 21 (by decide) (by decide) (by decide)).trans added21
  · intro i outside
    exact (shape.kept i (by omega) (by omega) (by omega)).trans
      ((AddOutput.other p _ addedValue i (by omega)).trans (pkeep i (by omega)))

#print axioms executes
end DuplicatePrefix.PositiveRootAddToCopy
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootAddToCopy.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual add-to-copy dependency {dependency}"
