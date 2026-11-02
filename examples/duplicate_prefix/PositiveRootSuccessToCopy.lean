import duplicate_prefix.PositiveRootMutableBorrow
import duplicate_prefix.PositiveRootAsMutToCopy
import duplicate_prefix.PositiveRootSuccessProfile
import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.RootMutPreparation
import duplicate_prefix.PositiveRootGuardBlock
import duplicate_prefix.EmptyRootSafetyFalse
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveRootSuccessToCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState Miri.TreeBorrows
private theorem slot_eq (a b : Array α) (i : Nat) (va : i<a.size) (vb : i<b.size)
    (same : a[i]?=b[i]?) : (a[i]'va)=(b[i]'vb) :=
  Option.some.inj ((Array.getElem?_eq_getElem va).symm.trans (same.trans (Array.getElem?_eq_getElem vb)))

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (within : count≤len/2) (size : frame.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live11 : (frame.locals[11]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (cache11 : (frame.locals[11]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨3,0⟩)
    (all : CopyHelperCleanup.AllImmediate frame) (noClocks : frame.extra.dataRace=none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (cmp : ProjectionMetadataFacts.NullComparator) (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (tags : Fin 6→BorTag) (distinct : Function.Injective tags)
    (capacity base offset : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize=Size.ofBytes capacity)
    (tree : entry.allocation.extra=RootReferenceTrees.initialTree false tags capacity offset len)
    (positive : (0:UInt64)<len) (nonnull : base+offset≠0) (signedFits : len.toNat<9223372036854775808)
    (bounds : offset.toNat+len.toNat≤capacity.toNat)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag=tags 4) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (race : machine.dataRace=none)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty==4)=false)
    (helperTag : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)=tags 5)
    (helperFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value<18446744073709551615)
    (countPositive : (0:UInt64)<count)
    (source2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤24→(frame.locals[i]'v)=⟨.dead,none⟩)
    (trackNone : frame.trackCallerArg=none) (relevant : frame.extra.userRelevance>0)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread?=some thread)
    (cachedThread : thread.topUserRelevantFrame=some 0)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (backend : machine.user.payload.payload.user.backend=.none) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
    let destinationValue : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))
    let finalTracker := AsMutRootOutput.held (ReferenceBorrowDriver.allocatedTracker tracker fresh) helperFresh id
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      PositiveRootSuccessProfile.FrameShape frame result pointer destinationValue count ∧
      PositiveRootSuccessProfile.MachineShape options remaining span machine finalMachine finalTracker thread tags id entry capacity offset len := by
  dsimp only
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let m2 := tick options remaining span (tick options remaining span machine)
  let value := RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference
  let finalTree5 := RootReferenceTrees.finalTree false tags capacity offset len
  let bm := {ReferenceBorrowDriver.allocatedMachine m2 tracker fresh with memory:=RetagEntry.updatedMemory machine.memory id entry finalTree5}
  let bt := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let be := {entry with allocation:=entry.allocation.setExtra finalTree5}
  obtain ⟨p,pt,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,ploc,p0,p1,p2,p13,p15,p16,pkeep,pa⟩ :=
    PositiveRootMutableBorrow.executes options limits remaining span source debug fuel fuelEq frame machine len count within size temp12
      live12 live13 cache13 live0 cache0 live7 cache7 dead15 cache15 dead16 cache16 live8 cache8 live9 cache9 live10 cache10 live11 cache11
      body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed precise implicitWrites cmp dynamicFuel dynamicEq
      tags distinct capacity base offset id entry allocationSize tree positive nonnull signedFits bounds (by intro i hi;exact mask i (by omega))
      nextTag fresh source1 cache1 cachedAddress present race metadata notConstructed
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have same2 : (p.locals[2]'(vp ⟨2,by decide⟩))=(frame.locals[2]'(vo ⟨2,by decide⟩)) := slot_eq _ _ _ _ _ p2
  have cell15 : (p.locals[15]'(vp ⟨15,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨15,by decide⟩)).symm.trans p15)
  have cell16 : (p.locals[16]'(vp ⟨16,by decide⟩))=⟨.live (.immediate value.imm),some ActualReferenceMetadata.reference⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨16,by decide⟩)).symm.trans p16)
  have ghost2 : bm.user.payload.ghost=false := (tick_ghost options remaining span _).trans ((tick_ghost options remaining span _).trans ghost)
  have shallow2 : bm.user.payload.validation=.Shallow := (tick_shallow options remaining span _).trans ((tick_shallow options remaining span _).trans shallow)
  have addresses : bm.user.addresses=machine.user.addresses := by
    unfold bm m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have types : bm.user.payload.payload.user.types=machine.user.payload.payload.user.types := by
    unfold bm m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extrasEq : bm.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
    unfold bm m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have backendEq : bm.user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold bm m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have unchecked2 : (cfg.terminators.getControl bm.user).checkedArithmetic=false :=
    (tick_flags options remaining span _).1.trans ((tick_flags options remaining span _).1.trans unchecked)
  have noGc2 : (cfg.terminators.getControl bm.user).gcInterval=0 :=
    (tick_flags options remaining span _).2.trans ((tick_flags options remaining span _).2.trans noGc)
  have present5 : bm.memory.live.find? (fun row=>row.1==id)=some (id,be) := MemoryCopyBridge.live_lookup_replaced _ id _
  have unusedP : ∀i(v:i<p.locals.size),17≤i→i≤24→(p.locals[i]'v)=⟨.dead,none⟩ := by
    intro i valid lower upper
    have old : i<frame.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,pkeep i lower,Array.getElem?_eq_getElem old,unused i old lower upper]
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  obtain ⟨helperDone,r,rt,rb,ri,rfn,rex,rrp,rrc,rva,rli,rtrack,rsz,rloc,r15,r17,r18,r19,r21,r24,rkeep,ra⟩ :=
    PositiveRootAsMutToCopy.executes options limits remaining budget dispatch span ctx debug cmp dynamicFuel fuel dynamicEq fuelEq tags distinct id be capacity base offset len
      rfl allocationSize positive nonnull signedFits bounds p bm bt rfl mode mask helperTag helperFresh
      (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc source (vp ⟨16,by decide⟩)
      (by rw [cell16]) (by rw [cell16]) (vp ⟨15,by decide⟩) (by rw [cell15]) (by rw [cell15])
      (by rw [pex];exact noClocks) ghost2 shallow2 (by rw [addresses];exact cachedAddress) present5 race (backendEq.trans backend)
      (by change bm.user.payload.payload.user.types.metadata=_;rw [types];exact metadata)
      (by change bm.user.payload.payload.user.types.entries.any (·.value.ty==4)=false;rw [types];exact notConstructed)
      unchecked2 noGc2 fixed thread active cachedThread psz count countPositive within
      (by rw [same2];exact source2) (by rw [same2];exact cache2) unusedP (ptrack.trans trackNone) (by rw [pex];exact relevant) pa
  let am := AsMutRootOutput.machine options remaining span p (vp ⟨15,by decide⟩) bm bt helperFresh id be tags capacity offset len helperDone thread
  let fm := AddOutput.machine options remaining span am
  let ft := AsMutRootOutput.held bt helperFresh id
  let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
  let destinationValue : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))
  have shape : PositiveRootSuccessProfile.FrameShape frame r pointer destinationValue count := {
    body:=rb.trans pb, identity:=ri.trans pi, callee:=rfn.trans pfn, extra:=rex.trans pex,
    destination:=rrp.trans prp, continuation:=rrc.trans prc, varargs:=rva.trans pva, localsIdentity:=rli.trans pli,
    trackedCaller:=rtrack.trans ptrack, size:=rsz, location:=rloc,
    slot0:=(rkeep 0 (Or.inl (by decide))).trans p0,
    slot1:=(rkeep 1 (Or.inl (by decide))).trans p1,
    slot2:=(rkeep 2 (Or.inl (by decide))).trans p2,
    slot13:=(rkeep 13 (Or.inl (by decide))).trans p13,
    slot15:=r15,slot17:=r17,slot18:=r18,slot19:=r19,slot21:=r21,slot24:=r24,immediate:=ra }
  have af := AsMutRootOutput.preserved options remaining span p (vp ⟨15,by decide⟩) bm bt helperFresh id be tags capacity offset len helperDone thread
  have df := AddOutput.preserved options remaining span am
  have post : PositiveRootSuccessProfile.MachineShape options remaining span machine fm ft thread tags id entry capacity offset len := by
    refine {
      tracked:=df.2.1.trans af.1,
      mask:=AsMutRootOutput.mask_after tags distinct bt helperFresh id helperTag mask,
      buffer:=?_,other:=?_,addresses:=df.2.2.2.2.1.trans (af.2.2.2.1.trans addresses),
      types:=df.2.2.2.2.2.2.2.2.2.trans (af.2.2.2.2.2.2.1.trans types),
      backend:=df.2.2.2.2.2.2.2.1.trans (af.2.2.2.2.2.2.2.1.trans backendEq),
      extras:=df.2.2.2.2.2.2.2.2.1.trans (af.2.2.2.2.2.2.2.2.trans extrasEq),
      ghost:=df.2.2.2.2.2.1.trans (af.2.2.2.2.1.trans ghost2),
      shallow:=df.2.2.2.2.2.2.1.trans (af.2.2.2.2.2.1.trans shallow2),
      race:=df.2.2.2.1.trans (af.2.1.trans race),fixed:=?_,unchecked:=?_,noGc:=?_,active:=?_ }
    · rw [df.1]
      have result := AsMutRootOutput.buffer_lookup options remaining span p (vp ⟨15,by decide⟩) bm bt helperFresh id be tags capacity offset len helperDone thread
      simpa only [be,AllocationCopy.set_extra_twice] using result
    · intro other otherEntry different initialPresent
      rw [df.1]
      have borrowedPresent : bm.memory.live.find? (fun row=>row.1==other)=some (other,otherEntry) :=
        StackPopRelease.lookup_commit_other machine.memory id other entry otherEntry finalTree5 different initialPresent
      exact AsMutRootOutput.other_lookup options remaining span p (vp ⟨15,by decide⟩) bm bt helperFresh id be tags capacity offset len helperDone thread other otherEntry different borrowedPresent
    · rw [df.2.2.1]
      exact af.2.2.1.trans fixed
    · change (cfg.terminators.getControl (AddOutput.machine options remaining span am).user).checkedArithmetic=false
      rw [AddOutput.control,AsMutRootOutput.control]
      exact unchecked2
    · change (cfg.terminators.getControl (AddOutput.machine options remaining span am).user).gcInterval=0
      rw [AddOutput.control,AsMutRootOutput.control]
      exact noGc2
    · rw [df.2.2.1]
      exact AsMutRootOutput.active options remaining span p (vp ⟨15,by decide⟩) bm bt helperFresh id be tags capacity offset len helperDone thread active cachedThread
  exact ⟨r,fm,SuccessfulTrace.append pt rt,shape,post⟩

#print axioms executes
end DuplicatePrefix.PositiveRootSuccessToCopy
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootSuccessToCopy.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved full positive root pre-copy dependency {dependency}"
