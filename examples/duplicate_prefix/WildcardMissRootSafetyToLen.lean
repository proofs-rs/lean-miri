import duplicate_prefix.WildcardMissRootSafetyBeforeLen
import duplicate_prefix.EmptyRootSafetyInitial
import duplicate_prefix.RootReferenceZeroBorrow
import duplicate_prefix.SuccessfulTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.WildcardMissRootSafetyToLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootReferenceInfo

theorem executes
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
    (miss : WildcardMissAddress.Miss machine.user.addresses address)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span machine) tracker fresh)) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨2,12⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
      result.locals[13]?=frame.locals[13]? ∧ CopyHelperCleanup.AllImmediate result := by
  let f := {EmptyRootSafetyInitialState.guardFrame frame size count with location:=FrameLocation.mir ⟨2,0⟩}
  let m := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨initial,b,i,fn,ex,rp,rc,va,li,sz,s0,s1,s2,keep,fa⟩ := EmptyRootSafetyInitial.executes
    options limits remaining span source debug validityFuel validityEq frame machine count countNonzero body identity callee location
    size dead3 dead4 dead5 cache4 cache5 live2 cache2 noClocks all tracker tracked mode ghost shallow unchecked noGc fixed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,s4,s5,_⟩ := EmptyRootSafetyInitialState.shape frame size count
  have vf (n : Fin 25) : n.val<f.locals.size := by rw [sz];exact n.isLt
  have vo (n : Fin 25) : n.val<frame.locals.size := by rw [size];exact n.isLt
  have original1 : (f.locals[1]'(vf ⟨1,by decide⟩))=(frame.locals[1]'(vo ⟨1,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨1,by decide⟩)).symm.trans (s1.trans (Array.getElem?_eq_getElem (vo ⟨1,by decide⟩))))
  have original2 : (f.locals[2]'(vf ⟨2,by decide⟩))=(frame.locals[2]'(vo ⟨2,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨2,by decide⟩)).symm.trans (s2.trans (Array.getElem?_eq_getElem (vo ⟨2,by decide⟩))))
  have slot3 : (f.locals[3]'(vf ⟨3,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨3,by decide⟩)).symm.trans (EmptyRootSafetyInitialState.slot3 frame size count cache3))
  have slot4 : (f.locals[4]'(vf ⟨4,by decide⟩))=⟨.live (.immediate (.scalar (.fromBool (count==0)))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨4,by decide⟩)).symm.trans s4)
  have slot5 : (f.locals[5]'(vf ⟨5,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vf ⟨5,by decide⟩)).symm.trans s5)
  have fu : ∀id(valid:id<f.locals.size),7≤id→id≤12→(f.locals[id]'valid)=⟨.dead,none⟩ := by
    intro id valid low high
    have old : id<frame.locals.size := by omega
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid,keep id (by omega) (by omega) (by omega),Array.getElem?_eq_getElem old,unused id old low high]
  have types : m.user.payload.payload.user.types=machine.user.payload.payload.user.types := by
    unfold m RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have addresses : m.user.addresses=machine.user.addresses := by
    unfold m RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have modeM : m.user.addresses.provenanceMode ≠ .strict := by rw [addresses];exact addressMode
  have missM : WildcardMissAddress.Miss m.user.addresses address := by rw [addresses];exact miss
  obtain ⟨result,rest,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,r1,r2,r7,r8,r9,r10,r11,r12,r13,ra⟩ :=
    WildcardMissRootSafetyBeforeLen.executes options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
      f m address count nonzero (.scalar (.fromBool (count==0))) (.scalar (.fromScalarInt (.ofUInt64 count))) sz
      (by rw [original1];exact source1) (by rw [original1];exact cache1)
      (by rw [original2];exact live2) (by rw [original2];exact cache2)
      (by rw [slot3]) (by rw [slot3]) (by rw [slot4]) (by rw [slot5]) fu
      (b.trans body) (i.trans identity) (fn.trans callee) rfl (by rw [ex];exact noClocks) fa tracker tracked mode fresh
      ((RootZeroCompleteState.tick_ghost options remaining span machine).trans ghost)
      ((RootZeroCompleteState.tick_shallow options remaining span machine).trans shallow) modeM missM (types ▸ metadata) (types ▸ notConstructed)
  exact ⟨result,SuccessfulTrace.append initial rest,rb.trans b,ri.trans i,rfn.trans fn,re.trans ex,rrp.trans rp,rrc.trans rc,
    rva.trans va,rli.trans li,rsz,rloc,r0.trans s0,r1.trans s1,r2.trans s2,r7,r8,r9,r10,r11,r12,
    r13.trans (keep 13 (by decide) (by decide) (by decide)),ra⟩

#print axioms executes
end DuplicatePrefix.WildcardMissRootSafetyToLen
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.WildcardMissRootSafetyToLen.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual empty-slice root prefix dependency {dependency}"
