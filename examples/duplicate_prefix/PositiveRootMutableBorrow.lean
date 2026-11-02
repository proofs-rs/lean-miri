import duplicate_prefix.PositiveRootMutablePreparation
import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.RootMutPreparation
import duplicate_prefix.PositiveRootGuardBlock
import duplicate_prefix.EmptyRootSafetyFalse
import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveRootMutableBorrow
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
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 4 false)
    (nextTag : tracker.global.nextPointerTag=tags 4) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (race : machine.dataRace=none)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty==4)=false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let value := RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference
    let outputMachine := {ReferenceBorrowDriver.allocatedMachine (tick options remaining span (tick options remaining span machine)) tracker fresh with
      memory:=RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree false tags capacity offset len)}
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result outputMachine) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.trackCallerArg=frame.trackCallerArg ∧
      result.locals.size=25 ∧ result.location=.mir ⟨6,8⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate value.imm),some ActualReferenceMetadata.reference⟩ ∧
      (∀i,17≤i→result.locals[i]?=frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result := by
  dsimp only
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let m2 := tick options remaining span (tick options remaining span machine)
  let value := RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference
  obtain ⟨p,pt,pb,pi,pfn,pex,prp,prc,pva,pli,ptrack,psz,ploc,p0,p1,p2,p13,p15,p16,pkeep,pa⟩ :=
    PositiveRootMutablePreparation.executes options limits remaining span source debug fuel fuelEq frame machine len count within size temp12
      live12 live13 cache13 live0 cache0 live7 cache7 dead15 cache15 dead16 cache16 live8 cache8 live9 cache9 live10 cache10 live11 cache11
      body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have vo (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have same1 : (p.locals[1]'(vp ⟨1,by decide⟩))=(frame.locals[1]'(vo ⟨1,by decide⟩)) := slot_eq _ _ _ _ _ p1
  have cell16 : (p.locals[16]'(vp ⟨16,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨16,by decide⟩)).symm.trans p16)
  have ghost2 : m2.user.payload.ghost=false := (tick_ghost options remaining span _).trans ((tick_ghost options remaining span _).trans ghost)
  have shallow2 : m2.user.payload.validation=.Shallow := (tick_shallow options remaining span _).trans ((tick_shallow options remaining span _).trans shallow)
  have addresses : m2.user.addresses=machine.user.addresses := by
    unfold m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have types : m2.user.payload.payload.user.types=machine.user.payload.payload.user.types := by
    unfold m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have memoryEq : m2.memory=machine.memory := by rfl
  have refStep := RootReferenceBorrow.positive_statement options limits remaining span precise implicitWrites debug cmp false
    dynamicFuel fuel dynamicEq fuelEq tags distinct capacity base offset len id entry allocationSize tree positive nonnull signedFits bounds
    #[] p m2 (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc tracker tracked mode mask nextTag fresh
    (vp ⟨1,by decide⟩) (vp ⟨16,by decide⟩) (by rw [same1];exact source1) (by rw [same1];exact cache1)
    (by simpa only [RootReferenceFacts.destination,Bool.false_eq_true,ite_false] using congrArg (fun row=>row.value) cell16)
    (by simpa only [RootReferenceFacts.destination,Bool.false_eq_true,ite_false] using congrArg (fun row=>row.layout) cell16)
    (by rw [pex];exact noClocks) ghost2 shallow2 (by rw [addresses];exact cachedAddress) present race
    (by change m2.user.payload.payload.user.types.metadata=_;rw [types];exact metadata) (by change m2.user.payload.payload.user.types.entries.any (·.value.ty==4)=false;rw [types];exact notConstructed)
  let result := CopyHelperSteps.advance (ActualLocalCopy.written p 16 ActualReferenceMetadata.reference (vp ⟨16,by decide⟩) value.imm) ⟨6,7⟩
  let outputMachine := {ReferenceBorrowDriver.allocatedMachine m2 tracker fresh with memory:=RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree false tags capacity offset len)}
  have actual : ExecutionMachine.step cfg limits () (Storage.withCurrent #[] p m2)=(Storage.withCurrent #[] result outputMachine,.ok true) := by
    simpa only [cfg,result,outputMachine,value,RootReferenceFacts.destination,RootReferenceFacts.location,RootReferenceTrees.nextIndex,
      RootReferenceInfo.layout,Bool.false_eq_true,ite_false,memoryEq,ActualReferenceContext.config] using refStep
  have history := SuccessfulTrace.append pt (.next actual (.refl _))
  have resultAll : CopyHelperCleanup.AllImmediate result := LocalDirectness.written_at p 16 ActualReferenceMetadata.reference value.imm (vp ⟨16,by decide⟩) ⟨6,8⟩ pa
  generalize finalEq : result=final at history resultAll
  refine ⟨final,history,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,resultAll⟩
  all_goals rw [←finalEq]
  all_goals simp only [result,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set,Array.getElem?_set,Array.getElem_set]
  all_goals try first | exact pb | exact pi | exact pfn | exact pex | exact prp | exact prc | exact pva | exact pli | exact ptrack | exact psz | rfl
  all_goals try simp only [Nat.reduceEqDiff,eq_self_iff_true,ite_true,ite_false]
  all_goals try first | exact p0 | exact p1 | exact p2 | exact p13 | exact p15 | rfl
  intro i lower
  simpa [show 16≠i by omega] using pkeep i lower

#print axioms executes
end DuplicatePrefix.PositiveRootMutableBorrow
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootMutableBorrow.executes) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved actual mutable root borrow dependency {dependency}"
