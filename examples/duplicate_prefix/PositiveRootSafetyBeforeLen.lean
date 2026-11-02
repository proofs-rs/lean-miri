import duplicate_prefix.CopyHelperCleanup
import duplicate_prefix.RootLenPrefix
import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.SuccessfulTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveRootSafetyBeforeLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootReferenceInfo

theorem executes_preserving
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity base offset len count : UInt64) (nonzero : base+offset≠0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (tree : entry.allocation.extra = RootReferenceTrees.initialTree true tags capacity offset len)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value=.live (.immediate .uninit)) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (live4 : (frame.locals[4]'(by omega)).value=.live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value=.live (.immediate temp5))
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨2,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 2 false)
    (nextTag : tracker.global.nextPointerTag = tags 2)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
        memory := RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree true tags capacity offset len)}) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨2,12⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
      result.locals[13]?=frame.locals[13]? ∧ CopyHelperCleanup.AllImmediate result) ∧ result.trackCallerArg = frame.trackCallerArg ∧
      (∀ index,13 ≤ index → result.locals[index]? = frame.locals[index]?) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have valid (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  obtain ⟨p,⟨pt,pb,pi,pfn,pex,prp,prc,psz,ploc,p0,p1,p2,p7,p8,p9,p10,p11,p12,p13,pva,pli,pa⟩,pTrack,pKeep⟩ :=
    RootLenPrefix.executes_preserving options limits remaining span source debug validityFuel validityEq #[] frame machine count temp4 temp5 size
      live2 cache2 live3 cache3 live4 live5 unused body identity callee location noClocks tracker tracked mode ghost shallow all
  have vp (i : Fin 25) : i.val<p.locals.size := by rw [psz];exact i.isLt
  have same1 : (p.locals[1]'(vp ⟨1,by decide⟩))=(frame.locals[1]'(valid ⟨1,by decide⟩)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨1,by decide⟩)).symm.trans (p1.trans (Array.getElem?_eq_getElem (valid ⟨1,by decide⟩))))
  have slot12 : (p.locals[12]'(vp ⟨12,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vp ⟨12,by decide⟩)).symm.trans p12)
  have ref := RootReferenceBorrow.positive_statement options limits remaining span precise implicitWrites debug cmp true
    dynamicFuel validityFuel dynamicEq validityEq tags distinct capacity base offset len id entry allocationSize tree positive nonzero signedFits bounds
    #[] p machine (pb.trans body) (pi.trans identity) (pfn.trans callee) ploc tracker tracked mode mask nextTag fresh
    (vp ⟨1,by decide⟩) (vp ⟨12,by decide⟩)
    ((congrArg (fun row=>row.value) same1).trans source1) ((congrArg (fun row=>row.layout) same1).trans cache1)
    (congrArg (fun row=>row.value) slot12) (congrArg (fun row=>row.layout) slot12)
    (by rw [pex];exact noClocks) ghost shallow cachedAddress present race metadata notConstructed
  let result := CopyHelperSteps.advance (ActualLocalCopy.written p 12 SharedReferenceMetadata.sharedLayout
    (vp ⟨12,by decide⟩) (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm) ⟨2,11⟩
  have trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
      (Storage.withCurrent #[] result {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
        memory := RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree true tags capacity offset len)}) :=
    SuccessfulTrace.append pt (.next ref (.refl _))
  have resultAll : CopyHelperCleanup.AllImmediate result :=
    CopyHelperCleanup.all_immediate_written p 12 SharedReferenceMetadata.sharedLayout
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm (vp ⟨12,by decide⟩) pa
  simp only [Array.getElem?_eq_getElem (vp ⟨0,by decide⟩)] at p0
  simp only [Array.getElem?_eq_getElem (vp ⟨1,by decide⟩)] at p1
  simp only [Array.getElem?_eq_getElem (vp ⟨2,by decide⟩)] at p2
  simp only [Array.getElem?_eq_getElem (vp ⟨7,by decide⟩)] at p7
  simp only [Array.getElem?_eq_getElem (vp ⟨8,by decide⟩)] at p8
  simp only [Array.getElem?_eq_getElem (vp ⟨9,by decide⟩)] at p9
  simp only [Array.getElem?_eq_getElem (vp ⟨10,by decide⟩)] at p10
  simp only [Array.getElem?_eq_getElem (vp ⟨11,by decide⟩)] at p11
  simp only [Array.getElem?_eq_getElem (vp ⟨13,by decide⟩)] at p13
  have keepHigh (index : Nat) (high : 13 ≤ index) : result.locals[index]? = frame.locals[index]? := by
    calc
      _ = p.locals[index]? := by simp [result,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,show (12:Nat) ≠ index by omega]
      _ = frame.locals[index]? := pKeep index high
  refine ⟨result,⟨trace,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,resultAll⟩,?_,keepHigh⟩
  all_goals simp only [result,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
    Array.size_set,Array.getElem?_set,Array.getElem_set_self,Array.getElem_set_ne,Array.getElem?_eq_getElem,Option.map_some]
  all_goals try first | exact pTrack | exact pb | exact pi | exact pfn | exact pex | exact prp | exact prc | exact pva | exact pli | exact psz | rfl
  all_goals simp [p0,p1,p2,p7,p8,p9,p10,p11,p13,psz]

theorem executes_tracked
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity base offset len count : UInt64) (nonzero : base+offset≠0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (tree : entry.allocation.extra = RootReferenceTrees.initialTree true tags capacity offset len)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value=.live (.immediate .uninit)) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (live4 : (frame.locals[4]'(by omega)).value=.live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value=.live (.immediate temp5))
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨2,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 2 false)
    (nextTag : tracker.global.nextPointerTag = tags 2)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
        memory := RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree true tags capacity offset len)}) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨2,12⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
      result.locals[13]?=frame.locals[13]? ∧ CopyHelperCleanup.AllImmediate result) ∧ result.trackCallerArg = frame.trackCallerArg := by
  obtain ⟨result,props,tracked,kept⟩ := executes_preserving options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq frame machine tags distinct capacity base offset len count nonzero id entry allocationSize tree positive signedFits bounds temp4 temp5 size source1 cache1 live2 cache2 live3 cache3 live4 live5 unused body identity callee location noClocks all tracker tracked mode mask nextTag fresh cachedAddress present race ghost shallow metadata notConstructed
  exact ⟨result,props,tracked⟩

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity base offset len count : UInt64) (nonzero : base+offset≠0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (tree : entry.allocation.extra = RootReferenceTrees.initialTree true tags capacity offset len)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (tags 1)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value=.live (.immediate .uninit)) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (live4 : (frame.locals[4]'(by omega)).value=.live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value=.live (.immediate temp5))
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨2,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 2 false)
    (nextTag : tracker.global.nextPointerTag = tags 2)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
        memory := RetagEntry.updatedMemory machine.memory id entry (RootReferenceTrees.finalTree true tags capacity offset len)}) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨2,12⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
      result.locals[13]?=frame.locals[13]? ∧ CopyHelperCleanup.AllImmediate result := by
  obtain ⟨result,props,tracked⟩ := executes_tracked options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq frame machine tags distinct capacity base offset len count nonzero id entry allocationSize tree positive signedFits bounds temp4 temp5 size source1 cache1 live2 cache2 live3 cache3 live4 live5 unused body identity callee location noClocks all tracker tracked mode mask nextTag fresh cachedAddress present race ghost shallow metadata notConstructed
  exact ⟨result,props⟩

#print axioms executes
end DuplicatePrefix.PositiveRootSafetyBeforeLen
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PositiveRootSafetyBeforeLen.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual positive-slice len prefix dependency {dependency}"
