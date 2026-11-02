import duplicate_prefix.PositiveRootMutablePreparation
import duplicate_prefix.S05DiagnosticDefaultExpression
namespace DuplicatePrefix.S05DiagnosticDefaultStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootZeroCompleteState
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Count one/length two takes the actual guard and preparation path, then executes
its TwoPhase mutable Ref. The resulting frame and machine are explicit expressions. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (ctx : ActualReferenceContext.Context options remaining span) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size=25)
    (temp12 : Immediate Provenance)
    (live12 : (frame.locals[12]'(by omega)).value=.live (.immediate temp12))
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live11 : (frame.locals[11]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))))
    (cache11 : (frame.locals[11]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨3,0⟩)
    (all : CopyHelperCleanup.AllImmediate frame) (noClocks : frame.extra.dataRace=none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (base : UInt64) (nonzero : base ≠ 0)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
    (treeEq : entry.allocation.extra = S05DiagnosticDefaultRead.tree)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 12)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticDefaultRead.protections)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (source1 : frame.locals[1]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 8)) (Size.ofBytes base))
      2 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩) :
    let m2 := tick options remaining span (tick options remaining span machine)
    let room : tracker.global.nextPointerTag.value < 18446744073709551615 := by rw [nextEq];decide
    let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 (RootReferenceInfo.layout false)
    let post := {ReferenceBorrowDriver.allocatedMachine m2 tracker room with
      memory := RetagEntry.updatedMemory m2.memory id entry S05DiagnosticDefaultRead.nextTree}
    ∃ prepared : CompilerFrameContext.ActualFrame, ∃ valid16 : 16 < prepared.locals.size,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] (CopyHelperSteps.advance
          (ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) valid16 value.imm) ⟨6,7⟩) post) ∧
      prepared.body = frame.body ∧ prepared.bodyIdentity = frame.bodyIdentity ∧ prepared.functionInstance = frame.functionInstance ∧
      prepared.extra = frame.extra ∧ prepared.returnPlace = frame.returnPlace ∧ prepared.returnContinuation = frame.returnContinuation ∧
      prepared.vaList = frame.vaList ∧ prepared.localsIdentity = frame.localsIdentity ∧ prepared.trackCallerArg = frame.trackCallerArg ∧
      prepared.locals.size = 25 ∧ prepared.location = .mir ⟨6,7⟩ ∧ prepared.locals[1]? = frame.locals[1]? ∧
      prepared.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate prepared := by
  obtain ⟨prepared,pureTrace,pbody,pidentity,pcallee,pextra,preturn,pcontinuation,pva,plocalsId,ptrack,psize,plocation,
    p0,p1,p2,p13,p15,p16,pkeep,pall⟩ := PositiveRootMutablePreparation.executes options limits remaining span source debug fuel fuelEq
    frame machine 2 1 (by decide) size temp12 live12 live13 cache13 live0 cache0 live7 cache7 dead15 cache15 dead16 cache16
    live8 cache8 live9 cache9 live10 cache10 live11 cache11 body identity callee location all noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  let m2 := tick options remaining span (tick options remaining span machine)
  have fields : m2.memory = machine.memory ∧ m2.borrowTracker = machine.borrowTracker ∧ m2.dataRace = machine.dataRace ∧
      m2.user.addresses = machine.user.addresses ∧ m2.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      m2.user.payload.ghost = machine.user.payload.ghost ∧ m2.user.payload.validation = machine.user.payload.validation := by
    unfold m2 tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have v1 : 1 < prepared.locals.size := by rw [psize];decide
  have v16 : 16 < prepared.locals.size := by rw [psize];decide
  have src := Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans (p1.trans source1))
  have dst := Option.some.inj ((Array.getElem?_eq_getElem v16).symm.trans p16)
  have srcLive : prepared.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 8)) (Size.ofBytes (base+0))) 2 ActualReferenceMetadata.reference).imm) := by
    rw [src]
    simp only [UInt64.add_zero]
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by rw [nextEq];decide
  have query := RootReferenceFacts.compute_destination #[] prepared m2 (pbody.trans body) (pidentity.trans identity) (pcallee.trans callee) false
  have expression := S05DiagnosticDefaultExpression.positive_rvalue options limits remaining span ctx debug cmp .Erased dynamicFuel fuel dynamicEq fuelEq
    base 0 2 id entry (by decide) (by simpa using nonzero) (by decide) #[] prepared m2 tracker (fields.2.1.trans tracked) mode room
    (S05DiagnosticFnEntryRead.tag 8) treeEq rfl nextEq protectedEq rfl rfl (by simpa using bounds) 16 rfl v1 v16 srcLive
    (by rw [src]) (by rw [dst]) (by rw [dst]) query (by rw [pextra];exact noClocks)
    (fields.2.2.2.2.2.1.trans ghost) (fields.2.2.2.2.2.2.trans shallow)
    (by rw [fields.2.2.2.1];exact cachedAddress) (by rw [fields.1];exact present) (fields.2.2.1.trans race)
    (by change m2.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2.2.1];exact metadata)
    (by change m2.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2.2.1];exact notConstructed)
  have treeDone : (S05DiagnosticDefaultExpression.child entry.allocation.extra tracker.global.protectedTags
      (S05DiagnosticFnEntryRead.tag 8) tracker.global.nextPointerTag 0 2 .VisitChildrenOfAccessed).tree = S05DiagnosticDefaultRead.nextTree := by
    unfold S05DiagnosticDefaultExpression.child S05DiagnosticDefaultExpression.read
    simp only [treeEq,protectedEq,nextEq]
    change ((S05DiagnosticDefaultRead.tree.performBorrowAccessRange (.concrete (S05DiagnosticFnEntryRead.tag 8)) Size.ZERO
      (Size.ofBytes 2) .Read S05DiagnosticDefaultRead.protections .VisitChildrenOfAccessed).tree.newChild Size.ZERO
        (.concrete (S05DiagnosticFnEntryRead.tag 8)) (S05DiagnosticFnEntryRead.tag 12)
        (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree = _
    rw [S05DiagnosticDefaultRead.read.2]
    exact S05DiagnosticDefaultRead.constructor_tree
  let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 (RootReferenceInfo.layout false)
  let post := {ReferenceBorrowDriver.allocatedMachine m2 tracker room with memory := RetagEntry.updatedMemory m2.memory id entry S05DiagnosticDefaultRead.nextTree}
  let written := ActualLocalCopy.written prepared 16 (RootReferenceInfo.layout false) v16 value.imm
  have effect : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (config options (remaining+1) span) limits) ()
      (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) ⟨16,#[]⟩ (Storage.withCurrent #[] prepared m2) =
      .ok () (Storage.withCurrent #[] written post) := by
    simpa only [treeDone,UInt64.add_zero,written,value,post] using expression
  have step := CopyHelperSteps.assign_of_actual_rvalue (config options (remaining+1) span) limits #[] prepared written m2 post
    ⟨6,7⟩ ⟨16,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind false) ⟨1,#[.Deref]⟩) plocation
    (by simpa only [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using plocation)
    (by rw [pbody,body];exact RootReferenceFacts.statement false) effect
  exact ⟨prepared,v16,SuccessfulTrace.append pureTrace (.next step (.refl _)),pbody,pidentity,pcallee,pextra,preturn,pcontinuation,pva,plocalsId,ptrack,psize,plocation,p1,p15,pall⟩

#print axioms executes
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticDefaultStep." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic default step dependency {dependency}"
end
end DuplicatePrefix.S05DiagnosticDefaultStep
