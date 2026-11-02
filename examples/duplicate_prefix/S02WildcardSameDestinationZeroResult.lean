import duplicate_prefix.S02WildcardSameDestinationInit
import duplicate_prefix.S02WildcardPositiveZeroFrameSettings
import duplicate_prefix.S03ZeroCountBodyActiveSame
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.S02WildcardPositiveIdUnique
import duplicate_prefix.S02SeparateDestinationStateJoin
namespace DuplicatePrefix.S02WildcardSameDestinationZeroResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

/-- The actual positive wildcard source and concrete return place execute and
return normally at count zero when their resolved allocation is the same. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
        DuplicatePrefixArgumentCallResult.Result options limits remaining span before
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨reference,output,fresh,argument,ready⟩ :=
    S02WildcardSameDestinationInit.enters address len 0 input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro sameId
  obtain ⟨data,updated,protect,actual,⟨packet⟩⟩ := ready sameId
  let destination := data.destination
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) 0).frame
  let changed := {args with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned data.nextFresh tree updated
  let installed := CallEntryFacts.doneRootFrame
    {TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
  obtain ⟨frame,machine,tracker,borrowFrame,thread,fuel,actual2,body,identity,callee,location,frameSize,
    slot0,slot2,slot3,slot4,slot5,noLocalClocks,frameTracked,returnPlace,continuation,immediateLocals,varargs,
    enabled,defaultMode,active,race,backend,ghost,shallow,unchecked,noGc,fixed,extrasEq,returnExtras,debugOff,validationFuel⟩ :=
    S02WildcardPositiveZeroFrameSettings.ready_from_protect address len input nonempty reference output fresh argument
      destination data.nextFresh tree updated protect
  have same : Storage.withCurrent #[] frame machine = Storage.withCurrent #[] installed after.machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq := S02SeparateDestinationStateJoin.same_frame frame installed machine after.machine same
  have machineEq := S02SeparateDestinationPacketJoin.same_machine frame installed machine after.machine same
  subst frame
  subst machine
  have trackerEq : packet.tracker = tracker := Option.some.inj (packet.enabled.symm.trans enabled)
  have borrowEq : packet.borrowFrame = borrowFrame := Option.some.inj (packet.frameTracked.symm.trans frameTracked)
  have packetMode : packet.tracker.retagMode = .Default := by rw [trackerEq];exact defaultMode
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination returnTag returnConcrete).1
  have extras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩) := by
    rw [physicalId];exact returnExtras
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < packet.destination.offset.toNat ∨ packet.destination.offset.toNat+1 ≤ row.1.bytes.toNat := by simp
  have slot0Row := Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot0)
  have slot2Row := Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot2)
  have slot3Row := Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot3)
  have slot4Row := Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot4)
  have slot5Row := Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot5)
  obtain ⟨done,trace,terminal,empty,noErrors,noUB⟩ := S03ZeroCountBodyActiveSame.complete options limits remaining span
    installed after.machine packet.tracker packet.borrowFrame packetMode packet.enabled packet.frameTracked
    place packet.destination packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
    packet.sourceTag packet.sourceChild packet.sourceSelected packet.sourceMaximum packet.sourceOffset packet.sourceLen
    packet.sourceNode packet.sourceTagged packet.sourcePresent packet.sourceHidden packet.sourceRuntime
    packet.sourcePositive packet.sourceDistinct packet.sourceOrder packet.sourceShort packet.sourceActivity
    packet.owned packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge packet.returnHidden
    packet.hiddenFrame packet.runtime packet.positive packet.distinct packet.order packet.short packet.disjoint
    packet.returnLeaf packet.childrenDifferent packet.activity thread active race backend ghost shallow #[] extras outside
    fuel debugOff validationFuel (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
    body identity callee location frameSize (congrArg LocalState.value slot0Row) (congrArg LocalState.layout slot0Row)
    (congrArg LocalState.value slot3Row) (congrArg LocalState.value slot4Row) (congrArg LocalState.value slot5Row)
    (congrArg LocalState.layout slot4Row) (congrArg LocalState.layout slot5Row)
    (congrArg LocalState.value slot2Row) (congrArg LocalState.layout slot2Row) noLocalClocks returnPlace continuation
    immediateLocals varargs unchecked noGc fixed
  exact ⟨Storage.withCurrent #[] installed after.machine,done,actual,trace,terminal,empty,noErrors,noUB,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

/-- Fix the original source witness explicitly: allocation uniqueness removes
any dependence on the existential choice in `result`. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨resolved,run⟩ := result address len input nonempty returnTag returnConcrete
  have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
  exact run (by rw [←unique];exact same)
end
end DuplicatePrefix.S02WildcardSameDestinationZeroResult
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02WildcardSameDestinationZeroResult.result,
      ``DuplicatePrefix.S02WildcardSameDestinationZeroResult.same_id] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard same zero Result dependency {dependency}"
