import duplicate_prefix.S02SameDestinationZeroCore
import duplicate_prefix.S02SameDestinationZeroExtras
import duplicate_prefix.S02SameZeroFrameSettings
import duplicate_prefix.S02SeparateDestinationStateJoin
import duplicate_prefix.S03ZeroCountBodyActiveSame

namespace DuplicatePrefix.S02SameDestinationZeroBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original call reaches normal return without UB for count zero in the
positive concrete, same-allocation concrete return-place case. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg limits installed done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn safety 1 installed ∧
      CallSafety.NoUBBeforeReturn safety 1 installed := by
  obtain ⟨frame,machine,actual,⟨packet⟩⟩ :=
    S02SameDestinationZeroCore.enters id tag address len 0 input nonempty sameAllocation
      returnTag returnConcrete
  obtain ⟨frame2,machine2,tracker2,borrowFrame2,thread,fuel,actual2,body,identity,callee,
    location,frameSize,slot0,slot2,slot3,slot4,slot5,noLocalClocks,frameTracked,
    returnPlace,continuation,immediateLocals,varargs,enabled2,defaultMode,active,race,
    backend,ghost,shallow,unchecked,noGc,fixed,debugOff,validationFuel⟩ :=
    S02SameZeroFrameSettings.ready id tag address len input nonempty sameAllocation returnTag returnConcrete
  obtain ⟨frame3,machine3,actual3,extras3⟩ :=
    S02SameDestinationZeroExtras.ready id tag address len 0 input nonempty sameAllocation
      returnTag returnConcrete
  have same2 : Storage.withCurrent #[] frame machine = Storage.withCurrent #[] frame2 machine2 :=
    (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
  have same3 : Storage.withCurrent #[] frame machine = Storage.withCurrent #[] frame3 machine3 :=
    (EStateM.Result.ok.inj (actual.symm.trans actual3)).2
  have frameEq : frame = frame2 := S02SeparateDestinationStateJoin.same_frame frame frame2 machine machine2 same2
  have machineEq : machine = machine2 := S02SeparateDestinationPacketJoin.same_machine frame frame2 machine machine2 same2
  have machineEq3 : machine = machine3 := S02SeparateDestinationPacketJoin.same_machine frame frame3 machine machine3 same3
  subst frame2
  subst machine2
  have trackerEq : packet.tracker = tracker2 := Option.some.inj (packet.enabled.symm.trans enabled2)
  have borrowEq : packet.borrowFrame = borrowFrame2 := Option.some.inj (packet.frameTracked.symm.trans frameTracked)
  have packetMode : packet.tracker.retagMode = .Default := by rw [trackerEq]; exact defaultMode
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  have extras : machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩) := by
    rw [physicalId,machineEq3]
    exact extras3
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < packet.destination.offset.toNat ∨
        packet.destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  have slot0Row : frame.locals[0]'(by rw [frameSize];decide) =
      ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot0)
  have slot2Row : frame.locals[2]'(by rw [frameSize];decide) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot2)
  have slot3Row : frame.locals[3]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot3)
  have slot4Row : frame.locals[4]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot4)
  have slot5Row : frame.locals[5]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot5)
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨done,trace,terminal,empty,noErrors,noUB⟩ :=
    S03ZeroCountBodyActiveSame.complete options limits remaining span
      frame machine packet.tracker packet.borrowFrame packetMode packet.enabled packet.frameTracked
      place packet.destination packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
      packet.sourceTag
      packet.sourceChild packet.sourceSelected packet.sourceMaximum packet.sourceOffset packet.sourceLen
      packet.sourceNode packet.sourceTagged packet.sourcePresent packet.sourceHidden packet.sourceRuntime
      packet.sourcePositive packet.sourceDistinct packet.sourceOrder packet.sourceShort packet.sourceActivity
      packet.owned packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge
      packet.returnHidden packet.hiddenFrame packet.runtime packet.positive packet.distinct packet.order
      packet.short packet.disjoint packet.returnLeaf packet.childrenDifferent packet.activity thread active
      race backend ghost shallow
      #[] extras outside fuel debugOff validationFuel source
      body identity callee location
      frameSize (congrArg LocalState.value slot0Row)
      (congrArg LocalState.layout slot0Row) (congrArg LocalState.value slot3Row)
      (congrArg LocalState.value slot4Row) (congrArg LocalState.value slot5Row)
      (congrArg LocalState.layout slot4Row) (congrArg LocalState.layout slot5Row)
      (congrArg LocalState.value slot2Row) (congrArg LocalState.layout slot2Row)
      noLocalClocks returnPlace continuation immediateLocals varargs
      unchecked noGc fixed
  exact ⟨Storage.withCurrent #[] frame machine,done,actual,trace,terminal,empty,noErrors,noUB⟩

end
end DuplicatePrefix.S02SameDestinationZeroBody

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationZeroBody.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination zero-body dependency {dependency}"
