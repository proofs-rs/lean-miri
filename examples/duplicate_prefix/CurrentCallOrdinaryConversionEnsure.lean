import duplicate_prefix.CurrentCallOrdinaryConversionInitial
import duplicate_prefix.CurrentCallConversionActualEnsure
namespace DuplicatePrefix.CurrentCallOrdinaryConversionEnsure
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem root_wiring (options : EvalConfigurationCore.Options) :
    ∃externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance),
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape
          (CurrentCallConversionActualEnsure.hooks options).address externStatic := by
  exact ⟨_,rfl⟩

private theorem width (options : EvalConfigurationCore.Options) :
    (CurrentCallConversionActualEnsure.hooks options).address.arithmetic=⟨Size.ofBytes 8⟩ := by rfl

private theorem layout_width : PreparedReflection.actual.compiler.runtime.target.base.pointerWidth=.w64 := by rfl

/-- The real original ensure runs the finite converter internally. Every
argument here is an actual current-phase frame or initial selected datum. -/
theorem first {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (current : RootState) (tracker : MachineHooks.BorrowState)
    (infoEq : ∀id,current.machine.memory.getAllocInfo id=before.memory.getAllocInfo id)
    (addresses : current.machine.user.addresses=before.user.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get current.machine=Miri.Input.EvalPointerSource.tape.get before)
    (thread : current.machine.threads.activeThread=before.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=input.tracker.global.rootTag? id)
    (spent reserve : Nat) (room : spent+reserve≤16) (positive : 0<reserve)
    (counter : tracker.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+spent)
    (enabled : current.machine.borrowTracker=some tracker)
    (metadata : ∀id∈CurrentCallConversionPlan.selectedIds before argument length place,RelocationTargetMetadata current.machine id)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (rest : List (Allocation CtfeProvenance Unit))
    (head : CurrentCallConversionPlan.selectedPayloads before argument length place=source::rest)
    (selected : CurrentPayload current.machine id source)
    (absent : current.machine.memory.live.find? (fun row=>row.1==id)=none)
    (cached : tracker.global.rootTag? id=some root)
    (registry : current.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id)=false)
    (race : current.machine.dataRace=none) :
    ∃externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance),
      (CurrentCallConversionActualEnsure.hooks options).rootPointer=
        PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape
          (CurrentCallConversionActualEnsure.hooks options).address externStatic ∧
    ∃finalAddresses finalTape,
    ∃result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic current.machine tracker
      (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) reserve finalAddresses finalTape,
      (PreparedContracts.actualConfig options () remaining span).retag.ensureTreeExtra id current=
        .ok () {current with machine:=(CurrentCallConversionMaterialize.installed
          (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩)
          id .global (result.converted.mapExtra (fun _=>BorrowTree.new root result.converted.byteSize)))} := by
  obtain ⟨externStatic,wiring⟩:=root_wiring options
  obtain ⟨finalAddresses,finalTape,⟨result⟩⟩:=CurrentCallOrdinaryConversionInitial.convert_first_phase input current.machine tracker
    infoEq addresses tape thread roots spent reserve room positive counter enabled metadata source rest head
    PreparedReflection.actual.compiler.runtime.target.base (CurrentCallConversionActualEnsure.hooks options).address
    (width options) externStatic race layout_width
  have conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state=>.ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer current.machine=.ok result.converted result.machine := by
    rw [wiring]
    exact result.completed
  have tracked : result.machine.borrowTracker=some {tracker with global:=result.global} := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  have afterRace : result.machine.dataRace=none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact race
  have afterRegistry : result.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id)=false := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    exact registry
  have ensure:=CurrentCallConversionActualEnsure.ensure options remaining span current result.machine
    {tracker with global:=result.global} id root source result.converted selected absent conversion tracked
    (result.roots id root cached) afterRace afterRegistry
  exact ⟨externStatic,wiring,finalAddresses,finalTape,result,ensure⟩


/-- Continue with the actual remaining protocol after source materialization.
New target roots and addresses from the first conversion are retained. -/
theorem next {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (initial : Before) (oldTracker : MachineHooks.BorrowState)
    (firstSource source : Allocation CtfeProvenance Unit) (rest : List (Allocation CtfeProvenance Unit))
    (head : CurrentCallConversionPlan.selectedPayloads before argument length place=firstSource::source::rest)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer Miri.Input.EvalPointerSource.tape
        (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (oldReserve : Nat) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (previous : CurrentCallConversionFiniteFold.Result firstSource PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic initial oldTracker
      (CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets)
      (addressCharge before) oldReserve finalAddresses finalTape)
    (current : RootState) (tracker : MachineHooks.BorrowState)
    (initialInfo : ∀id,initial.memory.getAllocInfo id=before.memory.getAllocInfo id)
    (infoEq : ∀id,current.machine.memory.getAllocInfo id=initial.memory.getAllocInfo id)
    (addresses : current.machine.user.addresses=previous.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get current.machine=previous.tape)
    (thread : current.machine.threads.activeThread=initial.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=previous.global.rootTag? id)
    (spent reserve : Nat) (room : spent+reserve≤oldReserve) (positive : 0<reserve)
    (counter : tracker.global.nextPointerTag.value.toNat≤previous.global.nextPointerTag.value.toNat+spent)
    (enabled : current.machine.borrowTracker=some tracker)
    (bases : ∀id base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base→
      current.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base)
    (metadata : ∀id∈CurrentCallConversionFiniteFold.targets source,RelocationTargetMetadata current.machine id)
    (id : AllocId) (root : BorTag) (selected : CurrentPayload current.machine id source)
    (absent : current.machine.memory.live.find? (fun row=>row.1==id)=none)
    (cached : tracker.global.rootTag? id=some root)
    (registry : current.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id)=false)
    (race : current.machine.dataRace=none) :
    ∃result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic current.machine tracker
      (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) reserve finalAddresses finalTape,
      (PreparedContracts.actualConfig options () remaining span).retag.ensureTreeExtra id current=
        .ok () {current with machine:=(CurrentCallConversionMaterialize.installed
          (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) result.machine id ⟨none,#[]⟩)
          id .global (result.converted.mapExtra (fun _=>BorrowTree.new root result.converted.byteSize)))} := by
  have protocol:=CurrentCallConversionMaterialize.protocol_memory infoEq
    (UInt32.ofNat initial.threads.activeThread.toNat) previous.protocol
  have resources:=CurrentCallConversionResourcesFrame.memory initial.memory current.machine.memory previous.addresses
    _ (addressCharge before) infoEq previous.resources
  have protocolNext : CurrentCallConversionChoiceProtocol.AddressProtocol current.machine.memory
      (UInt32.ofNat current.machine.threads.activeThread.toNat) current.machine.user.addresses
      (Miri.Input.EvalPointerSource.tape.get current.machine)
      (CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets) finalAddresses finalTape := by
    simpa only [addresses,tape,thread] using protocol
  have resourcesNext : CurrentCallConversionFiniteFold.Resources current.machine.memory current.machine.user.addresses
      (CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) := by
    simpa only [addresses] using resources
  have rootBudget : tracker.global.nextPointerTag.value.toNat+
      ((CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets).filter
        (fun id=>(tracker.global.rootTag? id).isNone)).length+reserve<2^64 := by
    have predicates : (fun id=>(tracker.global.rootTag? id).isNone)=(fun id=>(previous.global.rootTag? id).isNone) := by
      funext id
      rw [roots]
    rw [predicates]
    have old:=previous.rootBudget
    omega
  have member : source∈CurrentCallConversionPlan.selectedPayloads before argument length place := by rw [head];simp
  obtain ⟨_,data,_⟩:=CurrentCallOrdinaryConversionSelected.payload_data input source member
  have formation : ∀target∈CurrentCallConversionFiniteFold.targets source,
      current.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==target)=none→
      ∀info,current.machine.memory.getAllocInfo target=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
          (GlobalAddressBumpRangeFormation.length info.size).toNat≤addressCharge before := by
    intro target found missing info actual
    have selectedTarget : target∈CurrentCallConversionPlan.selectedIds before argument length place := by
      unfold CurrentCallConversionPlan.selectedIds
      rw [head]
      simp only [List.flatMap_cons]
      apply List.mem_append_right
      apply List.mem_append_left
      simpa only [CurrentCallConversionFiniteFold.targets_eq] using found
    have originalMissing : before.user.addresses.baseAddr.find? (fun row=>row.allocId==target)=none := by
      cases old : before.user.addresses.baseAddr.find? (fun row=>row.allocId==target) with
      | none=>rfl
      | some base=>rw [bases target base old] at missing;cases missing
    have originalActual : before.memory.getAllocInfo target=.ok info :=
      (initialInfo target).symm.trans ((infoEq target).symm.trans actual)
    exact CurrentCallConversionFiniteFold.formation_initial before target
      (CurrentCallOrdinaryConversionSelected.targets_metadata input target selectedTarget) originalMissing info originalActual
  obtain ⟨result⟩:=CurrentCallConversionFiniteFold.invoke source PreparedReflection.actual.compiler.runtime.target.base
    (CurrentCallConversionActualEnsure.hooks options).address (width options) externStatic current.machine tracker enabled
    _ (addressCharge before) reserve positive finalAddresses finalTape protocolNext resourcesNext rootBudget
    metadata formation race data.2.1 data.2.2.1 layout_width
  have conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state=>.ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer current.machine=.ok result.converted result.machine := by
    rw [wiring]
    exact result.completed
  have tracked : result.machine.borrowTracker=some {tracker with global:=result.global} := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  have afterRace : result.machine.dataRace=none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact race
  have afterRegistry : result.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id)=false := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    exact registry
  have ensure:=CurrentCallConversionActualEnsure.ensure options remaining span current result.machine
    {tracker with global:=result.global} id root source result.converted selected absent conversion tracked
    (result.roots id root cached) afterRace afterRegistry
  exact ⟨result,ensure⟩

end
end DuplicatePrefix.CurrentCallOrdinaryConversionEnsure

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryConversionEnsure.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual ensure orchestration {name}: {dependency}"
