import duplicate_prefix.CurrentCallOrdinaryConversionSelected
import duplicate_prefix.CurrentCallConversionFiniteFold
import duplicate_prefix.CurrentCallConversionMaterialize
import duplicate_prefix.CurrentCallConversionResourcesFrame
namespace DuplicatePrefix.CurrentCallOrdinaryConversionInitial
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem root_budget {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    input.tracker.global.nextPointerTag.value.toNat+
      ((CurrentCallConversionPlan.selectedIds before argument length place).filter
        (fun id=>(input.tracker.global.rootTag? id).isNone)).length+16<2^64 := by
  have bound:=CurrentCallOrdinaryConversionSelected.root_misses_le input
  have room:=input.conversionBudget.rootTags
  omega

theorem resources {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    CurrentCallConversionFiniteFold.Resources before.memory before.user.addresses
      (CurrentCallConversionPlan.selectedIds before argument length place) (addressCharge before) := by
  have bound:=CurrentCallOrdinaryConversionSelected.address_misses_le input
  rcases input.conversionBudget.addresses with cached | ⟨generation,sizes,initial,_,_,_,_,limit,ending⟩
  · apply CurrentCallConversionFiniteFold.resources_cached
    intro id member
    cases old : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id) with
    | some entry=>exact ⟨entry,rfl⟩
    | none=>
      have hit : id∈(CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone) :=
        List.mem_filter.mpr ⟨member,by rw [old];rfl⟩
      have positive:=List.length_pos_of_mem hit
      omega
  · apply CurrentCallConversionFiniteFold.resources_of_initial _ _ _ _ generation sizes initial
    · intro needed
      obtain ⟨id,member,uncached,info,metadata,nonTypeId⟩:=needed
      exact input.conversionReady.aligned id info initial.managed member uncached metadata nonTypeId generation initial.generationEq
    · have weighted:=Nat.mul_le_mul_right (addressCharge before) bound
      change generation.generator.nextBaseAddr.toNat+
        ((CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone)).length*addressCharge before<2^64
      omega
    · have weighted:=Nat.mul_le_mul_right (addressCharge before) bound
      change generation.generator.nextBaseAddr.toNat+
        ((CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone)).length*addressCharge before≤generation.generator.endAddr.toNat
      omega

/-- The actual selected protocol and its numeric resources all follow from the initial domain. -/
theorem prepared {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    ∃finalAddresses finalTape,
      CurrentCallConversionChoiceProtocol.AddressProtocol before.memory
        (UInt32.ofNat before.threads.activeThread.toNat) before.user.addresses
        (Miri.Input.EvalPointerSource.tape.get before)
        (CurrentCallConversionPlan.selectedIds before argument length place) finalAddresses finalTape ∧
      CurrentCallConversionFiniteFold.Resources before.memory before.user.addresses
        (CurrentCallConversionPlan.selectedIds before argument length place) (addressCharge before) ∧
      input.tracker.global.nextPointerTag.value.toNat+
        ((CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(input.tracker.global.rootTag? id).isNone)).length+16<2^64 ∧
      (∀id∈CurrentCallConversionPlan.selectedIds before argument length place,
        RelocationTargetMetadata before id) := by
  obtain ⟨finalAddresses,finalTape,protocol⟩:=input.conversionReady.protocol
  exact ⟨finalAddresses,finalTape,protocol,resources input,root_budget input,
    CurrentCallOrdinaryConversionSelected.targets_metadata input⟩


/-- Allocating the saved source tag consumes one unit of the initial reserve.
The actual registered state may change control and the protector table. -/
theorem registered {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (phase : Before) (tracker : MachineHooks.BorrowState)
    (memory : phase.memory=before.memory) (addresses : phase.user.addresses=before.user.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get phase=Miri.Input.EvalPointerSource.tape.get before)
    (thread : phase.threads.activeThread=before.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=input.tracker.global.rootTag? id)
    (counter : tracker.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+1) :
    ∃finalAddresses finalTape,
      CurrentCallConversionChoiceProtocol.AddressProtocol phase.memory
        (UInt32.ofNat phase.threads.activeThread.toNat) phase.user.addresses
        (Miri.Input.EvalPointerSource.tape.get phase)
        (CurrentCallConversionPlan.selectedIds before argument length place) finalAddresses finalTape ∧
      CurrentCallConversionFiniteFold.Resources phase.memory phase.user.addresses
        (CurrentCallConversionPlan.selectedIds before argument length place) (addressCharge before) ∧
      tracker.global.nextPointerTag.value.toNat+
        ((CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(tracker.global.rootTag? id).isNone)).length+15<2^64 ∧
      (∀id∈CurrentCallConversionPlan.selectedIds before argument length place,
        RelocationTargetMetadata phase id) := by
  obtain ⟨finalAddresses,finalTape,protocol,resources,rootBudget,metadata⟩:=prepared input
  refine ⟨finalAddresses,finalTape,?_,?_,?_,?_⟩
  · simpa only [memory,addresses,tape,thread] using protocol
  · simpa only [memory,addresses] using resources
  · have predicates : (fun id=>(tracker.global.rootTag? id).isNone)=(fun id=>(input.tracker.global.rootTag? id).isNone) := by
      funext id
      rw [roots]
    rw [predicates]
    omega
  · intro id member
    have old:=metadata id member
    simpa only [RelocationTargetMetadata,memory,addresses] using old


/-- Actual target formation at the registered phase uses the same declared charge. -/
theorem formation {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (phase : Before) (memory : phase.memory=before.memory)
    (addresses : phase.user.addresses=before.user.addresses)
    (id : AllocId) (member : id∈CurrentCallConversionPlan.selectedIds before argument length place)
    (missing : phase.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (info : AllocationInfo) (actual : phase.memory.getAllocInfo id=.ok info) :
    info.kind≠.dead ∧info.align.pow2≤29 ∧
      15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
        (GlobalAddressBumpRangeFormation.length info.size).toNat≤addressCharge before := by
  have metadata : RelocationTargetMetadata phase id := by
    have old:=CurrentCallOrdinaryConversionSelected.targets_metadata input id member
    simpa only [RelocationTargetMetadata,memory,addresses] using old
  have result:=CurrentCallConversionFiniteFold.formation_initial phase id metadata missing info actual
  simpa only [addressCharge,maximumMetadataAlignment,maximumMetadataSize,memory] using result


/-- Execute the actual first selected conversion from initial domain resources.
The head equation is an internal classifier identity, not an operation result. -/
theorem convert_first {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (phase : Before) (tracker : MachineHooks.BorrowState)
    (memory : phase.memory=before.memory) (addresses : phase.user.addresses=before.user.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get phase=Miri.Input.EvalPointerSource.tape.get before)
    (thread : phase.threads.activeThread=before.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=input.tracker.global.rootTag? id)
    (counter : tracker.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+1)
    (enabled : phase.borrowTracker=some tracker)
    (source : Allocation CtfeProvenance Unit) (rest : List (Allocation CtfeProvenance Unit))
    (head : CurrentCallConversionPlan.selectedPayloads before argument length place=source::rest)
    (layout : TargetDataLayout)
    (hooks : MachineAddress.Hooks MiriMemoryKind CurrentCallConversionFiniteFold.Control)
    (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (race : phase.dataRace=none) (layoutWidth : layout.pointerWidth=.w64) :
    ∃finalAddresses finalTape,Nonempty (CurrentCallConversionFiniteFold.Result source layout hooks externStatic
      phase tracker (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) 15 finalAddresses finalTape) := by
  have ids : CurrentCallConversionPlan.selectedIds before argument length place=
      CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets := by
    simp only [CurrentCallConversionPlan.selectedIds,head,List.flatMap_cons]
    congr 1
    · exact (CurrentCallConversionFiniteFold.targets_eq source).symm
    · apply congrArg (fun f=>rest.flatMap f)
      funext item
      exact (CurrentCallConversionFiniteFold.targets_eq item).symm
  obtain ⟨finalAddresses,finalTape,protocol,resources,rootBudget,metadata⟩:=
    registered input phase tracker memory addresses tape thread roots counter
  rw [ids] at protocol resources rootBudget metadata
  have member : source∈CurrentCallConversionPlan.selectedPayloads before argument length place := by rw [head];simp
  obtain ⟨id,data,_⟩:=CurrentCallOrdinaryConversionSelected.payload_data input source member
  refine ⟨finalAddresses,finalTape,CurrentCallConversionFiniteFold.invoke source layout hooks width externStatic phase tracker enabled
    _ (addressCharge before) 15 (by decide) finalAddresses finalTape protocol resources rootBudget
    (fun target found=>metadata target (List.mem_append_left _ found)) ?_ race data.2.1 data.2.2.1 layoutWidth⟩
  intro target found missing info actual
  apply formation input phase memory addresses target _ missing info actual
  rw [ids]
  exact List.mem_append_left _ found


/-- One shared first-conversion phase after any bounded number of actual
registrations. Heap changes are admitted through their real info-query frame. -/
theorem phase {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (current : Before) (tracker : MachineHooks.BorrowState)
    (infoEq : ∀id,current.memory.getAllocInfo id=before.memory.getAllocInfo id)
    (addresses : current.user.addresses=before.user.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get current=Miri.Input.EvalPointerSource.tape.get before)
    (thread : current.threads.activeThread=before.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=input.tracker.global.rootTag? id)
    (spent reserve : Nat) (room : spent+reserve≤16)
    (counter : tracker.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+spent)
    (metadata : ∀id∈CurrentCallConversionPlan.selectedIds before argument length place,
      RelocationTargetMetadata current id) :
    ∃finalAddresses finalTape,
      CurrentCallConversionChoiceProtocol.AddressProtocol current.memory
        (UInt32.ofNat current.threads.activeThread.toNat) current.user.addresses
        (Miri.Input.EvalPointerSource.tape.get current)
        (CurrentCallConversionPlan.selectedIds before argument length place) finalAddresses finalTape ∧
      CurrentCallConversionFiniteFold.Resources current.memory current.user.addresses
        (CurrentCallConversionPlan.selectedIds before argument length place) (addressCharge before) ∧
      tracker.global.nextPointerTag.value.toNat+
        ((CurrentCallConversionPlan.selectedIds before argument length place).filter
          (fun id=>(tracker.global.rootTag? id).isNone)).length+reserve<2^64 ∧
      (∀id∈CurrentCallConversionPlan.selectedIds before argument length place,
        RelocationTargetMetadata current id) := by
  obtain ⟨finalAddresses,finalTape,protocol,resources,rootBudget,_⟩:=prepared input
  have nextProtocol:=CurrentCallConversionMaterialize.protocol_memory infoEq
    (UInt32.ofNat before.threads.activeThread.toNat) protocol
  have nextResources:=CurrentCallConversionResourcesFrame.memory before.memory current.memory before.user.addresses
    _ (addressCharge before) infoEq resources
  refine ⟨finalAddresses,finalTape,?_,?_,?_,metadata⟩
  · simpa only [addresses,tape,thread] using nextProtocol
  · simpa only [addresses] using nextResources
  · have predicates : (fun id=>(tracker.global.rootTag? id).isNone)=(fun id=>(input.tracker.global.rootTag? id).isNone) := by
      funext id
      rw [roots]
    rw [predicates]
    omega

theorem convert_first_phase {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (current : Before) (tracker : MachineHooks.BorrowState)
    (infoEq : ∀id,current.memory.getAllocInfo id=before.memory.getAllocInfo id)
    (addresses : current.user.addresses=before.user.addresses)
    (tape : Miri.Input.EvalPointerSource.tape.get current=Miri.Input.EvalPointerSource.tape.get before)
    (thread : current.threads.activeThread=before.threads.activeThread)
    (roots : ∀id,tracker.global.rootTag? id=input.tracker.global.rootTag? id)
    (spent reserve : Nat) (room : spent+reserve≤16) (positive : 0<reserve)
    (counter : tracker.global.nextPointerTag.value.toNat≤input.tracker.global.nextPointerTag.value.toNat+spent)
    (enabled : current.borrowTracker=some tracker)
    (metadata : ∀id∈CurrentCallConversionPlan.selectedIds before argument length place,RelocationTargetMetadata current id)
    (source : Allocation CtfeProvenance Unit) (rest : List (Allocation CtfeProvenance Unit))
    (head : CurrentCallConversionPlan.selectedPayloads before argument length place=source::rest)
    (layout : TargetDataLayout)
    (hooks : MachineAddress.Hooks MiriMemoryKind CurrentCallConversionFiniteFold.Control)
    (width : hooks.arithmetic=⟨Size.ofBytes 8⟩)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (race : current.dataRace=none) (layoutWidth : layout.pointerWidth=.w64) :
    ∃finalAddresses finalTape,Nonempty (CurrentCallConversionFiniteFold.Result source layout hooks externStatic
      current tracker (rest.flatMap CurrentCallConversionFiniteFold.targets) (addressCharge before) reserve finalAddresses finalTape) := by
  have ids : CurrentCallConversionPlan.selectedIds before argument length place=
      CurrentCallConversionFiniteFold.targets source++rest.flatMap CurrentCallConversionFiniteFold.targets := by
    simp only [CurrentCallConversionPlan.selectedIds,head,List.flatMap_cons]
    congr 1
    · exact (CurrentCallConversionFiniteFold.targets_eq source).symm
    · apply congrArg (fun f=>rest.flatMap f)
      funext item
      exact (CurrentCallConversionFiniteFold.targets_eq item).symm
  obtain ⟨finalAddresses,finalTape,protocol,resources,rootBudget,_⟩:=
    phase input current tracker infoEq addresses tape thread roots spent reserve room counter metadata
  rw [ids] at protocol resources rootBudget
  have member : source∈CurrentCallConversionPlan.selectedPayloads before argument length place := by rw [head];simp
  obtain ⟨id,data,_⟩:=CurrentCallOrdinaryConversionSelected.payload_data input source member
  refine ⟨finalAddresses,finalTape,CurrentCallConversionFiniteFold.invoke source layout hooks width externStatic current tracker enabled
    _ (addressCharge before) reserve positive finalAddresses finalTape protocol resources rootBudget
    (fun target found=>metadata target (by rw [ids];exact List.mem_append_left _ found)) ?_ race data.2.1 data.2.2.1 layoutWidth⟩
  intro target found missing info actual
  have selected : target∈CurrentCallConversionPlan.selectedIds before argument length place := by rw [ids];exact List.mem_append_left _ found
  have oldMissing : before.user.addresses.baseAddr.find? (fun row=>row.allocId==target)=none := by rw [←addresses];exact missing
  have oldActual : before.memory.getAllocInfo target=.ok info := (infoEq target).symm.trans actual
  exact CurrentCallConversionFiniteFold.formation_initial before target
    (CurrentCallOrdinaryConversionSelected.targets_metadata input target selected) oldMissing info oldActual

end
end DuplicatePrefix.CurrentCallOrdinaryConversionInitial

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryConversionInitial.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial-conversion dependency {name}: {dependency}"
