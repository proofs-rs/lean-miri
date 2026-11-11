import empty_function.ProjectedAddress
import empty_function.ProjectedPolicyChoiceSupply
import empty_function.ProjectedPolicyAddress
import empty_function.ProjectedImage
namespace EmptyFunction.ProjectedCreate
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def registered (s : Static) (state : State) (reserved : MemoryState Provenance BorrowTree MiriMemoryKind)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) (id : AllocId)
    (bytes : Allocation Provenance Unit) (tag : BorTag) (size : Size) : State :=
  let initialized := MemoryExtras.putAllocation (ProjectedAllocation.extras s)
    {state.machine with memory := reserved,borrowTracker := some {tracker with global}} id {weakMemory := none}
  {state with machine := {initialized with memory :=
    {initialized.memory with live := initialized.memory.live.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag size)⟩)}}}

 theorem allocate (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : PolicyResourceMargins s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (needed : InputDraft.NeedsEnclosingAllocation p)
    (state : State) (memory : state.machine.memory = p.before.machine.memory)
    (addresses : state.machine.user.addresses = p.before.machine.user.addresses)
    (tracked : state.machine.borrowTracker = some input.tracker)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noRace : state.machine.dataRace = none)
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations =
      p.before.machine.user.payload.payload.user.runtime.extras.allocations)
    (choices : state.machine.user.payload.payload.user.choices = p.before.machine.user.payload.payload.user.choices) :
    ∃ (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId) (global : GlobalState)
      (tag : BorTag) (bytes : Allocation Provenance Unit) (base : UInt64) (value : Nat) (nextTape : ExecutionChoices.Tape) (finalAddresses : AllocAddresses.GlobalAddressState),
      p.before.machine.memory.reserveAllocId = (reserved,.ok id) ∧
      input.tracker.global.rootPointerTag id = .ok (global,tag) ∧
      bytes.byteSize = destination.baseLayout.layout.size ∧ bytes.align = destination.baseLayout.layout.align.abi ∧
      bytes.nativeBuffer = none ∧ bytes.mutability = .Mut ∧
      Allocation.tryNew (Prov := Provenance) destination.baseLayout.layout.size destination.baseLayout.layout.align.abi .Uninit
        (fun size _ => some (Array.replicate size.bytesNat 0)) = .ok bytes ∧
      PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout state =
        .ok ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩
          (ProjectedAddress.assigned
            (ChoiceProjection.tapeAccess.put (registered s state reserved input.tracker global id bytes tag destination.baseLayout.layout.size) nextTape)
            finalAddresses) ∧
      finalAddresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧ base.toNat + destination.baseLayout.layout.size.bytes.toNat < 2^64 ∧
      reserved.live.find? (fun row => row.1 == id) = none ∧
      ∃ supported : value < 16, finalAddresses = (ProjectedAddress.stackAttempt
        (registered s state reserved input.tracker global id bytes tag destination.baseLayout.layout.size) id
        destination.baseLayout.layout.size destination.baseLayout.layout.align.abi ⟨value,supported⟩).state ∧
        (ProjectedAddress.stackAttempt (registered s state reserved input.tracker global id bytes tag destination.baseLayout.layout.size)
          id destination.baseLayout.layout.size destination.baseLayout.layout.align.abi ⟨value,supported⟩).outcome = .ok (.ready base) := by
  have alignment := metadata.compilerLayoutAlignment destination.metadata.normalizedTy destination.baseLayout destination.metadata.lookup
  obtain ⟨bytes,created,sizeEq,lengthEq,notNative,mutable,alignEq⟩ :=
    ProjectedImage.create_uninit_full destination.baseLayout.layout.size destination.baseLayout.layout.align.abi alignment
  obtain ⟨reserved,id,reserveEq,idEq,vacantExtras,missing,missingLive⟩ := ProjectedAllocation.reserve_initial s p input resources needed
  have reserveCurrent : state.machine.memory.reserveAllocId = (reserved,.ok id) := by rw [memory]; exact reserveEq
  have missingCurrent : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none := by rw [addresses]; exact missing
  have vacantCurrent : state.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by rw [extras]; exact vacantExtras
  obtain ⟨global,tag,rootEq,initializedEq,rootTag,protectedEq,oldRoots⟩ :=
    ProjectedAllocation.init_extra s metadata capacity {state.machine with memory := reserved} input.tracker tracked
      id destination.baseLayout.layout.size destination.baseLayout.layout.align.abi
      (ProjectedAllocation.tag_room s p input resources) backend noRace vacantCurrent
  let initial := MemoryExtras.putAllocation (ProjectedAllocation.extras s)
    {{state.machine with memory := reserved} with borrowTracker := some {input.tracker with global}} id {weakMemory := none}
  let liveState := registered s state reserved input.tracker global id bytes tag destination.baseLayout.layout.size
  have reserveView := ProjectedAllocation.reserve_registry state.machine.memory
  have sameLive : reserved.live = p.before.machine.memory.live := by
    rw [reserveCurrent] at reserveView
    exact reserveView.1.trans (congrArg (fun memory => memory.live) memory)
  have registeredLive : liveState.machine.memory.live.find? (fun row => row.1 == id) =
      some (id,⟨.stack,bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)⟩) := by
    change (reserved.live.push _).find? _ = _
    simp [Array.find?_push,sameLive,missingLive]
  let info : AllocationInfo := ⟨destination.baseLayout.layout.size,destination.baseLayout.layout.align.abi,.liveData,.Mut⟩
  have infoEq : liveState.machine.memory.getAllocInfo id = .ok info := by
    simp only [MemoryState.getAllocInfo,registeredLive,pure,Pure.pure,Except.pure]
    change Except.ok (⟨bytes.byteSize,bytes.align,.liveData,bytes.mutability⟩ : AllocationInfo) = _
    rw [sizeEq,alignEq,mutable]
  have isLive : liveState.machine.memory.isAllocLive id = true := by
    simp [MemoryState.isAllocLive,liveState,registered,MemoryExtras.putAllocation,ProjectedAllocation.extras,
      EvalCoreMachine.extras,Array.any_push]
  have addrEq : liveState.machine.user.addresses = p.before.machine.user.addresses := addresses
  have tapeEq : ChoiceProjection.tapeAccess.get liveState = p.before.machine.user.payload.payload.user.choices := choices
  have margins := resources.allocation needed
  obtain ⟨generation,representation⟩ := input.projectedGeneration needed
    ⟨margins.available,margins.nonzero,fun active => ⟨margins.sourceAvailable active,margins.sourceNonzero active⟩⟩
  obtain ⟨binding,environment⟩ := resources.choices.projected needed
  have supplied := ProjectedPolicyChoiceSupply.supplied s p binding id reserved reserveEq missing representation.managed generation representation.current environment
  have suppliedCurrent : PolicyChoiceSupply.Environment ChoiceSupply.stackMissPlan (ChoiceProjection.tapeAccess.get liveState) := by rw [tapeEq]; exact supplied
  have sizeBound := resources.localSizes destination.caller destination.localId destination.baseLayout destination.current ⟨destination.metadata⟩
  have alignBound := resources.localAlignments destination.caller destination.localId destination.baseLayout destination.current ⟨destination.metadata⟩
  have one : 1 ≤ resources.budget := by have reserve := resources.reserve; unfold work at reserve; omega
  have room := RawResources.room s p resources generation representation.current destination.baseLayout.layout.size
    destination.baseLayout.layout.align.abi alignment sizeBound alignBound one
  obtain ⟨alignmentBytes,bytesEq,normalized⟩ := alignment
  have frontier := RawResources.frontier p.before generation representation
  have ready := ProjectedPolicyAddress.stack (ConcreteProtection.source s).pointers liveState id info generation
    (by rw [addrEq];exact missing) infoEq rfl isLive (by rw [addrEq];exact representation.managed)
    (by rw [addrEq];exact representation.current)
    (RawGenerator.normalized_exponent _ _ normalized) room
    (resources.addresses generation representation.current).positiveCursor (by rw [addrEq];exact frontier) suppliedCurrent
  obtain ⟨value,supported,nextTape,finalAddresses,tapeStep,addressEq,cached,addressState,addressReady⟩ := ready
  let base := RawGenerator.base generation.generator destination.baseLayout.layout.align.abi ⟨value,supported⟩
  have geometric := RawGenerator.base_bounds generation.generator destination.baseLayout.layout.size
    destination.baseLayout.layout.align.abi (RawGenerator.normalized_exponent _ _ normalized) ⟨value,supported⟩ (room _)
  have roomBound := (room ⟨value,supported⟩).1
  have lengthBound := RawGenerator.length_nat destination.baseLayout.layout.size
  have baseFits : base.toNat + destination.baseLayout.layout.size.bytes.toNat < 2^64 := by
    dsimp only [base]
    omega
  have adjust := ProjectedAllocation.adjust_source s metadata capacity liveState id tag
    (bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)) registeredLive
  change ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape (ConcreteProtection.source s).pointers id (some .stack) liveState = _ at addressEq
  simp only [bind,Bind.bind,EStateM.bind] at adjust
  rw [addressEq] at adjust
  have maximumEq : s.cfg.allocation.maximumObjectSize = Size.ofBytes 9223372036854775807 := by
    rw [ProjectedAllocation.source s metadata capacity]
    exact ProjectedAllocation.maximum s metadata
  have byteBound : bytes.byteSize.bytes ≤ s.cfg.allocation.maximumObjectSize.bytes := by
    rw [sizeEq,maximumEq,UInt64.le_iff_toNat_le]
    have signed := destination.baseSigned
    change destination.baseLayout.layout.size.bytes.toNat ≤ 9223372036854775807
    omega
  have allocatedPrefix := ProjectedAllocation.raw_prefix s metadata capacity state destination.baseLayout.layout.size
    destination.baseLayout.layout.align.abi bytes created byteBound notNative reserved id reserveCurrent
    (BorrowTree.new tag destination.baseLayout.layout.size) initial initializedEq
    {input.tracker with global} tag rfl rootTag
  change PlaceMachine.allocateStackRaw s.cfg.allocation _ _ state = _ at allocatedPrefix
  change s.cfg.allocation.adjustRootAddress id tag liveState = _ at adjust
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] at adjust
  change PlaceMachine.allocateStackRaw s.cfg.allocation _ _ state =
    ((do let pointer ← s.cfg.allocation.adjustRootAddress id tag; pure pointer.withOptionalProvenance) :
      MachineHooks.M MiriMemoryKind RootUser (Pointer (Option Provenance))) liveState at allocatedPrefix
  simp only [bind,Bind.bind,EStateM.bind] at allocatedPrefix
  rw [adjust] at allocatedPrefix
  refine ⟨reserved,id,global,tag,bytes,base,value,nextTape,finalAddresses,reserveEq,rootEq,sizeEq,alignEq,notNative,mutable,created,?_,cached,baseFits,(by simpa only [sameLive] using missingLive),⟨supported,addressState,addressReady⟩⟩
  unfold PlaceMachine.allocateStack
  simp only [destination.baseSized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,allocatedPrefix]
  rfl

end EmptyFunction.ProjectedCreate
