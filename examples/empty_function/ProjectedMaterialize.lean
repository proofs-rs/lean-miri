import empty_function.ProjectedCreate
import empty_function.ProjectedForce
import empty_function.ProjectionOffset
namespace EmptyFunction.ProjectedMaterialize
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

/-- The actual projected-uninitialized force-allocation arm, including the
managed address draw, source span callback, caller-slot replacement and wrapping
offset. The relations identify its current state with the original resources. -/
theorem uninit (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : PolicyResourceMargins s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (offset : Size)
    (projected : destination.offset = some offset) (old : destination.oldOperand = .immediate .uninit)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses)
    (tracked : machine.borrowTracker = some input.tracker)
    (backend : machine.user.payload.payload.user.backend = .none) (noRace : machine.dataRace = none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations =
      p.before.machine.user.payload.payload.user.runtime.extras.allocations)
    (choices : machine.user.payload.payload.user.choices = p.before.machine.user.payload.payload.user.choices)
    (slot : LocalState Provenance LocalLayout) (bound : destination.localId < frame.locals.size)
    (atSlot : frame.locals[destination.localId]? = some slot)
    (live : slot.value = .live (.immediate .uninit)) (cache : slot.layout = some destination.baseLayout)
    (normalized : CompilerFrameContext.normalizedLocalType s.prepared.compiler frame destination.localId =
      .ok destination.metadata.normalizedTy) (noClocks : frame.extra.dataRace = none) :
    ∃ (id : AllocId) (tag : BorTag) (base : UInt64) (allocatedMachine movedMachine : MachineHooks.MachineState MiriMemoryKind RootUser),
      PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout (LocalUnit.current frames frame machine) =
        .ok ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩
          (LocalUnit.current frames frame allocatedMachine) ∧
      (∃ (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (global : GlobalState)
          (bytes : Allocation Provenance Unit) (value : Nat) (nextTape : ExecutionChoices.Tape) (finalAddresses : AllocAddresses.GlobalAddressState),
        p.before.machine.memory.reserveAllocId = (reserved,.ok id) ∧
        input.tracker.global.rootPointerTag id = .ok (global,tag) ∧
        Allocation.tryNew (Prov := Provenance) destination.baseLayout.layout.size destination.baseLayout.layout.align.abi .Uninit
          (fun size _ => some (Array.replicate size.bytesNat 0)) = .ok bytes ∧
        allocatedMachine = (ProjectedAddress.assigned
          (ChoiceProjection.tapeAccess.put (ProjectedCreate.registered s (LocalUnit.current frames frame machine)
            reserved input.tracker global id bytes tag destination.baseLayout.layout.size) nextTape) finalAddresses).machine ∧
        ∃ supported : value < 16, finalAddresses = (ProjectedAddress.stackAttempt
          (ProjectedCreate.registered s (LocalUnit.current frames frame machine) reserved input.tracker global id bytes tag destination.baseLayout.layout.size)
          id destination.baseLayout.layout.size destination.baseLayout.layout.align.abi ⟨value,supported⟩).state ∧
          (ProjectedAddress.stackAttempt (ProjectedCreate.registered s (LocalUnit.current frames frame machine) reserved input.tracker global id bytes tag destination.baseLayout.layout.size)
            id destination.baseLayout.layout.size destination.baseLayout.layout.align.abi ⟨value,supported⟩).outcome = .ok (.ready base) ∧
          finalAddresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) ∧
      Nonempty (InputDraft.IndirectFootprint (LocalUnit.current frames frame allocatedMachine)
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes base)) destination.baseLayout.layout.size) ∧
      (∃ span, movedMachine = {allocatedMachine with allocationSpans :=
        (allocatedMachine.allocationSpans.filter (fun row => row.1 != id)).push (id,span,none)}) ∧
      forceAllocation (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler) ()
        ⟨.local frames.size destination.localId (some offset) frame.localsIdentity,s.abi.ret.layout⟩
        (LocalUnit.current frames frame machine) =
        .ok ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset.bytes)),.none,none⟩,s.abi.ret.layout⟩
          (LocalUnit.current frames {frame with locals := frame.locals.set destination.localId {slot with value := .live (.indirect ⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩)} bound}
            movedMachine) := by
  have needed := ProjectedForce.needed s p input.tracker destination offset projected .uninit old
  obtain ⟨reserved,id,global,tag,bytes,base,value,nextTape,finalAddresses,reserveEq,rootEq,sizeEq,alignEq,notNative,mutable,
    created,allocationEq,cached,baseFits,missingLive,addressState⟩ := ProjectedCreate.allocate s metadata capacity p input resources destination needed
      (LocalUnit.current frames frame machine) memory addresses tracked backend noRace extras choices
  obtain ⟨supported,addressPure,addressReady⟩ := addressState
  let post := ProjectedAddress.assigned
    (ChoiceProjection.tapeAccess.put (ProjectedCreate.registered s (LocalUnit.current frames frame machine)
      reserved input.tracker global id bytes tag destination.baseLayout.layout.size) nextTape) finalAddresses
  let allocated : MPlaceTy Provenance :=
    ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,destination.baseLayout⟩
  have allocatedEq : PlaceMachine.allocateStack s.cfg.allocation destination.baseLayout
      (LocalUnit.current frames frame machine) = .ok allocated (LocalUnit.current frames frame post.machine) := allocationEq
  have liveId : post.machine.memory.live.any (fun row => row.1 == id) = true := by
    change (reserved.live.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)⟩)).any (fun row => row.1 == id) = true
    simp [Array.any_push]
  obtain ⟨span,moved⟩ := ProjectedForce.after_move s metadata capacity frames frame post.machine
    destination.localId destination.metadata.normalizedTy normalized allocated id tag rfl liveId noClocks
  let movedMachine : MachineHooks.MachineState MiriMemoryKind RootUser := {post.machine with allocationSpans := (post.machine.allocationSpans.filter (fun row => row.1 != id)).push (id,span,none)}
  have footprint : Nonempty (InputDraft.IndirectFootprint (LocalUnit.current frames frame post.machine) allocated.mplace.ptr
      destination.baseLayout.layout.size) := by
    refine ⟨{id := id,entry := ⟨.stack,bytes.withExtra (BorrowTree.new tag destination.baseLayout.layout.size)⟩, live := ?_,base := base,relative := 0,cached := cached,address := ?_,addressFits := ?_,extent := ?_,attribution := rfl}⟩
    · change (reserved.live.push _).find? _ = _
      simp [Array.find?_push,missingLive]
    · simp [allocated,Pointer.new,Size.ofBytes]
    · change base.toNat + bytes.byteSize.bytes.toNat < 2^64
      rw [sizeEq]
      exact baseFits
    · change 0 + destination.baseLayout.layout.size.bytes.toNat ≤ bytes.byteSize.bytes.toNat
      rw [sizeEq]
      omega
  have dictionaries := MetadataBinding.fields s metadata capacity
  have forced := ProjectedForce.uninit s.cfg.access s.cfg.allocation s.cfg.compiler () frames frame machine
    post.machine movedMachine destination.localId slot destination.baseLayout s.abi.ret.layout bound atSlot live cache
    destination.baseSized (dictionaries.debug.trans profile.debug) allocated allocatedEq moved (some offset) frame.localsIdentity
  refine ⟨id,tag,base,post.machine,movedMachine,allocatedEq,⟨reserved,global,bytes,value,nextTape,finalAddresses,reserveEq,rootEq,created,rfl,⟨supported,addressPure,addressReady,cached⟩⟩,footprint,⟨span,rfl⟩,?_⟩
  rw [forced]
  dsimp only
  have wrapped := ProjectionOffset.wrapping s metadata capacity
    (LocalUnit.current frames {frame with locals := frame.locals.set destination.localId {slot with value := .live (.indirect allocated.mplace)} bound} movedMachine) allocated.mplace offset
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [wrapped]
  rfl
end EmptyFunction.ProjectedMaterialize
