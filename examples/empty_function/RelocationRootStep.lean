import empty_function.RelocationCallbackPost
namespace EmptyFunction.RelocationRootStep
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
abbrev S := ChoiceExecution.S

def CachedOrTypeId (before : WholeCall.State) (id : AllocId) : Prop :=
  (∃ base,before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) ∨
    ∃ info,before.machine.memory.getAllocInfo id = .ok info ∧ info.kind = .typeId ∧ before.machine.memory.isAllocLive id = true

theorem normal (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World before.machine tracker)
    (tables : InputDraft.AddressTables before) (needed : Prop)
    (generation : needed → ∃ current,InputDraft.GenerationRepresentation before current)
    (provenance : CtfeProvenance) (offset : UInt64) (target : AllocationInfo)
    (admission : RawRootAdmission.Normal before.machine.memory provenance.allocId)
    (backing : InputDraft.MetadataBacking before provenance.allocId)
    (metadata : before.machine.memory.getAllocInfo provenance.allocId = .ok target)
    (live : before.machine.memory.isAllocLive provenance.allocId = true) (notDead : target.kind ≠ .dead)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (noDraw : ¬needed → CachedOrTypeId before provenance.allocId)
    (noRace : before.machine.dataRace = none) (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ pointer final,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .ok pointer final ∧
      Nonempty (RelocationCallbackPost.Post before tracker needed final)) ∨
    (∃ error failed,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new provenance (Size.ofBytes offset)) before.machine = .error error failed ∧ RunLoop.reportsUB error = false) := by
  classical
  by_cases need : needed
  · obtain ⟨current,rep⟩ := generation need
    rcases RootAddressOutcome.normal before hooks externStatic tracker world current rep provenance offset target admission backing
      metadata live notDead alignment noRace width classifier with success | stopped
    · obtain ⟨pointer,final,actual,⟨post⟩⟩ := success
      exact .inl ⟨pointer,final,actual,⟨RelocationCallbackPost.generated post⟩⟩
    · exact .inr stopped
  · rcases NoDrawBasicRootTotal.normal before hooks externStatic tracker world tables provenance offset admission width (noDraw need) with success | stopped
    · obtain ⟨pointer,final,actual,⟨post⟩⟩ := success
      exact .inl ⟨pointer,final,actual,⟨RelocationCallbackPost.cached tables need post⟩⟩
    · exact .inr stopped

theorem static_root (before : WholeCall.State) (hooks : ChoiceExecution.H)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World before.machine tracker)
    (tables : InputDraft.AddressTables before) (needed : Prop)
    (generation : needed → ∃ current,InputDraft.GenerationRepresentation before current)
    (id : AllocId) (target : AllocationInfo)
    (backing : InputDraft.MetadataBacking before id) (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (noDraw : ¬needed → CachedOrTypeId before id) (noRace : before.machine.dataRace = none)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ pointer final,ForeignResolverPrelude.root hooks id before.machine = .ok pointer final ∧
      Nonempty (RelocationCallbackPost.Post before tracker needed final)) ∨
    (∃ error failed,ForeignResolverPrelude.root hooks id before.machine = .error error failed ∧ RunLoop.reportsUB error = false) := by
  classical
  by_cases need : needed
  · obtain ⟨current,rep⟩ := generation need
    rcases RootAddressOutcome.static_root before hooks tracker world current rep id target backing metadata live notDead alignment noRace classifier
        with success | stopped
    · obtain ⟨pointer,final,actual,⟨post⟩⟩ := success
      exact .inl ⟨pointer,final,actual,⟨RelocationCallbackPost.generated post⟩⟩
    · exact .inr stopped
  · rcases NoDrawBasicRootTotal.static_root before hooks tracker world tables id (noDraw need) with success | stopped
    · obtain ⟨pointer,final,actual,⟨post⟩⟩ := success
      exact .inl ⟨pointer,final,actual,⟨RelocationCallbackPost.cached tables need post⟩⟩
    · exact .inr stopped
end EmptyFunction.RelocationRootStep
