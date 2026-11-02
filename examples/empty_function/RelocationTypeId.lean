import empty_function.RelocationAdmittedRoot
import empty_function.AddressPost
namespace EmptyFunction.RelocationTypeId
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem assignment (state : GlobalAddressState) (id : AllocId) (info : AllocationInfo)
    (choices : AddressRandomChoices) (thread : UInt32)
    (missing : state.baseAddr.find? (fun row => row.allocId == id) = none) :
    state.addrFromAllocId id (some ⟨.typeId,true,info.size,info.align,some .other,thread⟩) choices =
      ⟨{state with baseAddr := state.baseAddr.push ⟨id,0⟩},.ok (.ready 0)⟩ := by
  simp only [GlobalAddressState.addrFromAllocId]
  unfold_reuse ".GlobalAddressState.findBase"
  simp only [missing,Option.map_none]
  simp only [show (AllocationAddressKind.typeId == .dead) = false from rfl,
    show (AllocationAddressKind.typeId == .typeId) = true from rfl,
    Bool.not_true,Bool.or_self,Bool.false_eq_true,↓reduceIte,AddressPost.cache_zero _ id missing,
    pure,Pure.pure,bind,Bind.bind,Id.run]

/-- TypeId's actual uncached address path caches zero and consumes no choice,
even without an address generator. This is not a resource-exclusion premise. -/
theorem address (hooks : ChoiceExecution.H) (state : ChoiceExecution.S) (id : AllocId) (info : AllocationInfo)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info) (kind : info.kind = .typeId)
    (live : state.memory.isAllocLive id = true) :
    MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks id (some .other) state =
      .ok 0 {state with user := {state.user with addresses :=
        {state.user.addresses with baseAddr := state.user.addresses.baseAddr.push ⟨id,0⟩}}} := by
  have pureAddress : state.user.addresses.addrFromAllocId id
      (some ⟨.typeId,true,info.size,info.align,some .other,UInt32.ofNat state.threads.activeThread.toNat⟩)
      ⟨false,false,0,⟨0,by decide⟩⟩ ⟨none⟩ =
        ⟨{state.user.addresses with baseAddr := state.user.addresses.baseAddr.push ⟨id,0⟩},.ok (.ready 0)⟩ := by
    simp only [GlobalAddressState.addrFromAllocId]
    unfold_reuse ".GlobalAddressState.findBase"
    simp only [missing,Option.map_none]
    simp only [show (AllocationAddressKind.typeId == .dead) = false from rfl,
      show (AllocationAddressKind.typeId == .typeId) = true from rfl,
      Bool.not_true,Bool.or_self,Bool.false_eq_true,↓reduceIte,AddressPost.cache_zero _ id missing,
      pure,Pure.pure,bind,Bind.bind,Id.run]
  have zeroFin : (⟨0,by decide⟩ : Fin 16) = 0 := rfl
  rw [zeroFin] at pureAddress
  unfold MachineAddress.addrFromAllocId MachineAddress.assign
  unfold_machine_address_helpers
  simp [missing,metadata,kind,live,pureAddress,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,EStateM.bind,pure,EStateM.pure]
/-- The zero-draw TypeId address result is used by the actual admitted root
pipeline, including a fresh root tag and the source wrapping offset. -/
theorem root (before : ChoiceExecution.S) (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64) (info : AllocationInfo)
    (admission : RawRootAdmission.Normal before.memory provenance.allocId)
    (enabled : before.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 2^64)
    (missing : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = none)
    (metadata : before.memory.getAllocInfo provenance.allocId = .ok info) (kind : info.kind = .typeId)
    (live : before.memory.isAllocLive provenance.allocId = true)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ (global : GlobalState) (tag : BorTag),
      tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
      PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
        (Pointer.new provenance (Size.ofBytes offset)) before =
        .ok (Pointer.new (.concrete provenance.allocId tag) (Size.ofBytes offset))
          {before with borrowTracker := some {tracker with global}, user := {before.user with addresses :=
            {before.user.addresses with baseAddr := before.user.addresses.baseAddr.push ⟨provenance.allocId,0⟩}}} := by
  obtain ⟨global,tag,tagged,_protected,_tracked⟩ := RelocationRoot.root_tag_room tracker.global provenance.allocId tagRoom
  let rooted : ChoiceExecution.S := {before with borrowTracker := some {tracker with global}}
  have assigned := address hooks rooted provenance.allocId info missing metadata kind live
  have actual := RawRootAdmission.root_address ChoiceExecution.tapeAccess hooks externStatic before tracker provenance offset 0 tag global _
    admission enabled tagged assigned width
  refine ⟨global,tag,tagged,?_⟩
  simpa only [UInt64.zero_add] using actual

end EmptyFunction.RelocationTypeId
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationTypeId.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved typeId relocation axiom {dependency} in {name}"
