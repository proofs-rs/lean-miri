import empty_function.CanonicalLatentPreflight
namespace EmptyFunction.CanonicalLatentProtectAt
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
/-- Internal hit branch of raw canonical preflight; the resolver equation is
obtained by CanonicalLatentPreflight.resolve, not required of valid input. -/
theorem protect (s : WholeCall.Static) (p : WholeCall.Packet)
    (metadata : Specification.Metadata s) (profile : Specification.Profile s) (positive : 0 < s.capacity) (input : InputDraft.CurrentInputDraft s p)
    (resources : Specification.ResourceMargins s p)
    (frames : Array F) (frame : F) (frameBorrow : frame.extra.borrowTracker = some {})
    (machine : ChoiceExecution.S) (enabled : machine.borrowTracker = some input.tracker)
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses)
    (runtime : machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (tape : ChoiceExecution.tapeAccess.get machine = ChoiceExecution.tapeAccess.get p.before.machine)
    (thread : machine.threads.activeThread = p.before.machine.threads.activeThread) (noRace : machine.dataRace = none)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (place : MPlaceTy Provenance) (offset : UInt64) (parent : ProvenanceExtra)
    (pointerParent : Provenance) (encoding : place.mplace.ptr.provenance = some pointerParent)
    (parentBinding : parent = .wildcard ∨ ∃ tag, parent = .concrete tag ∧ input.tracker.global.rootTag? id = some tag)
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr
      (withCurrent frames frame (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (withCurrent frames frame (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))))
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none) :
    ∃ (ensuredMachine : ChoiceExecution.S) (ensuredTracker : MachineHooks.BorrowState) (entry : InputDraft.Entry) (tree : BorrowTree),
      let tag := input.tracker.global.nextPointerTag
      let protectedState := withCurrent frames (registeredFrame frame {} id tag)
        {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree}
      let releasedTracker := {ensuredTracker with global := {ensuredTracker.global with protectedTags := input.tracker.global.protectedTags}}
      let releasedState := withCurrent frames (registeredFrame frame {} id tag)
        {ensuredMachine with borrowTracker := some releasedTracker, memory := replaceTree ensuredMachine.memory id entry tree}
      TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place (withCurrent frames frame machine) = .ok () protectedState ∧
      MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra protectedState = .ok () releasedState ∧
      Preservation.OriginalLiveAllocations p.before protectedState ∧ Preservation.OriginalLiveAllocations p.before releasedState ∧
      Preservation.ExistingProtectors p.before releasedState ∧ Preservation.ExistingRoots p.before releasedState ∧
      Preservation.ExistingAddressFacts p.before releasedState ∧
      ensuredMachine.threads = machine.threads ∧
      replaceTree ensuredMachine.memory id entry tree =
        {p.before.machine.memory with live := ((p.before.machine.memory.live.filter fun row => row.1 != id).push
          (id,{entry with allocation := entry.allocation.setExtra tree}))} ∧
      ensuredMachine.borrowTracker = some ensuredTracker ∧
      ensuredTracker.global.protectedTags = input.tracker.global.protectedTags.insert tag .StrongProtector ∧
      tree.releaseProtector tag ensuredTracker.global.protectedTags = ⟨tree,.Released⟩ ∧
      RelocationContext.view ensuredMachine.user.payload = RelocationContext.view machine.user.payload := by
  have fields := MetadataBinding.fields s metadata positive
  obtain ⟨_resolveBinding,ensure,synchronize⟩ := ConcreteProtection.bindings s metadata positive
  have size : s.cfg.retag.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)) := by
    have sized : place.layout.layout.isSized = true := by rw [layout];exact metadata.unitSized
    simpa only [layout,metadata.unitSize,metadata.unitAlign] using fields.sizeAndAlign place sized
  have unitLayout : localMemoryLayout place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩ := by
    simp [localMemoryLayout,layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  exact CanonicalLatentProtect.protect s p metadata input resources frames frame frameBorrow machine enabled
    memory addresses runtime tape thread noRace id source selected absent noFunction noVaList descriptor ordinary
    place offset parent pointerParent encoding parentBinding
    (by rw [fields.checkPtrAccess]; exact UnitProtection.check_pointer_zero _ _ _)
    resolve fields.log (by rw [fields.precise,profile.precise])
    (by apply fields.freeze;rw [layout];exact metadata.unitFreeze)
    size unitLayout noMeta aligned s.cfg.access.runtime.pointerSize target
    (fun machine => by rw [fields.retainTouched]) fields.writeUninit
    (ConcreteProtection.source s).globals ensure synchronize
end EmptyFunction.CanonicalLatentProtectAt
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.CanonicalLatentProtectAt." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent hit axiom {dependency} in {name}"
