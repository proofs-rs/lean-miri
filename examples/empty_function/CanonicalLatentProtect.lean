import empty_function.CanonicalLatentReborrow
import empty_function.LatentProtectionPost
namespace EmptyFunction.CanonicalLatentProtect
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem tag_room (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p) :
    input.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have tags := resources.tagRoom input.tracker input.world.enabled
  have budget : 64 ≤ resources.budget := by
    have reserve := resources.reserve
    unfold Specification.work at reserve
    omega
  change input.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

private theorem successor_nat (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (allocatedTracker tracker room).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 := by
  change (tracker.global.nextPointerTag.value+1).toNat = _
  rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt]
  change tracker.global.nextPointerTag.value.toNat < 18446744073709551615 at room
  omega

private theorem allocated_world (machine : ChoiceExecution.S) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World machine tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    TreeRuntimeInput.World (allocatedMachine machine tracker room) (allocatedTracker tracker room) := by
  have next := successor_nat tracker room
  refine ⟨rfl,⟨?_,?_⟩,?_⟩
  · intro row member
    have prior := world.globals.protectedBelow row member
    change row.1.value.toNat < (allocatedTracker tracker room).global.nextPointerTag.value.toNat
    rw [next]
    omega
  · intro row member
    have prior := world.globals.rootsBelow row member
    change row.2.value.toNat < (allocatedTracker tracker room).global.nextPointerTag.value.toNat
    rw [next]
    omega
  · intro row member
    obtain ⟨formed⟩ := world.liveTrees row member
    exact ⟨RootTagPost.tree_mono row.2.allocation.extra tracker.global.nextPointerTag
      (allocatedTracker tracker room).global.nextPointerTag formed (by rw [next];omega)⟩

/-- The ordinary-source latent family enters the shared pipeline through the
actual protected unit operation and actual singleton release. The original raw
packet remains the input anchor throughout tag reservation and materialization. -/
theorem protect (s : WholeCall.Static) (p : WholeCall.Packet)
    (metadata : Specification.Metadata s) (input : InputDraft.CurrentInputDraft s p)
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
    (check : s.cfg.retag.checkPtrAccess place.mplace.ptr Size.ZERO
      (withCurrent frames frame (allocatedMachine machine input.tracker (tag_room s p input resources))) =
      .ok () (withCurrent frames frame (allocatedMachine machine input.tracker (tag_room s p input resources))))
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr
      (withCurrent frames frame (allocatedMachine machine input.tracker (tag_room s p input resources))) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (withCurrent frames frame (allocatedMachine machine input.tracker (tag_room s p input resources))))
    (log : s.cfg.retag.logCreation = fun _ _ _ _ _ => pure ())
    (precise : s.cfg.retag.preciseInteriorMut = pure false)
    (freeze : s.cfg.retag.typeIsFreeze place.layout.ty = pure true)
    (size : s.cfg.retag.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none) (pointerSize : Size)
    (target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, s.cfg.access.retainTouched machine none = machine)
    (writeBinding : ∀ place, s.cfg.retag.writeUninit place = (do
      let currentAccess ← ValidityMachine.scopedAccess s.cfg.access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit place))
    (globals : GlobalAllocationHooks Provenance BorrowTree MiriMemoryKind (PlaceMachine.AccessState MiriMemoryKind Configuration.RootUser))
    (extraBinding : s.cfg.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view = {view with machine := {view.machine with memory}}) :
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
  let room := tag_room s p input resources
  let entered := allocatedMachine machine input.tracker room
  let enteredTracker := allocatedTracker input.tracker room
  have initialWorld : TreeRuntimeInput.World machine input.tracker := by
    refine ⟨enabled,input.world.globals,?_⟩
    intro row member
    exact input.world.liveTrees row (by simpa only [memory] using member)
  have enteredWorld : TreeRuntimeInput.World entered enteredTracker := allocated_world machine input.tracker initialWorld room
  have next := successor_nat input.tracker room
  have tags : enteredTracker.global.nextPointerTag.value.toNat+(resources.budget-1) < 2^64 := by
    have prior := resources.tagRoom input.tracker input.world.enabled
    change (allocatedTracker input.tracker room).global.nextPointerTag.value.toNat+_ < _
    rw [next]
    have reserve := resources.reserve
    unfold Specification.work at reserve
    omega
  have fence : RootReservedPost.Fence enteredTracker.global input.tracker.global.nextPointerTag := by
    refine ⟨?_,?_⟩
    · change input.tracker.global.nextPointerTag.value.toNat < (allocatedTracker input.tracker room).global.nextPointerTag.value.toNat
      rw [next]
      omega
    · intro row member equal
      have prior := input.world.globals.rootsBelow row member
      rw [equal] at prior
      exact Nat.lt_irrefl _ prior
  obtain ⟨ensuredMachine,ensuredTracker,entry,tree,reborrow,ensuredEnabled,protectedEq,released,memoryPost,threadsPost,contextPost,rootsPost,addressPost⟩ :=
    CanonicalLatentReborrow.reborrow s p s.limits.retag metadata input resources frames frame {} entered enteredTracker rfl frameBorrow
      memory addresses runtime tape thread enteredWorld tags noRace input.tracker.global.nextPointerTag fence
      id source selected absent noFunction noVaList descriptor ordinary place offset parent parentBinding check resolve log precise freeze
  have protectedRun := LatentProtectionPost.protect_from_reborrow s.cfg.retag s.limits.retag place frames frame machine input.tracker
    enabled room id pointerParent encoding size _ reborrow s.cfg.access unitLayout noMeta aligned pointerSize target retain writeBinding
  have originalFresh := input.world.globals.nextNotProtected
  have protectedShape : ensuredTracker.global.protectedTags = input.tracker.global.protectedTags.insert input.tracker.global.nextPointerTag .StrongProtector := protectedEq
  have release := LatentProtectionPost.release_after_ensure .global globals synchronize frames frame ensuredMachine ensuredTracker
    ensuredEnabled input.tracker.global.protectedTags input.tracker.global.nextPointerTag originalFresh protectedShape id entry tree released
  rw [←extraBinding] at release
  have physical : replaceTree ensuredMachine.memory id entry tree =
      {p.before.machine.memory with live := ((p.before.machine.memory.live.filter fun row => row.1 != id).push
        (id,{entry with allocation := entry.allocation.setExtra tree}))} := by
    simpa only [entered,allocatedMachine,memory] using memoryPost
  refine ⟨ensuredMachine,ensuredTracker,entry,tree,protectedRun,release,?_,?_,?_,?_,?_,threadsPost,physical,ensuredEnabled,protectedShape,released,contextPost⟩
  · apply LatentProtectionPost.original_live p.before _ id {entry with allocation := entry.allocation.setExtra tree} absent
    exact congrArg MemoryState.live physical
  · apply LatentProtectionPost.original_live p.before _ id {entry with allocation := entry.allocation.setExtra tree} absent
    exact congrArg MemoryState.live physical
  · intro old prior
    have equal : old = input.tracker := Option.some.inj (prior.symm.trans input.world.enabled)
    subst old
    exact ⟨_,rfl,rfl⟩

  · intro old prior
    have equal : old = input.tracker := Option.some.inj (prior.symm.trans input.world.enabled)
    subst old
    refine ⟨_,rfl,?_⟩
    exact rootsPost

  · simpa only [Preservation.ExistingAddressFacts,withCurrent,entered,allocatedMachine,addresses] using addressPost

end EmptyFunction.CanonicalLatentProtect
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLatentProtect.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical latent protection axiom {dependency} in {name}"
