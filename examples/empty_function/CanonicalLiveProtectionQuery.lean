import empty_function.CommonEnsureRaw
import empty_function.LiveProtectionOutcome
import empty_function.ProtectionEnsureError
import empty_function.LiveQueryTransport
import empty_function.InitialQueryTransport
import empty_function.ReturnGeometry
import empty_function.ProtectionWorld
import empty_function.MemoryPartition
namespace EmptyFunction.CanonicalLiveProtectionQuery
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.ProtectionOutcome EmptyFunction.LiveProtectionOutcome EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem ensure_live (s : Static) (metadata : Metadata s) (current : State)
    (id : AllocId) (entry : InputDraft.Entry)
    (live : current.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    s.cfg.retag.ensureTreeExtra id current = .ok () current := by
  rw [(CanonicalEnsureRoute.fields s metadata).ensure,(CanonicalEnsureRoute.fields s metadata).globalConstruction]
  change GlobalAllocationMachine.ensure .global
    (GlobalAllocationMachine.hooks s.prepared.compiler.runtime.target.base
      (MaterializationPreservation.extras s) (MaterializationPreservation.globalLeaves s)
      (CanonicalEnsureRoute.initializer s)) id current = .ok () current
  simp [GlobalAllocationMachine.ensure,MemoryLifecycle.getAllocRaw,live,
    GlobalAllocationMachine.hooks,get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,EStateM.bind,pure,EStateM.pure,Id.run]


/-- A successful actual live protection preserves the old indirect parent
inbounds query. Materialization failures contradict the observed success;
node/tree changes are transported by their exact metadata snapshot. -/
theorem query (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noMetadata : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (before : Machine)
    (enabled : before.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : before.memory = p.before.machine.memory)
    (addresses : before.user.addresses = p.before.machine.user.addresses)
    (runtime : before.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (noRace : before.dataRace = none)
    (_effective : InputDraft.effectivePointer p = some place.mplace.ptr)
    (global : GlobalState) (tag : BorTag)
    (tagged : input.tracker.global.newPointerTag = .ok (global,tag))
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra)
    (resolve : s.cfg.retag.resolveAllocation place.mplace.ptr
      (LocalUnit.current frames frame (taggedMachine before input.tracker global)) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩)
        (LocalUnit.current frames frame (taggedMachine before input.tracker global)))
    (info : AllocationInfo) (classification : before.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (selected : ChoiceAdmission.SelectedId p id) (backing : InputDraft.Backing s p.before id)
    -- Successful protection is observed, rather than assumed at caller admission.
    (afterState : State)
    (success : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag place
      (LocalUnit.current frames frame before) = .ok () afterState)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old)
    (amount : Size) (projected : destination.offset = some amount)
    (_positive : amount.bytes ≠ 0) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers afterState old amount .inbounds .none =
      .ok (ProjectedIndirectPreflight.shifted old amount) := by
  let allocated := taggedMachine before input.tracker global
  let registered := registeredMachine allocated {input.tracker with global} tag
  let registeredFrame := UnitRetag.registeredFrame frame {} id tag
  let current := LocalUnit.current frames registeredFrame registered
  have oldWorld := ProtectionWorld.anchor s p input before enabled memory
  have allocatedWorld : TreeRuntimeInput.World allocated {input.tracker with global} :=
    ProtectionWorld.allocated before input.tracker oldWorld global tag tagged
  obtain ⟨_room,tagEq,next,_roots,_protectors,_tracked⟩ := ResourceFailures.tag_success input.tracker.global global tag tagged
  have below : tag.value.toNat < global.nextPointerTag.value.toNat := by rw [tagEq,next];omega
  have registeredWorld : TreeRuntimeInput.World registered (registeredTracker {input.tracker with global} tag) :=
    ProtectionWorld.registered allocated {input.tracker with global} allocatedWorld tag below
  cases initialLive : before.memory.live.find? (fun row => row.1 == id) with
  | some row =>
    have identity : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some initialLive
    have live : registered.memory.live.find? (fun row => row.1 == id) = some (id,row.2) := by
      change before.memory.live.find? (fun row => row.1 == id) = _
      rw [initialLive]
      exact congrArg some (Prod.ext identity rfl)
    have ensured := ensure_live s metadata current id row.2 live
    have formed := registeredWorld.liveTrees (id,row.2) (Array.mem_of_find?_eq_some live)
    apply LiveQueryTransport.query s metadata profile place frames frame before input.tracker global tag
      layout noMetadata aligned enabled frameBorrow tagged id offset parent resolve info classification data
      registered (registeredTracker {input.tracker with global} tag) ensured row.2 live _ formed registeredWorld.enabled
      afterState success old amount
    exact InitialQueryTransport.query s metadata p input.tracker destination old indirect amount projected current memory addresses
  | none =>
    have absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none := by rw [←memory];exact initialLive
    rcases MemoryPartition.selected s p id selected backing with resident | ⟨source,sourceSelected⟩
    · rcases resident with ⟨entry,live⟩ | nondata
      · rw [absent] at live
        cases live
      · obtain ⟨other,classified,notData⟩ := NondataProtection.classification p.before id nondata
        have classifiedBefore : before.memory.getAllocInfo id = .ok other := by rw [memory];exact classified
        have same : info = other := Except.ok.inj (classification.symm.trans classifiedBefore)
        exact False.elim (notData (same ▸ data))
    · rcases CommonEnsureTotal.ensure s metadata p input id source sourceSelected current
        memory addresses runtime (registeredTracker {input.tracker with global} tag) registeredWorld noRace with
        ⟨error,failed,failedEnsure,nonUB⟩ |
        ⟨ensuredMachine,ensuredTracker,entry,ensured,world,live,_stable,oldLive,geometry,kept⟩
      · have stopped := ProtectionEnsureError.actual s metadata profile place frames frame before input.tracker global tag
          layout enabled frameBorrow tagged id offset parent resolve info classification data error failed failedEnsure
        rw [success] at stopped
        cases stopped
      · have formed := world.liveTrees (id,entry) (Array.mem_of_find?_eq_some live)
        apply LiveQueryTransport.query s metadata profile place frames frame before input.tracker global tag
          layout noMetadata aligned enabled frameBorrow tagged id offset parent resolve info classification data
          ensuredMachine ensuredTracker ensured entry live _ formed world.enabled afterState success old amount
        exact ReturnGeometry.destination_query s metadata p input.tracker destination amount projected old indirect
          {current with machine := ensuredMachine} (fun _ => ⟨oldLive,kept,geometry⟩)
end EmptyFunction.CanonicalLiveProtectionQuery

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.CanonicalLiveProtectionQuery.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved canonical-live-query axiom {dependency} in {name}"
