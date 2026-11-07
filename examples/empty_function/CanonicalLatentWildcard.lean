import empty_function.CanonicalLatentProtectAt
import empty_function.LatentPreservation
import empty_function.MemoryInitFinish
import empty_function.WildcardCandidateExact
import empty_function.WildcardEndpoint
namespace EmptyFunction.CanonicalLatentWildcard
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open EmptyFunction.WholeCall EmptyFunction.Configuration EmptyFunction.Specification UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
set_option linter.unusedSimpArgs false

/-- Ordinary latent wildcard sources enter and leave the actual fixed machine.
All conditions below classify initial metadata; no operation-success law is
added to the original current-caller input. -/
theorem result (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtimeProfile : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.MemoryDestination s p input.tracker)
    (wild : destination.place.mplace.ptr.provenance = some .wildcard)
    (classification : CanonicalLatentPreflight.Ordinary s p) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata positive
  let room := ConcreteProtection.tag_room s p input resources
  let tag := input.tracker.global.nextPointerTag
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,frameBorrow,noClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      CanonicalInit.push_actual s metadata profile p runtimeProfile input positive
        (CanonicalInit.normalizedContinuation s continuation)
  have enabled : machine.borrowTracker = some input.tracker := machineTracker.trans input.world.enabled
  have memoryEq : machine.memory = p.before.machine.memory := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  have addressesEq : machine.user.addresses = p.before.machine.user.addresses := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  have runtimeEq : machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  have tapeEq : ChoiceExecution.tapeAccess.get machine = ChoiceExecution.tapeAccess.get p.before.machine := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  have activeEq : machine.threads.activeThread = p.before.machine.threads.activeThread := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  have threadsShape : machine.threads =
      (FrameRelevance.pushedMachine p.before.stack.frames frame previous p.before.machine).threads := by
    rw [machineEq,fields.freshLocalsIdentity]
    unfold FrameRelevance.pushedMachine
    split <;> rfl
  have viewEq : RelocationContext.view machine.user.payload = RelocationContext.view p.before.machine.user.payload := by
    rw [machineEq];unfold FrameRelevance.pushedMachine;rw [fields.freshLocalsIdentity];split <;> rfl
  let spanFrame := {frame with location := .unwinding metadata.localSpan}
  let entered := LocalUnit.current p.before.stack.frames spanFrame (allocatedMachine machine input.tracker room)
  obtain ⟨answer,resolved,_typed,hits⟩ := WildcardCanonical.resolve s metadata positive p.before entered memoryEq addressesEq
    input.tracker destination.place.mplace.ptr destination.pointer wild
  cases answer with
  | none =>
    have modeAndTables : p.before.machine.user.addresses.provenanceMode ≠ .strict ∧ InputDraft.AddressTables p.before := by
      cases destination.pointer with
      | integer encoding => rw [wild] at encoding;cases encoding
      | concrete id tag base tables encoding _ _ _ _ => rw [wild] at encoding;cases Option.some.inj encoding
      | wildcard _ mode tables _ => exact ⟨mode,tables⟩
    have resident : WildcardInit.Resident s p destination.place.mplace.ptr := by
      intro row member exposed geometry
      have chosen := WildcardCandidateExact.resolve s metadata positive p.before entered memoryEq addressesEq
        destination.place.mplace.ptr wild row member modeAndTables.2 modeAndTables.1 exposed geometry
      rw [resolved] at chosen
      cases chosen
    exact WildcardEndpoint.result s metadata profile p runtimeProfile input resources destination wild resident
  | some result =>
    obtain ⟨row,member,equal,exposed,geometry,_backing⟩ := hits
    subst result
    have selected : ChoiceAdmission.SelectedId p row.allocId :=
      .wildcard destination.place.mplace.ptr row (by simp [InputDraft.effectivePointer,destination.encoding]) wild
        member rfl exposed geometry
    obtain ⟨source,absent,noFunction,noVaList,descriptor,ordinary⟩ := classification row.allocId selected
    let id := row.allocId
    obtain ⟨ensured,tracker,entry,tree,protect,pop,oldLiveP,oldLiveR,oldProtected,oldRoots,oldAddresses,
      ensuredThreads,memoryPost,ensuredEnabled,protectedInsert,treeRelease,ensuredView⟩ :=
      CanonicalLatentProtectAt.protect s p metadata profile positive input resources p.before.stack.frames spanFrame frameBorrow
        machine enabled memoryEq addressesEq runtimeEq tapeEq activeEq machineRace id source selected absent noFunction noVaList
        descriptor ordinary destination.place (destination.place.mplace.ptr.offset.bytes-row.address) .wildcard
        .wildcard wild (Or.inl rfl) resolved
        destination.layout destination.sizedMetadata destination.alignmentCache
    let baseFrame : LocalUnit.F := {frame with locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start}
    let changed := {ensured with memory := replaceTree ensured.memory id entry tree}
    let borrow : FrameState := {protectedTags := #[(id,tag)]}
    have initialized : WholeCall.install s p = .ok ()
        (LocalUnit.current p.before.stack.frames (registeredFrame baseFrame {} id tag) changed) := by
      exact MemoryInitFinish.finish s metadata positive p destination.place destination.encoding frame machine changed borrow
        push body identity function location locals noClocks callerArg protect
    have ensuredCtx : ensured.user.payload.payload.user.types = p.before.machine.user.payload.payload.user.types ∧
        ensured.user.payload.ghost = p.before.machine.user.payload.ghost ∧
        ensured.user.payload.validation = p.before.machine.user.payload.validation ∧
        ensured.user.payload.payload.user.host.ioSources = p.before.machine.user.payload.payload.user.host.ioSources ∧
        ensured.user.payload.payload.user.host.control = p.before.machine.user.payload.payload.user.host.control := by
      simpa only [RelocationContext.view,Prod.mk.injEq] using ensuredView.trans viewEq
    have fixed : ensured.threads.fixedScheduling = true := by
      rw [ensuredThreads,threadsShape]
      unfold FrameRelevance.pushedMachine
      split <;> exact runtimeProfile.fixedScheduling
    obtain ⟨thread,active⟩ : ∃ thread, ensured.threads.activeThread? = some thread := by
      rw [ensuredThreads,threadsShape]
      unfold FrameRelevance.pushedMachine
      split
      · refine ⟨{input.thread with topUserRelevantFrame := some p.before.stack.frames.size},?_⟩
        change (p.before.machine.threads.threads.mapIdx (fun index old =>
          if index == p.before.machine.threads.activeThread.toNat then
            {old with topUserRelevantFrame := some p.before.stack.frames.size} else old))[p.before.machine.threads.activeThread.toNat]? = _
        rw [List.getElem?_mapIdx]
        have initialActive := input.active
        change p.before.machine.threads.threads[p.before.machine.threads.activeThread.toNat]? = some input.thread at initialActive
        rw [initialActive]
        simp
      · exact ⟨input.thread,input.active⟩
    obtain ⟨older,original,installEq,depthEq,exec,returned,safe,noUB⟩ :=
      LatentExecution.run s metadata profile p input resources destination (ConcreteProtection.source s).globals
        (ConcreteProtection.bindings s metadata positive).2.1 (ConcreteProtection.bindings s metadata positive).2.2
        baseFrame ensured tracker ensuredEnabled id entry tree protectedInsert treeRelease body identity function rfl rfl noClocks
        returnPlace returning varargs (ensuredCtx.2.1.trans runtimeProfile.ghost) (ensuredCtx.2.2.1.trans runtimeProfile.shallow)
        fixed (by rw [ensuredCtx.2.2.2.2];exact runtimeProfile.gc)
        (by rw [ensuredCtx.2.2.2.2];exact runtimeProfile.unchecked) thread active initialized
    let nextFrame := {BodyStep.withUnit (registeredFrame baseFrame {} id tag) .uninit (some s.abi.ret.layout) with location := .mir ⟨0,1⟩}
    let baseline : ChoiceExecution.S := {ensured with borrowTracker := some {tracker with global := {tracker.global with protectedTags := input.tracker.global.protectedTags}},memory := replaceTree ensured.memory id entry tree}
    have preserved := LatentPreservation.finish s p input destination.place destination.encoding older original
      frame previous nextFrame baseline (thread.topUserRelevantFrame.getD p.before.stack.frames.size) (by simpa only [Preservation.OriginalLiveAllocations,baseline,LocalUnit.current,withCurrent] using oldLiveR)
      (by simpa only [Preservation.ExistingProtectors,baseline,LocalUnit.current,withCurrent] using oldProtected)
      (by simpa only [Preservation.ExistingRoots,baseline,LocalUnit.current,withCurrent] using oldRoots)
      (by simpa only [Preservation.ExistingAddressFacts,baseline,LocalUnit.current,withCurrent] using oldAddresses)
      (ensuredThreads.trans threadsShape) (ensuredView.trans viewEq)
    exact ⟨_,_,installEq,depthEq,exec,returned,preserved,safe,noUB⟩
end EmptyFunction.CanonicalLatentWildcard
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.CanonicalLatentWildcard." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent concrete axiom {dependency} in {name}"
