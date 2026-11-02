import empty_function.RelocationRootStep
namespace EmptyFunction.RelocationCallback
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S

theorem step (s : WholeCall.Static) (anchor : WholeCall.State) (current : S)
    (hooks : ChoiceExecution.H) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World current tracker)
    (tables : InputDraft.AddressTables {anchor with machine := current}) (needed : Prop)
    (generation : needed → ∃ next,InputDraft.GenerationRepresentation {anchor with machine := current} next)
    (memory : current.memory = anchor.machine.memory)
    (runtime : current.user.payload.payload.user.runtime = anchor.machine.user.payload.payload.user.runtime)
    (bases : ∀ id row,anchor.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
      current.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row)
    (provenance : CtfeProvenance) (offset : UInt64)
    (target : InputDraft.RelocationTarget s anchor provenance.allocId)
    (noDraw : ¬needed → RelocationRootStep.CachedOrTypeId {anchor with machine := current} target.resolved)
    (noRace : current.dataRace = none) (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classifier : hooks.classifyAddressError = PointerSource.addressError) :
    (∃ pointer final,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)
      (Pointer.new provenance (Size.ofBytes offset)) current = .ok pointer final ∧
      Nonempty (RelocationCallbackPost.Post {anchor with machine := current} tracker needed final)) ∨
    (∃ error failed,PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks (ForeignResolverPrelude.resolver s hooks)
      (Pointer.new provenance (Size.ofBytes offset)) current = .error error failed ∧ RunLoop.reportsUB error = false) := by
  classical
  obtain ⟨info,metadata⟩ := RawResources.backing_info anchor target.resolved target.backing
  have currentMetadata : current.memory.getAllocInfo target.resolved = .ok info := by rw [memory];exact metadata
  have currentLive : current.memory.isAllocLive target.resolved = true := by rw [memory];exact target.live
  have notDead := LiveMetadata.not_dead current.memory target.resolved currentLive info currentMetadata
  have currentBacking := AddressTransport.backing anchor {anchor with machine := current} memory target.resolved target.backing
  have alignment : current.user.addresses.baseAddr.find? (fun row => row.allocId == target.resolved) = none →
      info.kind ≠ .typeId → InputDraft.AlignmentRepresentation info.align := by
    intro missing _
    have originalMissing : anchor.machine.user.addresses.baseAddr.find? (fun row => row.allocId == target.resolved) = none := by
      cases original : anchor.machine.user.addresses.baseAddr.find? (fun row => row.allocId == target.resolved) with
      | none => rfl
      | some row =>
        have retained := bases target.resolved row original
        rw [missing] at retained
        cases retained
    exact target.uncachedAlignment originalMissing info metadata
  rcases target with ⟨resolved,mapping,backing,live,rawAlignment⟩
  cases mapping with
  | direct same supplier predicates format =>
    subst resolved
    have admission : RawRootAdmission.Normal current.memory provenance.allocId := by
      rw [memory]
      exact ⟨supplier,predicates,format⟩
    exact RelocationRootStep.normal {anchor with machine := current} hooks (ForeignResolverPrelude.resolver s hooks) tracker world tables needed
      generation provenance offset info admission currentBacking currentMetadata currentLive notDead alignment noDraw noRace width classifier
  | foreign global definition descriptor payload selection =>
    let Post := fun final => Nonempty (RelocationCallbackPost.Post {anchor with machine := current} tracker needed final)
    have initial : Post current := ⟨RelocationCallbackPost.identical {anchor with machine := current} tracker needed world tables generation⟩
    have rootStage : ForeignSelectionPartial.IsExported selection →
        (∃ pointer final,ForeignResolverPrelude.root hooks resolved current = .ok pointer final ∧
          final.memory = anchor.machine.memory ∧ Post final) ∨
        (∃ error failed,ForeignResolverPrelude.root hooks resolved current = .error error failed ∧ RunLoop.reportsUB error = false) := by
      intro _
      rcases RelocationRootStep.static_root {anchor with machine := current} hooks tracker world tables needed generation resolved info
        currentBacking currentMetadata currentLive notDead alignment noDraw noRace classifier with success | stopped
      · obtain ⟨pointer,final,actual,post⟩ := success
        obtain ⟨witness⟩ := post
        exact .inl ⟨pointer,final,actual,witness.memory.trans memory,⟨witness⟩⟩
      · exact .inr stopped
    have runtimeExtern : current.user.payload.payload.user.runtime.externStatics = ExternMapping.runtime anchor := by
      rw [runtime]
      rfl
    have currentDescriptor : current.memory.findGlobal? provenance.allocId = some global := by rw [memory];exact descriptor
    rcases ForeignSelectionPartial.resolve_when_exported s hooks anchor current memory runtimeExtern definition resolved selection Post initial rootStage
      with success | stopped
    · obtain ⟨pointer,final,actual,_,post,_⟩ := success
      refine .inl ⟨pointer,final,?_,post⟩
      unfold PointerSource.globalRootPointer
      simp [Pointer.new,currentDescriptor,payload,actual,get,getThe,MonadStateOf.get,EStateM.get,
        bind,Bind.bind,EStateM.bind,pure,EStateM.pure]
    · obtain ⟨error,failed,actual,nonUB⟩ := stopped
      refine .inr ⟨error,failed,?_,nonUB⟩
      unfold PointerSource.globalRootPointer
      simp [Pointer.new,currentDescriptor,payload,actual,get,getThe,MonadStateOf.get,EStateM.get,
        bind,Bind.bind,EStateM.bind,pure,EStateM.pure]
end EmptyFunction.RelocationCallback
