import empty_function.RelocationBinding
import empty_function.RelocationInvariant
namespace EmptyFunction.RelocationInput
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

/-- Current effective-pointer classification supplies the selected backing;
this is raw selection geometry, not an operational resolver-success premise. -/
theorem selected_backing (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (id : AllocId)
    (selected : ChoiceAdmission.SelectedId p id) : InputDraft.Backing s p.before id := by
  cases selected with
  | concrete pointer tag effective provenance =>
    have pointerInput := input.effective pointer effective
    cases pointerInput with
    | integer encoding => rw [provenance] at encoding; cases encoding
    | concrete actualId actualTag _ _ encoding _ backing _ _ =>
      have same := Provenance.concrete.inj (Option.some.inj (encoding.symm.trans provenance))
      rcases same with ⟨rfl,_⟩
      exact backing
    | wildcard encoding _ _ _ => rw [provenance] at encoding; cases encoding
  | wildcard pointer row effective provenance rowAt identity exposed geometry =>
    have pointerInput := input.effective pointer effective
    cases pointerInput with
    | integer encoding => rw [provenance] at encoding; cases encoding
    | concrete _ _ _ _ encoding _ _ _ _ => rw [provenance] at encoding; cases encoding
    | wildcard _ _ _ select =>
      rw [←identity]
      exact select row rowAt (by simpa only [identity] using exposed) geometry

/-- The existing raw ordinary-memory descriptor record contains the compiler
relocation format/targets. No materialization, retag or copy succeeds by assumption. -/
theorem memory_source (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    InputDraft.RelocationInput s p.before source := by
  have backing := selected_backing s p input id selected
  cases backing with
  | live entry row => rw [absent] at row; cases row
  | global entry query _ content _ _ =>
    have same := Option.some.inj (query.symm.trans descriptor)
    cases same
    cases content with
    | memory actual kind payload _ _ _ sourceInput =>
      have same := GlobalAllocationPayload.memory.inj (Option.some.inj payload)
      cases same
      exact sourceInput
    | internalStatic _ _ kind _ _ _ _ _ _ => cases kind
    | externalStatic _ kind _ => cases kind
    | threadLocalStatic _ _ kind _ => cases kind
    | function kind => cases kind
    | vtable kind => cases kind
    | typeId kind => cases kind
  | extraFunction row =>
    unfold MemoryState.hasExtraFunctionId at row
    have impossible : p.before.machine.memory.hasFunctionPointer id = true := by
      simp only [MemoryState.hasFunctionPointer,row,Bool.true_or]
    rw [noFunction] at impossible
    cases impossible
  | vaList row => rw [noVaList] at row; cases row
  | dead _ _ _ _ _ noGlobal => rw [descriptor] at noGlobal; cases noGlobal
/-- CurrentInput and its existing ResourceMargins supply all first-operation
facts for an ordinary-memory first relocation. The source may have any finite
remaining relocation list. No operation-success/headroom field is added. -/
theorem first_memory (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p)
    (profile : Specification.RuntimeProfile s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (row : Size × CtfeProvenance) (rest : List (Size × CtfeProvenance))
    (rows : source.provenanceMap.ptrs.toList = row::rest)
    (target : Allocation CtfeProvenance Unit)
    (targetDescriptor : p.before.machine.memory.findGlobal? row.2.allocId = some
      ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (missing : p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none)
    (hooks : ChoiceExecution.H)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (offset : UInt64) (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ (tail : List (Option AllocId)) (pointer : Pointer Provenance) (final : ChoiceExecution.S),
      SourceChoicePlan.Rows (fun row demand => SourceChoicePlan.Demand s p.before row.2.allocId demand) rest tail ∧
      PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
      (Pointer.new row.2 (Size.ofBytes offset)) p.before.machine = .ok pointer final ∧
      final.memory = p.before.machine.memory ∧ final.threads = p.before.machine.threads ∧
      ChoiceSupply.Fits (SourceChoicePlan.ordered p.before tail final.user.addresses)
        (ChoiceExecution.tapeAccess.get final) ∧
      ∃ next nextTracker, InputDraft.GenerationRepresentation {p.before with machine := final} next ∧
        TreeRuntimeInput.World final nextTracker ∧
        nextTracker.global.nextPointerTag.value.toNat+(resources.budget-1) < 2^64 ∧
        InputDraft.GenerationResources next (resources.budget-1) resources.maximumSize resources.maximumAlignment ∧ final.dataRace = none := by
  have sourceInput := memory_source s p input id source selected absent noFunction noVaList descriptor
  have listMember : row ∈ source.provenanceMap.ptrs.toList := by rw [rows]; simp
  have member : row ∈ source.provenanceMap.ptrs := by simpa using listMember
  obtain ⟨binding,environment⟩ := resources.choices.latent id source
    (.memory selected absent noFunction noVaList descriptor)
  obtain ⟨tail,head⟩ := RelocationBinding.memory_head s p.before source binding row rest rows target targetDescriptor
  obtain ⟨info,metadata⟩ := RawResources.backing_info p.before row.2.allocId
    (.global _ targetDescriptor rfl)
  have bounds := RelocationResources.memory_info_bounds s p resources row.2.allocId target info targetDescriptor metadata
  obtain ⟨generation,representation,alignment⟩ := RelocationBinding.generation_alignment s p.before
    source sourceInput row member target info targetDescriptor missing metadata bounds.2.1
  obtain ⟨targetInput⟩ := sourceInput.targets row member
  have identity := RelocationBinding.memory_resolved s p.before row.2.allocId targetInput target targetDescriptor
  have live : p.before.machine.memory.isAllocLive row.2.allocId = true := by
    simpa only [identity] using targetInput.live
  have minimum : 64 ≤ Specification.work s p := by unfold Specification.work; omega
  have one : 1 ≤ resources.budget := by have := resources.reserve; omega
  have tagRoom : input.tracker.global.nextPointerTag.value.toNat + 1 < 2^64 := by
    have reserved := resources.tagRoom input.tracker input.world.enabled
    omega
  have rooms := RawResources.room s p resources generation representation.current info.size info.align alignment
    bounds.2.2.1 bounds.2.2.2 one
  have fitted := RelocationBinding.first_fits s p.before source binding environment row.2.allocId tail head info
    missing metadata bounds.1 bounds.2.1 live
  have correspondence := RelocationBinding.tail_rows s p.before source binding row rest tail rows head
  obtain ⟨pointer,final,actual,memory,threads,tailFits,strictFinal,next,rep,shape,tagPost,_basePost,_static⟩ := RelocationEntry.memory_fits p.before generation representation hooks externStatic input.tracker row.2 offset target info
    (SourceChoicePlan.ordered p.before tail) targetDescriptor input.world.enabled tagRoom missing metadata bounds.1 bounds.2.1 live
    profile.noRace alignment rooms (resources.addresses generation representation.current).positiveCursor width
    environment.strict fitted
  obtain ⟨nextTracker,world,tags,numeric⟩ := RelocationInvariant.successor p.before final input.tracker generation next
    resources.budget resources.maximumSize resources.maximumAlignment row.2.allocId info.size info.align input.world
    (resources.addresses generation representation.current) one (resources.tagRoom input.tracker input.world.enabled)
    (RawGenerator.normalized_exponent info.align alignment.choose alignment.choose_spec.2)
    bounds.2.2.1 (by
      rw [RawGenerator.alignment_nat info.align (RawGenerator.normalized_exponent info.align alignment.choose alignment.choose_spec.2)]
      exact bounds.2.2.2) memory shape tagPost
  obtain ⟨_,_,_,_,race,_runtime,_context⟩ := tagPost
  exact ⟨tail,pointer,final,correspondence,actual,memory,threads,tailFits,next,nextTracker,rep,world,tags,numeric,race.trans profile.noRace⟩
end EmptyFunction.RelocationInput
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationInput.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation input axiom {dependency} in {name}"
