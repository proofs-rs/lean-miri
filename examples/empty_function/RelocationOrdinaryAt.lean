import empty_function.RelocationOrdinaryConversion
import empty_function.RelocationReservedFold
import empty_function.RelocationReservedCachedFold
import empty_function.AddressTransport
namespace EmptyFunction.RelocationOrdinaryAt
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem info_eq (anchor snapshot : WholeCall.State)
    (memory : snapshot.machine.memory = anchor.machine.memory)
    (thread : snapshot.machine.threads.activeThread = anchor.machine.threads.activeThread) (id : AllocId) :
    SourceChoicePlan.info snapshot id = SourceChoicePlan.info anchor id := by
  simp only [SourceChoicePlan.info,memory,thread]

/-- The raw metadata snapshot and active thread determine the entire actual
ordered address-demand plan, independently of tracker and caller-frame updates. -/
private theorem ordered_eq (anchor snapshot : WholeCall.State)
    (memory : snapshot.machine.memory = anchor.machine.memory)
    (thread : snapshot.machine.threads.activeThread = anchor.machine.threads.activeThread)
    (demands : List (Option AllocId)) (addresses : GlobalAddressState) :
    SourceChoicePlan.ordered snapshot demands addresses = SourceChoicePlan.ordered anchor demands addresses := by
  induction demands generalizing addresses with
  | nil => rfl
  | cons head tail ih =>
    have continuation : SourceChoicePlan.ordered snapshot tail = SourceChoicePlan.ordered anchor tail := funext ih
    cases head <;> simp only [SourceChoicePlan.ordered,continuation,info_eq anchor snapshot memory thread]

/-- Conversion post at an actual prefix: the source anchor remains fixed and
the already reserved child remains outside every subsequently cached root. -/
def Post (current : ChoiceExecution.S) (budget count : Nat) (reserved : BorTag) (final : ChoiceExecution.S) : Prop :=
  final.memory = current.memory ∧ final.threads = current.threads ∧
  final.user.payload.payload.user.runtime = current.user.payload.payload.user.runtime ∧
  RelocationContext.view final.user.payload = RelocationContext.view current.user.payload ∧
  AddressStaticPost.Facts current.user.addresses final.user.addresses ∧ final.dataRace = none ∧
  ∃ tracker, TreeRuntimeInput.World final tracker ∧
    tracker.global.nextPointerTag.value.toNat+(budget-count) < 2^64 ∧ RootReservedPost.Fence tracker.global reserved ∧
      (∀ initialTracker, current.borrowTracker = some initialTracker → RootFramePost.Frame initialTracker.global tracker.global)

/-- The original raw input and reserves apply at the actual tag-reservation
prefix. Only metadata/choice equalities are transported; no replacement packet
is asserted to satisfy CurrentInput or a rebuilt ResourceMargins record. -/
theorem convert (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p)
    (current : ChoiceExecution.S)
    (memory : current.memory = p.before.machine.memory)
    (addresses : current.user.addresses = p.before.machine.user.addresses)
    (runtime : current.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (tape : ChoiceExecution.tapeAccess.get current = ChoiceExecution.tapeAccess.get p.before.machine)
    (thread : current.threads.activeThread = p.before.machine.threads.activeThread)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World current tracker)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+(resources.budget-1) < 2^64)
    (noRace : current.dataRace = none) (reserved : BorTag) (fence : RootReservedPost.Fence tracker.global reserved)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic) current = .ok converted final ∧
      Post current (resources.budget-1) source.provenanceMap.ptrs.size reserved final ∧
      final.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime ∧
      RelocationByteFold.Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  classical
  let snapshot : WholeCall.State := {p.before with machine := current}
  have sourceInput := RelocationInput.memory_source s p input id source selected absent noFunction noVaList descriptor
  have spare := RelocationOrdinaryConversion.spare s p resources id source sourceInput.physical descriptor
  have count : source.provenanceMap.ptrs.size ≤ resources.budget-1 := by omega
  by_cases uncached : ∃ row ∈ source.provenanceMap.ptrs,
      p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none
  · obtain ⟨binding,environment⟩ := resources.choices.latent id source
      (.memory selected absent noFunction noVaList descriptor)
    have demandEq := RelocationRawBinder.demands s p.before source.provenanceMap.ptrs.toList binding.demands binding.correspondence
      (fun row member => ordinary row (by simpa using member))
    obtain ⟨missingRow,member,missing⟩ := uncached
    obtain ⟨target,registered⟩ := ordinary missingRow member
    obtain ⟨rawTarget⟩ := sourceInput.targets missingRow member
    have identity := RelocationBinding.memory_resolved s p.before missingRow.2.allocId rawTarget target registered
    obtain ⟨missingInfo,missingMetadata⟩ := RawResources.backing_info p.before missingRow.2.allocId (.global _ registered rfl)
    have missingBounds := RelocationResources.memory_info_bounds s p resources missingRow.2.allocId target missingInfo registered missingMetadata
    obtain ⟨generation,representation⟩ := sourceInput.generation
      ⟨missingRow,member,rawTarget,(by simpa only [identity] using missing),missingInfo,
        (by simpa only [identity] using missingMetadata),missingBounds.2.1⟩
    have currentRep : InputDraft.GenerationRepresentation snapshot generation :=
      AddressTransport.representation p.before snapshot memory addresses generation representation
    have numeric := RelocationNumeric.unchanged generation generation.reusePool resources.budget
      resources.maximumSize resources.maximumAlignment (resources.addresses generation representation.current)
    have initial : RelocationReservedFold.Invariant snapshot source reserved (resources.budget-1)
        resources.maximumSize resources.maximumAlignment 0 current := by
      refine ⟨generation,tracker,rfl,rfl,rfl,rfl,?_,currentRep,world,?_,?_,?_,noRace,?_,fence,?_,rfl⟩
      · intro oldId old prior; exact prior
      · simpa using numeric
      · simpa using tagRoom
      · rw [tape]
        exact environment.strict
      · have fitted := environment.fits
        change ChoiceSupply.Fits (SourceChoicePlan.ordered p.before binding.demands p.before.machine.user.addresses)
          (ChoiceExecution.tapeAccess.get p.before.machine) at fitted
        rw [←addresses,←tape] at fitted
        rw [←ordered_eq p.before snapshot memory thread] at fitted
        rw [demandEq] at fitted
        exact fitted
      · intro initial enabled
        have same : initial = tracker := Option.some.inj (enabled.symm.trans world.enabled)
        subst initial
        exact ⟨rfl,rfl,by intro id tag prior; exact prior⟩
    have targets : ∀ row ∈ source.provenanceMap.ptrs,
        RelocationReservedFold.Target snapshot resources.maximumSize resources.maximumAlignment row := by
      intro row member
      obtain ⟨target,registered⟩ := ordinary row member
      obtain ⟨rawTarget⟩ := sourceInput.targets row member
      have identity := RelocationBinding.memory_resolved s p.before row.2.allocId rawTarget target registered
      obtain ⟨info,metadata⟩ := RawResources.backing_info p.before row.2.allocId (.global _ registered rfl)
      have bound := RelocationResources.memory_info_bounds s p resources row.2.allocId target info registered metadata
      refine ⟨target,info,by simpa only [snapshot,memory] using registered,
        by simpa only [snapshot,memory] using metadata,bound.1,bound.2.1,?_,?_,bound.2.2.1,bound.2.2.2⟩
      · simpa only [snapshot,memory,identity] using rawTarget.live
      · intro missing
        apply rawTarget.uncachedAlignment (by simpa only [snapshot,addresses,identity] using missing) info
        simpa only [identity] using metadata
    obtain ⟨converted,final,actual,invariant,attributes,keys,fragments⟩ := RelocationReservedFold.convert snapshot source layout
      hooks externStatic reserved (resources.budget-1) resources.maximumSize resources.maximumAlignment count targets
      width pointerWidth sourceInput.physical.ordered sourceInput.physical.windows sourceInput.physical.fragments initial
    obtain ⟨_generation,_tracker,memPost,threadsPost,runtimePost,contextPost,_cache,_rep,worldPost,_numbers,tags,_strict,race,_fits,fencePost,framePost,staticPost⟩ := invariant
    have addressFacts : AddressStaticPost.Facts current.user.addresses final.user.addresses :=
      AddressStaticPost.facts snapshot {snapshot with machine := final} currentRep.tables _rep.tables memPost _cache staticPost
    exact ⟨converted,final,actual,⟨memPost,threadsPost,runtimePost,contextPost,addressFacts,race,_tracker,worldPost,tags,fencePost,framePost⟩,
      runtimePost.trans runtime,attributes,keys,fragments⟩
  · have cached : ∀ row ∈ source.provenanceMap.ptrs, ∃ base,
        current.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = some ⟨row.2.allocId,base⟩ := by
      intro row member
      rw [addresses]
      cases prior : p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) with
      | none => exact False.elim (uncached ⟨row,member,prior⟩)
      | some entry =>
        have identifier : entry.allocId = row.2.allocId := by
          have test := Array.find?_some prior
          exact of_decide_eq_true test
        exact ⟨entry.address,by cases entry;simp_all⟩
    have initial : RelocationReservedCachedFold.Invariant current reserved (resources.budget-1) 0 current :=
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,noRace,tracker,world,by simpa using tagRoom,fence,(by intro initial enabled; have same : initial = tracker := Option.some.inj (enabled.symm.trans world.enabled); subst initial; exact ⟨rfl,rfl,by intro id tag prior; exact prior⟩)⟩
    obtain ⟨converted,final,actual,invariant,attributes,keys,fragments⟩ := RelocationReservedCachedFold.convert current source layout
      hooks externStatic reserved (resources.budget-1) count
      (by intro row member;simpa only [memory] using ordinary row member) cached width pointerWidth
      sourceInput.physical.ordered sourceInput.physical.windows sourceInput.physical.fragments initial
    obtain ⟨memPost,threadsPost,_addresses,_tape,runtimePost,contextPost,race,nextTracker,worldPost,tags,fencePost,framePost⟩ := invariant
    exact ⟨converted,final,actual,⟨memPost,threadsPost,runtimePost,contextPost,AddressStaticPost.identical _ _ _addresses,race,nextTracker,worldPost,tags,fencePost,framePost⟩,
      runtimePost.trans runtime,attributes,keys,fragments⟩
end EmptyFunction.RelocationOrdinaryAt
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationOrdinaryAt.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary prefix conversion axiom {dependency} in {name}"
