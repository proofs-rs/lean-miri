import empty_function.RelocationRawBinder
import empty_function.RelocationMemoryFold
namespace EmptyFunction.RelocationCurrentFold
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
private theorem fits_demands (before : WholeCall.State) (left right : List (Option AllocId))
    (same : left=right) (addresses : GlobalAddressState) (tape : ExecutionChoices.Tape)
    (fitted : ChoiceSupply.Fits (SourceChoicePlan.ordered before left addresses) tape) :
    ChoiceSupply.Fits (SourceChoicePlan.ordered before right addresses) tape := by cases same; exact fitted
/-- Raw CurrentInput/resources instantiate the finite ordinary-memory branch.
Every source row is retained, including repeated and initially uncached targets.
The explicit target classification is a branch of the unfinished whole proof. -/
theorem convert (s : WholeCall.Static) (p : WholeCall.Packet)
    (input : InputDraft.CurrentInputDraft s p) (resources : Specification.ResourceMargins s p)
    (profile : Specification.RuntimeProfile s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (ordinary : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      p.before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (uncached : ∃ row ∈ source.provenanceMap.ptrs,
      p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none)
    (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic) p.before.machine = .ok converted final ∧
      RelocationMemoryFold.Invariant p.before source resources.budget resources.maximumSize resources.maximumAlignment
        source.provenanceMap.ptrs.size final ∧
      RelocationByteFold.Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  have sourceInput := RelocationInput.memory_source s p input id source selected absent noFunction noVaList descriptor
  obtain ⟨binding,environment⟩ := resources.choices.latent id source
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
  have initial : RelocationMemoryFold.Invariant p.before source resources.budget resources.maximumSize resources.maximumAlignment
      0 p.before.machine := by
    refine ⟨generation,input.tracker,rfl,rfl,rfl,rfl,?_,representation,input.world,?_,?_,environment.strict,profile.noRace,?_,rfl⟩
    · intro oldId old prior; exact prior
    · simpa using resources.addresses generation representation.current
    · simpa using resources.tagRoom input.tracker input.world.enabled
    · have fitted := environment.fits
      change ChoiceSupply.Fits (SourceChoicePlan.ordered p.before binding.demands p.before.machine.user.addresses)
        (ChoiceExecution.tapeAccess.get p.before.machine) at fitted
      exact fits_demands p.before binding.demands _ demandEq _ _ fitted
  apply RelocationMemoryFold.convert p.before source layout hooks externStatic resources.budget resources.maximumSize resources.maximumAlignment
    (RelocationRawBinder.count_resources s p resources id source sourceInput.physical descriptor) _ width pointerWidth
    sourceInput.physical.ordered sourceInput.physical.windows sourceInput.physical.fragments initial
  intro row member
  obtain ⟨target,registered⟩ := ordinary row member
  obtain ⟨rawTarget⟩ := sourceInput.targets row member
  have identity := RelocationBinding.memory_resolved s p.before row.2.allocId rawTarget target registered
  obtain ⟨info,metadata⟩ := RawResources.backing_info p.before row.2.allocId (.global _ registered rfl)
  have bound := RelocationResources.memory_info_bounds s p resources row.2.allocId target info registered metadata
  refine ⟨target,info,registered,metadata,bound.1,bound.2.1,?_,?_,bound.2.2.1,bound.2.2.2⟩
  · simpa only [identity] using rawTarget.live
  · intro missing
    apply rawTarget.uncachedAlignment (by simpa only [identity] using missing) info
    simpa only [identity] using metadata
end EmptyFunction.RelocationCurrentFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationCurrentFold.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation current fold axiom {dependency} in {name}"
