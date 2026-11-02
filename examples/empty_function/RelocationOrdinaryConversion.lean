import empty_function.RelocationCurrentFold
import empty_function.RelocationCachedFold
namespace EmptyFunction.RelocationOrdinaryConversion
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

def Post (snapshot : ChoiceExecution.S) (budget count : Nat) (final : ChoiceExecution.S) : Prop :=
  final.memory = snapshot.memory ∧ final.threads = snapshot.threads ∧
  final.user.payload.payload.user.runtime = snapshot.user.payload.payload.user.runtime ∧
  RelocationContext.view final.user.payload = RelocationContext.view snapshot.user.payload ∧
  final.dataRace = none ∧ ∃ tracker, TreeRuntimeInput.World final tracker ∧
    tracker.global.nextPointerTag.value.toNat+(budget-count) < 2^64

private theorem member_le_sum (values : List Nat) (value : Nat) (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst value; simp only [List.sum_cons]; omega
    · have bound := ih later; simp only [List.sum_cons]; omega

/-- Source bytes occur in the existing work count, leaving the fixed reserve
for post-conversion root initialization as well as all relocation callbacks. -/
theorem spare (s : WholeCall.Static) (p : WholeCall.Packet) (resources : Specification.ResourceMargins s p)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (physical : InputDraft.CompilerAllocation source)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    source.provenanceMap.ptrs.size+64 ≤ resources.budget := by
  have member := RelocationResources.global_mem p.before id _ descriptor
  have memberBytes : source.byteSize.bytes.toNat ∈
      (p.before.machine.memory.globals.toList.map (fun row => row.size.bytes.toNat)) := by
    apply List.mem_map.mpr
    exact ⟨_,by simpa using member,rfl⟩
  have bound := member_le_sum _ _ memberBytes
  have counted := RelocationRawBinder.count source physical
  have storage := physical.storage
  have reserve := resources.reserve
  unfold Specification.work at reserve
  omega

/-- Both cached-only and address-generation branches instantiate the unchanged
converter from the existing raw current input. No generator is required when
all targets are cached, and no additional ABI fact is required for those rows. -/
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
    (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic) p.before.machine = .ok converted final ∧
      Post p.before.machine resources.budget source.provenanceMap.ptrs.size final ∧
      RelocationByteFold.Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  classical
  by_cases uncached : ∃ row ∈ source.provenanceMap.ptrs,
      p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none
  · obtain ⟨converted,final,actual,invariant,attributes,keys,fragments⟩ := RelocationCurrentFold.convert s p input resources
      profile id source selected absent noFunction noVaList descriptor ordinary uncached layout hooks externStatic width pointerWidth
    obtain ⟨generation,tracker,memory,threads,runtime,context,_cache,_representation,world,_numeric,tags,_strict,race,_fits,_static⟩ := invariant
    exact ⟨converted,final,actual,⟨memory,threads,runtime,context,race,tracker,world,tags⟩,attributes,keys,fragments⟩
  · have sourceInput := RelocationInput.memory_source s p input id source selected absent noFunction noVaList descriptor
    have cached : ∀ row ∈ source.provenanceMap.ptrs, ∃ base,
        p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = some ⟨row.2.allocId,base⟩ := by
      intro row member
      cases prior : p.before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) with
      | none => exact False.elim (uncached ⟨row,member,prior⟩)
      | some entry =>
        have identifier : entry.allocId = row.2.allocId := by
          have test := Array.find?_some prior
          exact of_decide_eq_true test
        exact ⟨entry.address,by cases entry; simp_all⟩
    have initial : RelocationCachedFold.Invariant p.before.machine resources.budget 0 p.before.machine :=
      ⟨rfl,rfl,rfl,rfl,rfl,rfl,profile.noRace,input.tracker,input.world,by simpa using resources.tagRoom input.tracker input.world.enabled⟩
    obtain ⟨converted,final,actual,invariant,attributes,keys,fragments⟩ := RelocationCachedFold.convert p.before.machine source layout
      hooks externStatic resources.budget (RelocationRawBinder.count_resources s p resources id source sourceInput.physical descriptor)
      ordinary cached width pointerWidth sourceInput.physical.ordered sourceInput.physical.windows sourceInput.physical.fragments initial
    obtain ⟨memory,threads,_addresses,_tape,runtime,context,race,tracker,world,tags⟩ := invariant
    exact ⟨converted,final,actual,⟨memory,threads,runtime,context,race,tracker,world,tags⟩,attributes,keys,fragments⟩
end EmptyFunction.RelocationOrdinaryConversion
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationOrdinaryConversion.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary conversion axiom {dependency} in {name}"
