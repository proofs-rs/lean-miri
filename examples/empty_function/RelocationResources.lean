import empty_function.RelocationEntry
namespace EmptyFunction.RelocationResources
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

private theorem keyed_mem {K V : Type} [BEq K] [Hashable K] {keyFn : V → K}
    (table : KeyedArray K V keyFn) (key : K) (value : V)
    (query : table.find? key = some value) : value ∈ table.toArray := by
  unfold KeyedArray.find? at query
  simp only [bind,Option.bind] at query
  split at query <;> try contradiction
  dsimp only at query
  split at query <;> try contradiction
  exact Array.mem_of_getElem? query

/-- Certified current descriptor lookup implies membership of the resource
array. No layout/storage/address operation is run or assumed to succeed. -/
theorem global_mem (before : WholeCall.State) (id : AllocId) (global : GlobalAllocation)
    (query : before.machine.memory.findGlobal? id = some global) :
    global ∈ before.machine.memory.globals := by
  unfold MemoryState.findGlobal? at query
  exact keyed_mem _ _ _ query

/-- Target memory's current metadata is supplied by local backing, function/
va-list precedence, or its compiler descriptor. Every case has existing bounds. -/
theorem memory_info_bounds (s : WholeCall.Static) (p : WholeCall.Packet)
    (resources : Specification.ResourceMargins s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (info : AllocationInfo)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
    (metadata : p.before.machine.memory.getAllocInfo id = .ok info) :
    info.kind ≠ .dead ∧ info.kind ≠ .typeId ∧
      info.size.bytes.toNat ≤ resources.maximumSize ∧ 2^info.align.pow2 ≤ resources.maximumAlignment := by
  have registered := global_mem p.before id _ descriptor
  have alignBound := resources.globalAlignments _ registered
  have alignPositive : 1 ≤ resources.maximumAlignment := by
    have positive : 0 < (2:Nat)^source.align.pow2 := Nat.pow_pos (by decide)
    change 2^source.align.pow2 ≤ resources.maximumAlignment at alignBound
    omega
  unfold MemoryState.getAllocInfo at metadata
  cases located : p.before.machine.memory.live.find? (fun row => row.1 == id) with
  | some row =>
    simp only [located,pure,Except.pure] at metadata
    cases metadata
    refine ⟨by simp,by simp,?_,?_⟩
    · exact resources.liveByteSizes row (Array.mem_of_find?_eq_some located)
    · exact resources.liveAlignments row (Array.mem_of_find?_eq_some located)
  | none =>
    simp only [located] at metadata
    by_cases function : p.before.machine.memory.hasFunctionPointer id = true
    · simp only [function,↓reduceIte,pure,Except.pure] at metadata
      cases metadata
      exact ⟨by simp,by simp,Nat.zero_le _,alignPositive⟩
    · simp only [function] at metadata
      by_cases va : p.before.machine.memory.hasVaListId id = true
      · unfold MemoryState.hasVaListId at va
        simp only [va,↓reduceIte,pure,Except.pure] at metadata
        cases metadata
        exact ⟨by simp,by simp,Nat.zero_le _,alignPositive⟩
      · unfold MemoryState.hasVaListId at va
        simp only [va,descriptor,pure,Except.pure] at metadata
        cases metadata
        exact ⟨by simp,by simp,resources.globalSizes _ registered,alignBound⟩
end EmptyFunction.RelocationResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationResources.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation resource axiom {dependency} in {name}"
