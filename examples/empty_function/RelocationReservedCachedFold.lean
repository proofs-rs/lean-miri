import empty_function.RelocationRoot
import empty_function.RootTagPost
import empty_function.RootReservedPost
import empty_function.RootFramePost
import empty_function.RelocationNumeric
import empty_function.RelocationByteFold
namespace EmptyFunction.RelocationReservedCachedFold
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def Invariant (snapshot : ChoiceExecution.S) (reserved : BorTag) (budget index : Nat) (current : ChoiceExecution.S) : Prop :=
  current.memory = snapshot.memory ∧ current.threads = snapshot.threads ∧
  current.user.addresses = snapshot.user.addresses ∧
  ChoiceExecution.tapeAccess.get current = ChoiceExecution.tapeAccess.get snapshot ∧
  current.user.payload.payload.user.runtime = snapshot.user.payload.payload.user.runtime ∧
  RelocationContext.view current.user.payload = RelocationContext.view snapshot.user.payload ∧
  current.dataRace = none ∧
  ∃ tracker, TreeRuntimeInput.World current tracker ∧
    tracker.global.nextPointerTag.value.toNat+(budget-index) < 2^64 ∧ RootReservedPost.Fence tracker.global reserved ∧
      (∀ initialTracker, snapshot.borrowTracker = some initialTracker → RootFramePost.Frame initialTracker.global tracker.global)

/-- Entirely cached relocation lists need no generator representation or
random-choice supply, including a current state whose generator is absent. -/
theorem convert (snapshot : ChoiceExecution.S) (source : Allocation CtfeProvenance Unit)
    (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (reserved : BorTag) (budget : Nat) (count : source.provenanceMap.ptrs.size ≤ budget)
    (targets : ∀ row ∈ source.provenanceMap.ptrs, ∃ target : Allocation CtfeProvenance Unit,
      snapshot.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩)
    (cached : ∀ row ∈ source.provenanceMap.ptrs, ∃ base,
      snapshot.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) =
        some ⟨row.2.allocId,base⟩)
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (separate : source.provenanceMap.ptrs.toList.Pairwise RelocationByteFold.Separate)
    (bounds : ∀ row ∈ source.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ source.len)
    (fragments : source.provenanceMap.byteFragments = none)
    (initial : Invariant snapshot reserved budget 0 snapshot) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic) snapshot = .ok converted final ∧
      Invariant snapshot reserved budget source.provenanceMap.ptrs.size final ∧
      RelocationByteFold.Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  apply RelocationByteFold.convert source layout _ (Invariant snapshot reserved budget) snapshot width separate bounds fragments initial
  intro index valid current good
  obtain ⟨memory,threads,addresses,tape,runtime,context,noRace,tracker,world,tagRoom,fence,frame⟩ := good
  let row := source.provenanceMap.ptrs[index]
  have member : row ∈ source.provenanceMap.ptrs := Array.getElem_mem valid
  obtain ⟨target,descriptor⟩ := targets row member
  obtain ⟨base,oldCache⟩ := cached row member
  have one : 1 ≤ budget-index := by omega
  have tagOne : tracker.global.nextPointerTag.value.toNat+1 < 2^64 := by omega
  obtain ⟨tag,final,actual,memPost,threadPost,addressPost,tapePost,global,tagged,enabled,race,runtimePost,contextPost⟩ :=
    RelocationRoot.memory_cached current hooks externStatic tracker row.2
      (RelocationBytePrimitives.word layout (RelocationBytePrimitives.snapshot source) row.1.bytes.toNat)
      base target (by simpa only [memory] using descriptor) world.enabled tagOne
      (by simpa only [addresses] using oldCache) pointerWidth
  have worldPost := RootTagPost.world current final tracker global row.2.allocId tag world memPost enabled tagged
  have rootPost := RootTagPost.root tracker.global row.2.allocId global tag tagged
  have tags := RelocationNumeric.tag_remaining _ _ (budget-index) one tagRoom rootPost.2.2.2.2.2.1
  have fencePost := (RootReservedPost.root tracker.global global row.2.allocId tag reserved fence tagged).1
  refine ⟨_,final,actual,memPost.trans memory,threadPost.trans threads,addressPost.trans addresses,
    tapePost.trans tape,runtimePost.trans runtime,contextPost.trans context,race.trans noRace,{tracker with global},worldPost,?_,fencePost,(by intro initial enabled; exact RootFramePost.trans _ _ _ (frame initial enabled) (RootFramePost.root tracker.global global row.2.allocId tag tagged))⟩
  simpa only [Nat.sub_sub] using tags
end EmptyFunction.RelocationReservedCachedFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationReservedCachedFold.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation cached fold axiom {dependency} in {name}"
