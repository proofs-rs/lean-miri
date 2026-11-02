import empty_function.RelocationOrdered
import empty_function.RelocationReservedStep
import empty_function.RelocationByteFold
namespace EmptyFunction.RelocationReservedFold
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
abbrev Row := Size × CtfeProvenance

def demands (source : Allocation CtfeProvenance Unit) (index : Nat) : List (Option AllocId) :=
  (source.provenanceMap.ptrs.toList.drop index).map (fun row => some row.2.allocId)

/-- This branch classifies actual raw target descriptors, not future callbacks.
Other target kinds remain separate cases of the whole source domain. -/
def Target (snapshot : WholeCall.State) (maximumSize maximumAlignment : Nat) (row : Row) : Prop :=
  ∃ source : Allocation CtfeProvenance Unit, ∃ info : AllocationInfo,
    snapshot.machine.memory.findGlobal? row.2.allocId = some
      ⟨row.2.allocId,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩ ∧
    snapshot.machine.memory.getAllocInfo row.2.allocId = .ok info ∧
    info.kind ≠ .dead ∧ info.kind ≠ .typeId ∧ snapshot.machine.memory.isAllocLive row.2.allocId = true ∧
    (snapshot.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) = none →
      InputDraft.AlignmentRepresentation info.align) ∧ info.size.bytes.toNat ≤ maximumSize ∧
    2^info.align.pow2 ≤ maximumAlignment

def Invariant (snapshot : WholeCall.State) (source : Allocation CtfeProvenance Unit)
    (reserved : BorTag) (budget maximumSize maximumAlignment index : Nat) (current : ChoiceExecution.S) : Prop :=
  ∃ generation tracker,
    current.memory = snapshot.machine.memory ∧ current.threads = snapshot.machine.threads ∧
    current.user.payload.payload.user.runtime = snapshot.machine.user.payload.payload.user.runtime ∧
    RelocationContext.view current.user.payload = RelocationContext.view snapshot.machine.user.payload ∧
    (∀ oldId old, snapshot.machine.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old →
      current.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old) ∧
    InputDraft.GenerationRepresentation {snapshot with machine := current} generation ∧
    TreeRuntimeInput.World current tracker ∧
    InputDraft.GenerationResources generation (budget-index) maximumSize maximumAlignment ∧
    tracker.global.nextPointerTag.value.toNat+(budget-index) < 2^64 ∧
    (ChoiceExecution.tapeAccess.get current).policy = .strict ∧ current.dataRace = none ∧
    Fits (SourceChoicePlan.ordered snapshot (demands source index) current.user.addresses)
      (ChoiceExecution.tapeAccess.get current) ∧ RootReservedPost.Fence tracker.global reserved ∧
      (∀ initialTracker, snapshot.machine.borrowTracker = some initialTracker → RootFramePost.Frame initialTracker.global tracker.global) ∧
      AddressStaticPost.view current.user.addresses = AddressStaticPost.view snapshot.machine.user.addresses

/-- Arbitrary finite ordinary-memory targets, including duplicates, share one
actual byte conversion and machine-state induction. Every legal supplied
response is retained. The branch is explicit; it does not redefine ValidInput. -/
theorem convert (snapshot : WholeCall.State) (source : Allocation CtfeProvenance Unit)
    (layout : TargetDataLayout) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (reserved : BorTag) (budget maximumSize maximumAlignment : Nat)
    (count : source.provenanceMap.ptrs.size ≤ budget)
    (targets : ∀ row ∈ source.provenanceMap.ptrs, Target snapshot maximumSize maximumAlignment row)
    (width : layout.pointerWidth = .w64) (pointerWidth : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (separate : source.provenanceMap.ptrs.toList.Pairwise RelocationByteFold.Separate)
    (bounds : ∀ row ∈ source.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ source.len)
    (fragments : source.provenanceMap.byteFragments = none)
    (initial : Invariant snapshot source reserved budget maximumSize maximumAlignment 0 snapshot.machine) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (RelocationBytePrimitives.snapshot source) state)
        (PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic) snapshot.machine = .ok converted final ∧
      Invariant snapshot source reserved budget maximumSize maximumAlignment source.provenanceMap.ptrs.size final ∧
      RelocationByteFold.Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  apply RelocationByteFold.convert source layout _ (Invariant snapshot source reserved budget maximumSize maximumAlignment)
    snapshot.machine width separate bounds fragments initial
  intro index valid current good
  obtain ⟨generation,tracker,memory,threads,runtime,context,cacheStable,representation,world,numeric,tagRoom,strict,noRace,fitted,fence,frame,static⟩ := good
  let row := source.provenanceMap.ptrs[index]
  obtain ⟨target,info,descriptor,metadata,notDead,notType,live,alignment,sizeBound,alignBound⟩ :=
    targets row (Array.getElem_mem valid)
  have one : 1 ≤ budget-index := by omega
  have suffix : demands source index = some row.2.allocId :: demands source (index+1) := by
    unfold demands
    rw [List.drop_eq_getElem_cons (by simpa using valid)]
    simp only [List.map_cons,Array.getElem_toList,row]
  rw [suffix] at fitted
  have peeled := RelocationOrdered.head snapshot current row.2.allocId (demands source (index+1)) info metadata
    notDead notType live (congrArg (fun t => t.activeThread) threads) fitted
  obtain ⟨pointer,final,next,nextTracker,actual,memPost,threadPost,tail,strictPost,repPost,worldPost,tags,numbers,race,runtimePost,contextPost,bases,fencePost,framePost,staticPost⟩ :=
    RelocationReservedStep.step {snapshot with machine := current} generation representation hooks externStatic tracker reserved fence
      row.2 (RelocationBytePrimitives.word layout (RelocationBytePrimitives.snapshot source) row.1.bytes.toNat)
      target info (budget-index) maximumSize maximumAlignment (SourceChoicePlan.ordered snapshot (demands source (index+1)))
      world numeric one tagRoom (by simpa only [memory] using descriptor) (by simpa only [memory] using metadata)
      notDead notType (by simpa only [memory] using live) noRace (by
        intro missing
        apply alignment
        cases old : snapshot.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.2.allocId) with
        | none => rfl
        | some previous => have retained := cacheStable row.2.allocId previous old; rw [missing] at retained; cases retained) sizeBound alignBound pointerWidth strict peeled
  refine ⟨pointer,final,actual,next,nextTracker,memPost.trans memory,threadPost.trans threads,runtimePost.trans runtime,contextPost.trans context,(by intro oldId old prior; exact bases oldId old (cacheStable oldId old prior)),repPost,worldPost,?_,?_,strictPost,race,tail,fencePost,(by intro initial enabled; exact RootFramePost.trans _ _ _ (frame initial enabled) framePost),staticPost.trans static⟩
  · simpa only [Nat.sub_sub] using numbers
  · simpa only [Nat.sub_sub] using tags
end EmptyFunction.RelocationReservedFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationReservedFold.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation memory fold axiom {dependency} in {name}"
