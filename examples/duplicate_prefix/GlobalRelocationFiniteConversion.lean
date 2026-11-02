import duplicate_prefix.GlobalRelocationFiniteLoop
namespace DuplicatePrefix.GlobalRelocationSourceExtraction
open Lean Elab in
elab "source_sorted_keys" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".Miri.Memory.ProvenanceMap.sortedKeys" then some name else none
  let [name] := names | throwError "expected original provenance ordering helper"
  Lean.Meta.mkConstWithFreshMVarLevels name

end DuplicatePrefix.GlobalRelocationSourceExtraction

namespace DuplicatePrefix.GlobalRelocationFiniteConversion
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open GlobalRelocationFiniteLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem sorted (rows : List Row) (separate : rows.Pairwise Separate) :
    source_sorted_keys (rows.map output) = true := by
  induction rows with
  | nil =>
    simp only [List.map_nil]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    rfl
  | cons row rest ih =>
    cases rest with
    | nil =>
      simp only [List.map_cons,List.map_nil]
      unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
      rfl
    | cons next tail =>
      have ordered : row.position.bytes<next.position.bytes := by
        have bounded := (List.pairwise_cons.mp separate).1 next (by simp)
        change row.position.bytes.toNat<next.position.bytes.toNat
        unfold Separate at bounded
        omega
      have orderedTail := ih (List.pairwise_cons.mp separate).2
      simp only [List.map_cons]
      unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
      simpa only [List.map_cons,output,ordered,decide_true,Bool.true_and] using orderedTail

private theorem provenance_exists (rows : List Row) (separate : rows.Pairwise Separate) :
    ∃ provenance : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs (rows.map output).toArray = .ok provenance ∧
      provenance.ptrs = (rows.map output).toArray ∧ provenance.byteFragments = none := by
  have ordered := sorted rows separate
  simp only [ProvenanceMap.fromPresortedPtrs,ordered,ite_true]
  exact ⟨_,rfl,rfl,rfl⟩

private theorem finish {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance)) (before : State)
    (bytes : Array UInt8) (rows : List Row) (separate : rows.Pairwise Separate)
    (size : bytes.size = (AllocationCopy.snapshot source).size) :
    ∃ converted : Allocation Provenance Unit,
      GlobalRelocationActualStep.finish source layout (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before
        (none,bytes,before,(rows.map output).toArray) = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = (rows.map output).toArray ∧ converted.provenanceMap.byteFragments = none := by
  obtain ⟨provenance,conversion,ptrs,fragments⟩ := provenance_exists rows separate
  unfold GlobalRelocationActualStep.finish
  cases source
  rename_i raw allocationSize sourceProvenance mask align mutability extra native
  simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,pure,Pure.pure,Except.pure,Except.toOption] at size
  simp [conversion,pure,Pure.pure,bind,Bind.bind]
  refine ⟨_,rfl,?_,ptrs,fragments⟩
  exact ⟨rfl,size,rfl,rfl,rfl,rfl⟩

/-- Real allocation conversion for an arbitrary finite ordered, nonoverlapping
relocation list. Both endian decoding and all pointer callbacks are derived
from initial source representation and cached compiler metadata. -/
theorem convert {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout) (rows : List Row)
    (known : ∀ row ∈ rows, GlobalRelocationTwoWords.Known before.memory tracker before.user.addresses.baseAddr row)
    (enabled : before.borrowTracker = some tracker)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (separate : rows.Pairwise Separate)
    (windows : ∀ row ∈ rows, (AllocationCopy.snapshot source).extract row.position.bytes.toNat
      (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word)
    (bounds : ∀ row ∈ rows, row.position.bytes.toNat+8≤(AllocationCopy.snapshot source).size)
    (relocations : source.provenanceMap.ptrs = (rows.map input).toArray)
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer choices hooks externStatic) before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = (rows.map output).toArray ∧ converted.provenanceMap.byteFragments = none := by
  obtain ⟨bytes,size,loop⟩ := GlobalRelocationFiniteLoop.run choices hooks externStatic before tracker source layout rows
    known enabled arithmetic width separate windows bounds
  have loopArray : forIn (rows.map input).toArray (none,AllocationCopy.snapshot source,before,#[])
      (action source layout (PointerSource.globalRootPointer choices hooks externStatic) before) =
        (none,bytes,before,(rows.map output).toArray) := by
    rw [←Array.forIn_toList]
    simpa only [List.toList_toArray] using loop
  dsimp only [action] at loopArray
  obtain ⟨converted,finished,facts,ptrs,fragments⟩ := finish source layout
    (PointerSource.globalRootPointer choices hooks externStatic) before bytes rows separate size
  refine ⟨converted,?_,facts,ptrs,fragments⟩
  rw [GlobalRelocationActualStep.adjust_eq_loop source layout (PointerSource.globalRootPointer choices hooks externStatic) before noFragments,
    relocations,loopArray]
  exact finished
end DuplicatePrefix.GlobalRelocationFiniteConversion
