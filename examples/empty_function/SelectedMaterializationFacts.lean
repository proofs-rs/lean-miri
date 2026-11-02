import empty_function.StaticSourceInput
import empty_function.CanonicalDictionaries
namespace EmptyFunction.SelectedMaterializationFacts
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

private theorem memory_vacant (s : Static) (p : Packet)
    (input : InputDraft.CurrentInputDraft s p) (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    p.before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by
  have backing := RelocationInput.selected_backing s p input id selected
  cases backing with
  | live entry row => rw [absent] at row;cases row
  | global entry query _ _ _ vacant =>
    have same := Option.some.inj (query.symm.trans descriptor)
    cases same
    exact vacant absent (Or.inl rfl)
  | extraFunction row =>
    unfold MemoryState.hasExtraFunctionId at row
    have impossible : p.before.machine.memory.hasFunctionPointer id = true := by
      simp only [MemoryState.hasFunctionPointer,row,Bool.true_or]
    rw [noFunction] at impossible
    cases impossible
  | vaList row => rw [noVaList] at row;cases row
  | dead _ _ _ _ _ noGlobal => rw [descriptor] at noGlobal;cases noGlobal

/-- The actual selected source carries its compiler relocation format and
its currently vacant extras row. These are current-data facts, not resource
headroom or operational-success assumptions. -/
theorem facts (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id source) :
    InputDraft.RelocationInput s p.before source ∧
    p.before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by
  cases selected with
  | memory chosen absent noFunction noVa descriptor =>
    exact ⟨RelocationInput.memory_source s p input id source chosen absent noFunction noVa descriptor,
      memory_vacant s p input id source chosen absent noFunction noVa descriptor⟩
  | internalStatic definition chosen absent noFunction noVa descriptor initializer =>
    exact StaticSourceInput.facts s p input id definition source chosen absent noFunction noVa descriptor initializer

theorem tables (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id source) : InputDraft.AddressTables p.before := by
  cases selected with
  | memory chosen _ _ _ _ => exact StaticSourceInput.tables s p input id chosen
  | internalStatic _ chosen _ _ _ _ _ => exact StaticSourceInput.tables s p input id chosen

theorem absent (s : Static) (p : Packet) (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id source) :
    p.before.machine.memory.live.find? (fun row => row.1 == id) = none := by
  cases selected with
  | memory _ absent _ _ _ => exact absent
  | internalStatic _ _ absent _ _ _ _ => exact absent
end EmptyFunction.SelectedMaterializationFacts
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.SelectedMaterializationFacts.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved selected-materialization axiom {dependency} in {name}"
