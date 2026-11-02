import empty_function.DispatcherSkeleton
import empty_function.NondataProtection
namespace EmptyFunction.MemoryPartition
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxHeartbeats 8000000

def Resident (p : Packet) (id : AllocId) : Prop :=
  (∃ entry, p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) ∨
  NondataProtection.Registry p.before id

theorem selected (s : Static) (p : Packet) (id : AllocId)
    (selection : ChoiceAdmission.SelectedId p id) (backing : Backing s p.before id) :
    Resident p id ∨ ∃ source, ChoiceAdmission.SelectedSource s p id source := by
  classical
  cases DispatcherSkeleton.registry s p id backing with
  | live entry present => exact Or.inl (Or.inl ⟨entry,present⟩)
  | function absent present => exact Or.inl (Or.inr (.function absent present))
  | vaList absent noFunction present => exact Or.inl (Or.inr (.vaList absent present))
  | dead absent noFunction noVa noGlobal entry present =>
    exact Or.inl (Or.inr (.dead absent noGlobal entry present))
  | global absent noFunction noVa entry present raw =>
    cases raw with
    | live old row => rw [absent] at row;cases row
    | extraFunction extra =>
      unfold MemoryState.hasFunctionPointer at noFunction
      unfold MemoryState.hasExtraFunctionId at extra
      simp [extra] at noFunction
    | vaList listed => rw [noVa] at listed;cases listed
    | dead dead row noLive noFun noV noG => rw [present] at noG;cases noG
    | global actual row identity content storage vacant =>
      have same : actual = entry := Option.some.inj (row.symm.trans present)
      subst actual
      cases content with
      | memory source kind payload size align mutability sourceInput =>
        apply Or.inr
        refine ⟨source,.memory selection absent noFunction noVa ?_⟩
        have entryEq : entry = ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩ := by cases entry; simp_all
        simpa only [entryEq] using present
      | internalStatic definition source kind payload initializer size align mutability sourceInput =>
        apply Or.inr
        refine ⟨source,.internalStatic definition selection absent noFunction noVa ?_ initializer⟩
        have entryEq : entry = ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩ := by cases entry; simp_all
        simpa only [entryEq] using present
      | externalStatic definition kind payload =>
        have impossible := storage definition true false true payload
        simp at impossible
      | threadLocalStatic definition foreign kind payload =>
        have impossible := storage definition true true foreign payload
        simp at impossible
      | function kind => exact Or.inl (Or.inr (.global absent entry present (by simp [kind]) (by simp [kind])))
      | vtable kind => exact Or.inl (Or.inr (.global absent entry present (by simp [kind]) (by simp [kind])))
      | typeId kind => exact Or.inl (Or.inr (.global absent entry present (by simp [kind]) (by simp [kind])))
end EmptyFunction.MemoryPartition
