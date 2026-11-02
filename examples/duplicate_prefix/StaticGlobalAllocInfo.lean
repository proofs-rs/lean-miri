import duplicate_prefix.GlobalDataOnlyMaterialize

namespace DuplicatePrefix.StaticGlobalAllocInfo
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
/-- The source classifies a declared STATIC as live data before attempting its
initializer. This classification alone does not imply initializer success. -/
theorem alloc_info {K U : Type} (before : MachineHooks.MachineState K U)
    (id : AllocId) (source : Allocation CtfeProvenance Unit) (definition : Nat)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false)
    (noVaList : before.memory.hasVaListId id = false)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩) :
    before.memory.getAllocInfo id = .ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩ := by
  unfold MemoryState.hasVaListId at noVaList
  simp [MemoryState.getAllocInfo,absent,noFunction,noVaList,descriptor,pure,Pure.pure,Except.pure]
end DuplicatePrefix.StaticGlobalAllocInfo
