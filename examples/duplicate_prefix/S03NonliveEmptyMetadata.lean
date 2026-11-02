import duplicate_prefix.DuplicatePrefixEmptyReferenceInput

namespace DuplicatePrefix.S03NonliveEmptyMetadata
open Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false

/-- Raw supported nonlive cases derive the actual metadata result. Absence
from the live map rules out the live constructor without fabricating backing
storage for the zero-byte argument. Function, vaList, nondata global and dead
rows retain the interpreter's lookup precedence. -/
theorem known {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (tag : Option BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata memory id tag)
    (absent : memory.live.find? (fun row => row.1 == id) = none) :
    ∃ info, memory.getAllocInfo id = .ok info ∧ info.kind ≠ .liveData := by
  cases metadata with
  | live entry present parent => rw [absent] at present; cases present
  | functionRow missing present =>
    exact ⟨_,by simp only [MemoryState.getAllocInfo,missing,present,↓reduceIte];rfl,by intro impossible;cases impossible⟩
  | vaListRow missing noFunction present =>
    unfold MemoryState.hasVaListId at present
    exact ⟨_,by simp only [MemoryState.getAllocInfo,missing,noFunction,present,
      Bool.false_eq_true,↓reduceIte];rfl,by intro impossible;cases impossible⟩
  | nondataGlobal descriptor missing noFunction noVaList present kind =>
    unfold MemoryState.hasVaListId at noVaList
    rcases kind with kind | kind | kind
    all_goals
      simp only [MemoryState.getAllocInfo,missing,noFunction,noVaList,present,
        Bool.false_eq_true,↓reduceIte,kind]
      exact ⟨_,rfl,by intro impossible;cases impossible⟩
  | dead entry missing noFunction noVaList noGlobal present =>
    unfold MemoryState.hasVaListId at noVaList
    exact ⟨_,by simp only [MemoryState.getAllocInfo,missing,noFunction,noVaList,noGlobal,present,
      Bool.false_eq_true,↓reduceIte];rfl,by intro impossible;cases impossible⟩

/-- A live return allocation is distinct from an absent nonlive argument. -/
theorem separate {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id liveId : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (absent : memory.live.find? (fun row => row.1 == id) = none)
    (present : memory.live.find? (fun row => row.1 == liveId) = some (liveId,entry)) :
    liveId ≠ id := by
  intro same
  rw [same,absent] at present
  cases present

theorem live_replace_absent {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id liveId : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (absent : memory.live.find? (fun row => row.1 == id) = none) (different : liveId ≠ id) :
    ((memory.live.filter fun row => row.1 != liveId).push (liveId,entry)).find?
      (fun row => row.1 == id) = none := by
  apply Array.find?_eq_none.mpr
  intro row member selected
  rcases Array.mem_push.mp member with old | equal
  · exact (Array.find?_eq_none.mp absent) row (Array.mem_filter.mp old).1 selected
  · subst row
    exact different (by simpa using selected)

/-- Changing the separate physical return allocation preserves every raw
supported nonlive supplier. This applies to protection tree updates and the
actual uninitializing store; no property of its data or borrow tree is needed. -/
theorem replace {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id liveId : AllocId) (tag : Option BorTag) (entry : LocalAllocation Provenance BorrowTree K)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata memory id tag)
    (absent : memory.live.find? (fun row => row.1 == id) = none) (different : liveId ≠ id) :
    DuplicatePrefixEmptyReferenceInput.Metadata
      {memory with live := (memory.live.filter fun row => row.1 != liveId).push (liveId,entry)} id tag := by
  have missing := live_replace_absent memory id liveId entry absent different
  cases metadata with
  | live entry present parent => rw [absent] at present; cases present
  | functionRow _ present => exact .functionRow missing present
  | vaListRow _ noFunction present => exact .vaListRow missing noFunction present
  | nondataGlobal descriptor _ noFunction noVaList present kind =>
    exact .nondataGlobal descriptor missing noFunction noVaList present kind
  | dead entry _ noFunction noVaList noGlobal present =>
    exact .dead entry missing noFunction noVaList noGlobal present

end DuplicatePrefix.S03NonliveEmptyMetadata
