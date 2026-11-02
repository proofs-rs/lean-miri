import duplicate_prefix.S03NonliveEmptyMetadata

namespace DuplicatePrefix.S03NonliveMetadataTag
open Miri.Memory Miri.TreeBorrows
set_option autoImplicit false

/-- Nonlive metadata suppliers do not inspect a borrow-tree parent. Their
raw evidence can follow the actual retagged pointer without inventing a node. -/
theorem changeTag {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (source target : Option BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata memory id source)
    (absent : memory.live.find? (fun row => row.1 == id) = none) :
    DuplicatePrefixEmptyReferenceInput.Metadata memory id target := by
  cases metadata with
  | live entry present parent => rw [absent] at present;cases present
  | functionRow absent present => exact .functionRow absent present
  | vaListRow absent noFunction present => exact .vaListRow absent noFunction present
  | nondataGlobal descriptor absent noFunction noVaList present kind =>
    exact .nondataGlobal descriptor absent noFunction noVaList present kind
  | dead entry absent noFunction noVaList noGlobal present =>
    exact .dead entry absent noFunction noVaList noGlobal present

end DuplicatePrefix.S03NonliveMetadataTag
