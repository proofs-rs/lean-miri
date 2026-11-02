import duplicate_prefix.DuplicatePrefixEmptyReferenceInput
namespace DuplicatePrefix.WildcardEmptyTargetClassification
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Memory.AllocAddresses
open DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
/-- Exhaustive STORED target metadata alternatives for the S01 wildcard
candidate. This is a data case split, not a definition of validity or safety. -/
def Cases {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId) : Prop :=
  (∃ entry, memory.live.find? (fun row => row.1 == id) = some (id,entry)) ∨
  (Metadata memory id none ∧ memory.live.find? (fun row => row.1 == id) = none) ∨
  Materializable context memory addresses id none

theorem metadata_cases {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId)
    (target : TargetMetadata context memory addresses id none) : Cases context memory addresses id := by
  rcases target with known | image
  · cases known with
    | live entry present parent => exact Or.inl ⟨entry,present⟩
    | functionRow absent present => exact Or.inr (Or.inl ⟨.functionRow absent present,absent⟩)
    | vaListRow absent noFunction present => exact Or.inr (Or.inl ⟨.vaListRow absent noFunction present,absent⟩)
    | nondataGlobal descriptor absent noFunction noVaList present kind =>
      exact Or.inr (Or.inl ⟨.nondataGlobal descriptor absent noFunction noVaList present kind,absent⟩)
    | dead entry absent noFunction noVaList noGlobal present =>
      exact Or.inr (Or.inl ⟨.dead entry absent noFunction noVaList noGlobal present,absent⟩)
  · exact Or.inr (Or.inr image)

/-- No target family is chosen by the caller: the existing candidate's stored
exposed-target obligation yields the complete live/nondata/lazy-image split.
The nondata branch is the input consumed by WildcardNonliveRootSafety.invoke. -/
theorem exact_target_cases {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (base : UInt64) (id : AllocId) (position : Nat)
    (input : Candidate context memory addresses (Pointer.new (some .wildcard) (Size.ofBytes base)))
    (inverse : addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (exposed : addresses.exposed.contains id = true) : Cases context memory addresses id := by
  exact metadata_cases context memory addresses id
    (input.2.targets ⟨base,id⟩ (Array.mem_of_getElem? inverse) exposed)
end DuplicatePrefix.WildcardEmptyTargetClassification
