import duplicate_prefix.ConcreteEmptyCallTimeFactory
import duplicate_prefix.WildcardNonliveRootSafety
namespace DuplicatePrefix.ConcreteEmptyCandidateDispatch
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-- Exhaustive source-precedence cases at the SAME concrete ID and parent tag.
The known-nondata branch retains raw rows; lazy globals retain their raw image. -/
def Cases {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) (tag : BorTag) : Prop :=
  (∃ entry, memory.live.find? (fun row => row.1 == id) = some (id,entry) ∧ Parent entry.allocation.extra (some tag)) ∨
  (Metadata memory id (some tag) ∧ memory.live.find? (fun row => row.1 == id) = none) ∨
  Materializable context memory addresses id (some tag)

theorem target_cases {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) (tag : BorTag)
    (target : TargetMetadata context memory addresses id (some tag)) : Cases context memory addresses id tag := by
  rcases target with known | image
  · cases known with
    | live entry present parent => exact Or.inl ⟨entry,present,parent⟩
    | functionRow absent present => exact Or.inr (Or.inl ⟨.functionRow absent present,absent⟩)
    | vaListRow absent noFunction present => exact Or.inr (Or.inl ⟨.vaListRow absent noFunction present,absent⟩)
    | nondataGlobal descriptor absent noFunction noVaList present kind => exact Or.inr (Or.inl ⟨.nondataGlobal descriptor absent noFunction noVaList present kind,absent⟩)
    | dead entry absent noFunction noVaList noGlobal present => exact Or.inr (Or.inl ⟨.dead entry absent noFunction noVaList noGlobal present,absent⟩)
  · exact Or.inr (Or.inr image)

theorem from_candidate {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) (tag : BorTag) (address : UInt64)
    (candidate : Candidate context memory addresses (Pointer.new (some (.concrete id tag)) (Size.ofBytes address))) :
    address ≠ 0 ∧ ∃ base,
      addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      base+(address-base)=address ∧ Cases context memory addresses id tag := by
  obtain ⟨⟨base,cached⟩,target⟩ := candidate.2
  refine ⟨candidate.1,base,cached,?_,target_cases context memory addresses id tag target⟩
  rw [UInt64.add_comm,UInt64.sub_add_cancel]

theorem forget_parent {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (tag : BorTag) (metadata : Metadata memory id (some tag)) : Metadata memory id none := by
  cases metadata with
  | live entry present parent => exact .live entry present trivial
  | functionRow absent present => exact .functionRow absent present
  | vaListRow absent noFunction present => exact .vaListRow absent noFunction present
  | nondataGlobal descriptor absent noFunction noVaList present kind => exact .nondataGlobal descriptor absent noFunction noVaList present kind
  | dead entry absent noFunction noVaList noGlobal present => exact .dead entry absent noFunction noVaList noGlobal present

/-- Feed the existing actual nonlive all-count family with a lookup/kind fact
DERIVED from the concrete candidate's raw rows, not supplied as a success input. -/
theorem nondata_info {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (tag : BorTag) (metadata : Metadata memory id (some tag))
    (absent : memory.live.find? (fun row => row.1 == id) = none) :
    ∃ info, memory.getAllocInfo id = .ok info ∧ info.kind ≠ .liveData :=
  WildcardNonliveRootSafety.nondata_info memory id (forget_parent memory id tag metadata) absent

/-- A concrete lazy-global input tag is forced to the stored cached root; no
new parent tag is invented by the dispatcher. -/
theorem materializable_root {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : AllocAddresses.GlobalAddressState)
    (id : AllocId) (tag : BorTag) (image : Materializable context memory addresses id (some tag)) :
    ∃ source,
      memory.live.find? (fun row => row.1 == id) = none ∧ memory.hasFunctionPointer id = false ∧ memory.hasVaListId id = false ∧
      ImageDescriptor context memory id source ∧
      (context.rootTags.find? (fun row => row.1 == id)).map Prod.snd = some tag ∧
      context.extraAllocationIds.contains id = false ∧ context.nativeLibraryPathsEmpty = true ∧
      GlobalSupportedImage.Supported source context.runtime memory context.rootTags addresses.baseAddr := by
  obtain ⟨source,root,absent,noFunction,noVaList,descriptor,cached,incoming,extras,native,supported⟩ := image
  have same : tag=root := by
    rcases incoming with impossible | equal
    · cases impossible
    · exact Option.some.inj equal
  subst root
  exact ⟨source,absent,noFunction,noVaList,descriptor,cached,extras,native,supported⟩
end DuplicatePrefix.ConcreteEmptyCandidateDispatch
