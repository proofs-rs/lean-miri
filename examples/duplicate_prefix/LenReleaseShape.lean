import duplicate_prefix.LenReturn
import duplicate_prefix.ProtectedStages
import duplicate_prefix.EmptyBorrowHelpers
namespace DuplicatePrefix.LenReleaseShape
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures
open BorrowRangeAccess NestedBorrowAccess NestedConstruction
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

inductive Shape (protections : ProtectedTags) (rows : Array (AllocId × BorTag))
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) : Type where
  | positive (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
      (capacity offset finish : UInt64) (released : Bool)
      (owned : rows = #[(id,tags 3)])
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 released)))
      (mask : ProtectedStages.StageMask tags protections 4 true) : Shape protections rows memory
  | liveZero (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (tags : Fin 6 → BorTag) (distinct : Function.Injective tags) (capacity : UInt64)
      (owned : rows = #[(id,tags 3)])
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (tree : entry.allocation.extra = tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)) : Shape protections rows memory
  | nonlive (id : AllocId) (tag : BorTag) (info : AllocationInfo)
      (owned : rows = #[(id,tag)])
      (lookup : memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData) : Shape protections rows memory
  | noRows (empty : rows = #[]) : Shape protections rows memory

def resultMemory {protections : ProtectedTags} {rows : Array (AllocId × BorTag)}
    {memory : MemoryState Provenance BorrowTree MiriMemoryKind} (shape : Shape protections rows memory) :
    MemoryState Provenance BorrowTree MiriMemoryKind := match shape with
  | .positive id entry tags _ capacity offset finish _ _ _ _ _ =>
      StackPopRelease.commitTree memory id entry (tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 true)))
  | .liveZero id entry _ _ _ _ _ _ => StackPopRelease.commitTree memory id entry entry.allocation.extra
  | .nonlive .. => memory
  | .noRows .. => memory

theorem plan {protections : ProtectedTags} {rows : Array (AllocId × BorTag)}
    {memory : MemoryState Provenance BorrowTree MiriMemoryKind} (shape : Shape protections rows memory) :
    StackPopRelease.Plan protections rows.toList memory (resultMemory shape) := by
  cases shape with
  | positive id entry tags distinct capacity offset finish released owned present tree mask =>
    dsimp only [resultMemory]
    rw [owned]
    apply StackPopRelease.Plan.live id (tags 3) entry _ [] memory _ present
    · rw [tree]
      exact ProtectedStages.len_helper_release tags distinct protections mask capacity offset finish released
    · exact .nil _
  | liveZero id entry tags distinct capacity owned present tree =>
    dsimp only [resultMemory]
    rw [owned]
    apply StackPopRelease.Plan.live id (tags 3) entry entry.allocation.extra [] memory _ present
    · rw [tree]
      exact EmptyBorrowHelpers.len_release_zero tags distinct capacity protections
    · exact .nil _
  | nonlive id tag info owned lookup notLive =>
    dsimp only [resultMemory]
    rw [owned]
    exact StackPopRelease.plan_single_nonlive protections memory id tag info lookup notLive
  | noRows empty =>
    dsimp only [resultMemory]
    rw [empty]
    exact .nil memory

def transport {protections : ProtectedTags} {rows : Array (AllocId × BorTag)}
    {oldMemory newMemory : MemoryState Provenance BorrowTree MiriMemoryKind}
    (same : newMemory = oldMemory) (shape : Shape protections rows oldMemory) : Shape protections rows newMemory :=
  same.symm ▸ shape

theorem transport_result {protections : ProtectedTags} {rows : Array (AllocId × BorTag)}
    {oldMemory newMemory : MemoryState Provenance BorrowTree MiriMemoryKind}
    (same : newMemory = oldMemory) (shape : Shape protections rows oldMemory) :
    resultMemory (transport same shape) = resultMemory shape := by
  cases same
  rfl

end
end DuplicatePrefix.LenReleaseShape
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenReleaseShape.plan, ``DuplicatePrefix.LenReleaseShape.transport_result] do
   for dependency in (← collectAxioms name) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved structural len release proof dependency {dependency}"
