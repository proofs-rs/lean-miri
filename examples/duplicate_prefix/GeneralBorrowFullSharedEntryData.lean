import duplicate_prefix.GeneralBorrowFullSharedWrite
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GenericAsMutPtrEntryValidity
namespace DuplicatePrefix.GeneralBorrowFullSharedEntryData
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowFullSharedRead DuplicatePrefix.GeneralBorrowGcAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual root Read and append retain allocator and live-node tag coherence. -/
theorem child_invariant (input : Input) (location : LocationTree) (good : State input location)
    (initial : Invariant input.tree) : Invariant (child input {}).tree := by
  obtain ⟨forest⟩ := good.forest
  have readFacts := GeneralBorrowFullSharedRead.read_closed input location good.offset
    good.locations good.roots good.parentless forest good.profile
  let prepared := afterReadInput input location {} good.offset
  have preparedGood : Invariant prepared.tree :=
    ⟨initial.pool,initial.accounting,initial.unique,initial.nodeTags⟩
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput,good.offset]
  rw [actualChild]
  exact GeneralBorrowSharedAllocatorInvariant.Append.preserves prepared preparedGood

/-- Sparse vacant slots have no stale stored permissions anywhere in the
actual generated allocation, as required by the pooled invocation contract. -/
theorem vacant_clean (input : Input) (location : LocationTree) (good : State input location)
    (query : UniIndex) (vacant : input.tree.nodes.get query = none) :
    GeneralBorrowFreshFutureClean.Clean input.tree query := by
  unfold GeneralBorrowFreshFutureClean.Clean GeneralRangeMapState.Every
  rw [good.locations]
  intro position valid
  have zero : position = 0 := by
    change position < 1 at valid
    omega
  subst position
  exact good.profile.vacant query vacant

/-- Construct call-entry data from generated state and allocator coherence.
The allocator condition is discharged by the history formation theorem below. -/
def data (input : Input) (location : LocationTree) (good : State input location)
    (initial : Invariant input.tree) :
    GenericAsMutPtrEntryValidity.Data input.tree {} input.parentTag input.newTag input.offset input.len where
  parent := input.parent
  root := input.parent
  node := input.parentNode
  depth := input.depth
  children := input.children
  parentPresent := input.parentPresent
  roots := good.roots
  covered := input.covered
  tagPresent := input.parentTagPresent
  tagFresh := input.fresh
  protectorFresh := by
    intro row member same
    have present := (GeneralBorrowFreshReuseProtection.entries_get input.tree.nodes row.1 row.2).mp
      (Array.mem_toList_iff.mpr member)
    have lookup := initial.nodeTags row.1 row.2 present
    have absent : input.tree.tagMapping.get input.newTag = none := by
      unfold UniKeyMap.get
      rw [GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh]
      rfl
    rw [same,absent] at lookup
    cases lookup
  nodeFits := by have aligned := input.aligned;have fits := input.fits;omega
  slot := .append input.noFree input.aligned input.fits
  well := input.well
  owned := (GeneralBorrowFullSharedWrite.state_owned input location good).2

end DuplicatePrefix.GeneralBorrowFullSharedEntryData
