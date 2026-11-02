import duplicate_prefix.GeneralBorrowSharedGeneratorWrite
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GenericAsMutPtrEntryValidity
namespace DuplicatePrefix.GeneralBorrowGeneratedEntryData
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadParentRead DuplicatePrefix.GeneralBorrowGcAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual root Read and append retain allocator and live-node tag coherence. -/
theorem child_invariant (input : Input) (location : LocationTree) (good : State input location)
    (initial : Invariant input.tree) : Invariant (child input {}).tree := by
  obtain ⟨forest⟩ := good.forest
  have readFacts := GeneralBorrowSharedProfileParentRead.read_closed input location good.offset good.length
    good.locations good.roots good.parentless forest good.profile
  let prepared := afterReadInput input location {} good.offset good.length
  have preparedGood : Invariant prepared.tree :=
    ⟨initial.pool,initial.accounting,initial.unique,initial.nodeTags⟩
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput,good.offset,good.length]
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
  owned := (GeneralBorrowSharedGeneratorWrite.state_owned input location good).2

theorem iterate (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location) (initial : Invariant input.tree)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size + tags.length ≤ 4294967295) :
    ∃ final finalLocation, GeneralBorrowSharedGeneratorRepeat.Run input tags final ∧ State final finalLocation ∧ Invariant final.tree := by
  induction tags generalizing input location with
  | nil => exact ⟨input,location,.nil input,good,initial⟩
  | cons tag rest ih =>
    have tagFresh := fresh tag (by simp)
    have tagDifferent : input.newTag ≠ tag := fun same => current (by simp [same])
    have stepRoom : input.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      omega
    obtain ⟨readDone,childDone,next,nextLocation,tree,parent,newTag,nextGood,mappingEq⟩ :=
      GeneralBorrowSharedGeneratorStep.step input location good tag stepRoom tagFresh tagDifferent
    have nextFresh : ∀ future ∈ rest, GeneralBorrowTagMap.Fresh next.tree.tagMapping future := by
      intro future member
      have oldFresh := fresh future (by simp [member])
      have different : input.newTag ≠ future := fun same => current (by simp [same,member])
      have preserved := GeneralBorrowFreshMetadataChildAllocator.append_fresh input future oldFresh different
      rw [(GeneralBorrowFreshMetadataChildShared.append input).mapping] at preserved
      rw [mappingEq]
      exact preserved
    have nextCurrent : next.newTag ∉ rest := by rw [newTag];exact (List.nodup_cons.mp distinct).1
    have size : next.tree.tagMapping.mapping.size = input.tree.tagMapping.mapping.size+1 := by
      rw [mappingEq]
      simp only [mapping,Array.size_push]
    have nextRoom : next.tree.tagMapping.mapping.size+rest.length ≤ 4294967295 := by
      rw [size]
      simp only [List.length_cons] at room
      omega
    have nextInvariant : Invariant next.tree := by
      rw [tree]
      exact child_invariant input location good initial
    obtain ⟨final,finalLocation,history,finalGood,finalInvariant⟩ := ih next nextLocation nextGood nextInvariant nextFresh
      (List.nodup_cons.mp distinct).2 nextCurrent nextRoom
    exact ⟨final,finalLocation,.cons readDone childDone tree parent newTag history,finalGood,finalInvariant⟩
/-- Form concrete call-entry graph, allocator and Write-ownership data from
actual allocation and every finite shared-generation prefix. This is not yet a
whole-machine invocation: memory, runtime and compiler metadata remain separate. -/
theorem generate (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (room : 1+tags.length ≤ 4294967295) :
    let seed := GeneralBorrowSharedGeneratorSeed.input rootTag childTag different
    ∃ final finalLocation, GeneralBorrowSharedGeneratorRepeat.Run seed tags final ∧
      State final finalLocation ∧ Invariant final.tree ∧
      Nonempty (GenericAsMutPtrEntryValidity.Data final.tree {} final.parentTag final.newTag final.offset final.len) := by
  let seed := GeneralBorrowSharedGeneratorSeed.input rootTag childTag different
  have fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag member row present
    change row ∈ (GeneralBorrowSharedGeneratorSeed.tree rootTag).tagMapping.mapping at present
    rw [GeneralBorrowSharedGeneratorSeed.tree_eq] at present
    have same := Array.mem_singleton.mp present
    subst row
    intro equal
    have sameTag : rootTag = tag := equal
    exact rootUnused (sameTag.symm ▸ member)
  have capacity : seed.tree.tagMapping.mapping.size+tags.length ≤ 4294967295 := by
    change (GeneralBorrowSharedGeneratorSeed.tree rootTag).tagMapping.mapping.size+tags.length ≤ 4294967295
    rw [GeneralBorrowSharedGeneratorSeed.tree_eq]
    exact room
  have initial : Invariant seed.tree := GeneralBorrowGcAllocator.initial rootTag (Size.ofBytes 1)
  obtain ⟨final,location,history,good,coherent⟩ := iterate tags seed GeneralBorrowSharedGeneratorSeed.location
    (GeneralBorrowSharedGeneratorSeed.state rootTag childTag different) initial fresh unique childUnused capacity
  exact ⟨final,location,history,good,coherent,⟨data final location good coherent⟩⟩
end DuplicatePrefix.GeneralBorrowGeneratedEntryData
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGeneratedEntryData.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated entry data dependency {dependency}"
