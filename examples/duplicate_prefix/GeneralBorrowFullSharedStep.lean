import duplicate_prefix.GeneralBorrowFullSharedRead
import duplicate_prefix.GeneralBorrowFullSharedAppend
import duplicate_prefix.GeneralBorrowFullSharedNext
namespace DuplicatePrefix.GeneralBorrowFullSharedStep
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.GeneralBorrowFullSharedRead DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

set_option autoImplicit false in
/-- Explicit full-slice single-root generator invariant. Formation from arbitrary
Rust histories, arbitrary geometry, exposure protocols and free pools is separate. -/
structure State (input : Input) (location : LocationTree) : Prop where
  offset : input.offset = 0
  locations : input.tree.locations = homogeneous input.len location
  roots : input.tree.roots = #[input.parent]
  parentless : input.parentNode.parent = none
  forest : Nonempty (GeneralBorrowForest.Forest (source_normal_projection input.tree location {}).topology)
  profile : Profile input.tree location input.parent

/-- Derive a completed real ranged Read and shared constructor, then form the
same-parent next Input and its full invariant on the actual constructor tree.
Only initial state, next-tag freshness and numerical capacity are supplied. -/
theorem step (input : Input) (location : LocationTree) (good : State input location)
    (nextTag : BorTag) (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping nextTag) (different : input.newTag ≠ nextTag) :
    (read input {}).status = .Completed ∧ (child input {}).outcome = .ok () ∧
    ∃ nextInput postLocation, nextInput.tree = (child input {}).tree ∧ nextInput.parent = input.parent ∧
      nextInput.newTag = nextTag ∧ State nextInput postLocation ∧ nextInput.tree.tagMapping = mapping input ∧ nextInput.len = input.len := by
  obtain ⟨forest⟩ := good.forest
  let prepared := afterReadInput input location {} good.offset
  have readFacts := GeneralBorrowFullSharedRead.read_closed input location good.offset
    good.locations good.roots good.parentless forest good.profile
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput,good.offset]
  have childTree : (child input {}).tree = result prepared := by rw [actualChild];rfl
  have metadata := GeneralBorrowFreshMetadataChildShared.append prepared
  obtain ⟨postLocation,locations,profile,cache⟩ := GeneralBorrowFullSharedAppend.append prepared
    (readLocation input location {}) good.offset rfl good.parentless readFacts.2.2.1
  let nextInput := GeneralBorrowFullSharedNext.next prepared nextTag room fresh different
  have fields := GeneralBorrowFullSharedNext.next_fields prepared nextTag room fresh different
  change nextInput.tree = _ ∧ _ at fields
  rcases fields with ⟨treeEq,parentEq,parentTagEq,newEq,offsetEq,lengthEq,protectedEq,tagEq,parentlessEq,exposedEq⟩
  have postForest := GeneralBorrowFreshTopology.extended_forest _ _ prepared.parent.toNat
    (metadata.extension (readLocation input location {}) postLocation {}) forest
  refine ⟨readFacts.1,?_,nextInput,postLocation,treeEq.trans childTree.symm,parentEq,newEq,?_,?_,lengthEq⟩
  · rw [actualChild]
    exact metadata.success
  · refine ⟨offsetEq.trans good.offset,?_,?_,parentlessEq.trans good.parentless,?_,?_⟩
    · rw [lengthEq,treeEq];exact locations
    · rw [treeEq,metadata.roots,parentEq];exact good.roots
    · rw [treeEq];exact ⟨postForest⟩
    · rw [treeEq,parentEq];exact profile
  · rw [treeEq,metadata.mapping]
    rfl
end DuplicatePrefix.GeneralBorrowFullSharedStep
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFullSharedStep.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared generator step dependency {dependency}"
