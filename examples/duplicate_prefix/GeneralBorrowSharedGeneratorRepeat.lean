import duplicate_prefix.GeneralBorrowSharedGeneratorStep
namespace DuplicatePrefix.GeneralBorrowSharedGeneratorRepeat
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadParentRead
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Finite histories of the actual ranged Read and shared constructor. The
relation records completions; the theorem below constructs them from initial
state and fresh tags, rather than taking these completions as premises. -/
inductive Run : Input → List BorTag → Input → Prop where
  | nil (input : Input) : Run input [] input
  | cons {input next final : Input} {tag : BorTag} {rest : List BorTag}
      (readDone : (read input {}).status = .Completed)
      (childDone : (child input {}).outcome = .ok ())
      (tree : next.tree = (child input {}).tree)
      (parent : next.parent = input.parent) (newTag : next.newTag = tag)
      (tail : Run next rest final) : Run input (tag :: rest) final

/-- Every finite list of initially fresh, distinct future tags generates real
Read+append operations on the same parent and retains the invariant. The only
length bound is explicit UInt32 allocator headroom; there is no 65536 bound.
Initial profile/forest formation from arbitrary Rust histories remains separate. -/
theorem iterate (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size + tags.length ≤ 4294967295) :
    ∃ final finalLocation, Run input tags final ∧ State final finalLocation := by
  induction tags generalizing input location with
  | nil => exact ⟨input,location,.nil input,good⟩
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
    obtain ⟨final,finalLocation,history,finalGood⟩ := ih next nextLocation nextGood nextFresh
      (List.nodup_cons.mp distinct).2 nextCurrent nextRoom
    exact ⟨final,finalLocation,.cons readDone childDone tree parent newTag history,finalGood⟩
end DuplicatePrefix.GeneralBorrowSharedGeneratorRepeat
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedGeneratorRepeat.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved repeated generator dependency {dependency}"
