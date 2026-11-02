import duplicate_prefix.GeneralBorrowProtectedReadableStage
import duplicate_prefix.GeneralBorrowForestFnEntry
namespace DuplicatePrefix.GeneralBorrowProtectedReadableFnEntry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual fresh pointer-tag consumption and Strong registration occur BEFORE
the real leading Read and protected constructor. Simultaneously held readable
reservations are permitted; no intermediate success or ownership is an input. -/
theorem invoke (input : GeneralBorrowFreshMetadataChildMutable.Input) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (tag : input.newTag = global.nextPointerTag)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (unheld : global.protectedTags.get input.newTag = none)
    (nodeTags : ∀ index node,input.tree.nodeAt index = some node → input.tree.indexOfTag node.tag = some index)
    (roots : input.tree.roots = #[input.parent])
    (initial : Every (Profile input.tree global.protectedTags) input.tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) input.tree.locations) :
    ∃ output,GeneralBorrowForestFnEntry.operation input.tree global frame allocation input.parentTag input.offset input.len
      .VisitChildrenOfAccessed = .ok output ∧ output.tag = global.nextPointerTag ∧
      output.global.nextPointerTag = TypedRetagEmpty.successorTag global.nextPointerTag room ∧
      output.global.protectedTags.get output.tag = some .StrongProtector ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      Every (Profile output.child.tree output.global.protectedTags) output.child.tree.locations ∧
      Nonempty (GeneralBorrowProtectedReadableStage.Prepared input output.global.protectedTags) ∧
      output.global.protectedTags = global.protectedTags.insert input.newTag .StrongProtector ∧
      output.access = GeneralBorrowProtectedReadableStage.read input output.global.protectedTags ∧
      output.child = GeneralBorrowProtectedReadableStage.child input output.global.protectedTags := by
  let advanced := {global with nextPointerTag := TypedRetagEmpty.successorTag global.nextPointerTag room}
  let registration := advanced.addProtector frame allocation input.newTag .StrongProtector
  have absent : input.tree.indexOfTag input.newTag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  have fresh : GeneralBorrowProtector.Fresh input.tree input.newTag := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get input.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    intro same
    have lookup := nodeTags row.1 row.2 present
    rw [same,absent] at lookup
    cases lookup
  have registered : Every (Profile input.tree registration.1.protectedTags) input.tree.locations := by
    intro position valid
    have projection := GeneralBorrowProtector.normal_projection input.tree input.tree.locations.entries[position].data
      global.protectedTags input.newTag .StrongProtector fresh
    change Nonempty (GeneralBorrowForest.Forest (source_normal_projection input.tree _ registration.1.protectedTags).topology) ∧
      GeneralBorrowProtectedReadInvariant.Data (source_normal_projection input.tree _ registration.1.protectedTags)
    change Nonempty (GeneralBorrowForest.Forest (source_normal_projection input.tree _ (global.protectedTags.insert input.newTag .StrongProtector)).topology) ∧
      GeneralBorrowProtectedReadInvariant.Data (source_normal_projection input.tree _ (global.protectedTags.insert input.newTag .StrongProtector))
    rw [projection]
    exact initial position valid
  let prepared := GeneralBorrowProtectedReadableStage.prepare input registration.1.protectedTags roots registered clean
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,input.newTag,
    GeneralBorrowProtectedReadableStage.read input registration.1.protectedTags,
    GeneralBorrowProtectedReadableStage.child input registration.1.protectedTags⟩
  refine ⟨output,?_,tag,rfl,?_,?_,prepared.completed,prepared.success,prepared.profile,⟨prepared⟩,rfl,rfl,rfl⟩
  · simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag global room,Except.bind,Except.pure,bind,pure]
    dsimp only [output,registration,GeneralBorrowProtectedReadableStage.child,GeneralBorrowProtectedReadableStage.read]
    simp only [tag]
    rfl
  · exact ProtectedTags.get_insert_same _ _ _
  · rfl
end DuplicatePrefix.GeneralBorrowProtectedReadableFnEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadableFnEntry.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected readable FnEntry dependency {dependency}"
