import duplicate_prefix.GeneralBorrowProtectedSiblingPartialAdvance
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingPartialCore
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem run {capacity} (windows : List (Window capacity)) (before : Core capacity windows.length) :
    ∃ after : Core capacity 0,loop windows (snapshot before) = .ok (snapshot after) ∧
      after.tags.length = before.tags.length+windows.length ∧ after.origins.map Prod.snd = before.origins.map Prod.snd++windows := by
  induction windows with
  | nil => exact ⟨before,rfl,by simp,by simp⟩
  | cons window rest ih =>
    obtain ⟨advance⟩ := GeneralBorrowProtectedSiblingPartialAdvance.generate before window
    obtain ⟨after,actual,count,origins⟩ := ih advance.next
    refine ⟨after,(advance.actual rest).trans actual,?_,?_⟩
    · have step := advance.count
      simp only [List.length_cons]
      omega
    · rw [advance.origins] at origins
      simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using origins
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialComplete
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartial
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartialCore
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
/-- Arbitrary positive bounded windows, with arbitrary partial overlap and
chronology, are executed by real protected root reborrows. No intermediate
operation outcome, graph, permission, cache or allocator is supplied. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (windows : List (Window capacity))
    (room : windows.length+2 ≤ 4294967295) : Nonempty (Ready capacity windows) := by
  let initial := seed capacity nonzero windows.length room
  obtain ⟨after,actual,count,origins⟩ := GeneralBorrowProtectedSiblingPartialComplete.run windows initial
  have operationEq : operation capacity windows = .ok (snapshot after) := by
    simp only [operation,GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation,Except.bind,bind,pure,Except.pure]
    exact actual
  refine ⟨{
    state := snapshot after,actual := operationEq,input := after.input,tree := rfl,parent := after.parent,parentTag := after.parentTag,
    offset := after.offset,len := after.len,roots := after.roots,capacity := after.capacity,allocator := after.allocator,
    readable := after.readable,physical := after.physical,coherent := after.coherent,held := after.held,distinct := after.distinct,
    frame := after.frameTags,count := ?_,rootUnique := after.rootUnique,hidden := after.hidden,nodes := ?_,origins := after.origins,originTags := after.originTags,
    originWindows := ?_,latest := after.latest,descriptors := after.descriptors,mapBelow := after.mapBelow,protectedBelow := after.protectedBelow,tagBelow := after.tagBelow }⟩
  · change after.tags.length = windows.length
    have zero : initial.tags = [] := rfl
    simpa only [zero,List.length_nil,Nat.zero_add] using count
  · change after.input.tree.nodes.size = windows.length+1
    rw [after.nodes]
    have zero : initial.tags = [] := rfl
    rw [zero,List.length_nil,Nat.zero_add] at count
    rw [count]
  · have zero : initial.origins = [] := rfl
    simpa only [zero,List.map_nil,List.nil_append] using origins
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartial
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingPartial.generate] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved partial sibling generation dependency {dependency}"
