import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowAdvance
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedSiblingGenerationWindowCore
variable {capacity : UInt64}
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem run (selected : List Bool) (before : Core capacity selected.length) :
    ∃ after : Core capacity 0,loop capacity selected (snapshot before) = .ok (snapshot after) ∧ after.tags.length = before.tags.length+selected.length := by
  induction selected with
  | nil => exact ⟨before,rfl,by simp⟩
  | cons chosen rest ih =>
    obtain ⟨advance⟩ := GeneralBorrowProtectedSiblingGenerationWindowAdvance.generate before chosen
    obtain ⟨after,actual,count⟩ := ih advance.next
    exact ⟨after,(advance.actual rest).trans actual,by have step := advance.count;simpa only [List.length_cons] using (by omega : after.tags.length = before.tags.length+(rest.length+1))⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowComplete

namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindow
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindowCore
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Any finite schedule within explicit tag/node headroom starts at the actual
root allocation and performs every real FnEntry append and selected exposure.
All source outcomes, retained profiles/caches, next-input metadata and earlier
reservation conflicts are derived internally. This is a positive-capacity full-window BorrowTree
lifecycle component, not an all-input whole-MIR or Rust-reachability claim. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool) (room : selected.length+2 ≤ 4294967295) : Nonempty (Ready capacity selected) := by
  let initial := seed capacity nonzero selected.length room
  obtain ⟨after,actual,count⟩ := GeneralBorrowProtectedSiblingGenerationWindowComplete.run selected initial
  have operationEq : operation capacity selected = .ok (snapshot after) := by
    simp only [operation,GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation,Except.bind,bind,pure,Except.pure]
    exact actual
  refine ⟨{
    state := snapshot after,actual := operationEq,input := after.input,tree := rfl,parent := after.parent,parentTag := after.parentTag,
    offset := after.offset,len := after.len,roots := after.roots,capacity := after.capacity,allocator := after.allocator,
    readable := after.readable,physical := after.physical,coherent := after.coherent,held := after.held,distinct := after.distinct,
    frame := after.frameTags,count := ?_,mapBelow := after.mapBelow,protectedBelow := after.protectedBelow,tagBelow := after.tagBelow,mapped := ?_,earlier := ?_ }⟩
  · change after.tags.length = selected.length
    have zero : initial.tags = [] := rfl
    rw [zero,List.length_nil,Nat.zero_add] at count
    exact count
  · intro tag member
    obtain ⟨descriptor⟩ := after.descriptors tag member
    refine ⟨descriptor.index,descriptor.node,descriptor.present,descriptor.tagged,?_⟩
    simpa only [BorrowTree.indexOfTag,descriptor.tagged] using after.allocator.nodeTags descriptor.index descriptor.node descriptor.present
  · intro tag member
    change tag ∈ after.tags.dropLast at member
    rcases after.earlier with empty | ⟨past,last,index,split,found,typed,previous⟩
    · rw [empty] at member;simp at member
    · exact previous tag (by simpa [split] using member)
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindow

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowComplete.run,``DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindow.generate] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved arbitrary protected sibling generation dependency {dependency}"
