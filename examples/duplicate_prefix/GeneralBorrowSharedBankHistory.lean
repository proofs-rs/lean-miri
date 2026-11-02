import duplicate_prefix.GeneralBorrowSharedBankAdvance

namespace DuplicatePrefix.GeneralBorrowSharedBankHistory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowRecursiveSharedResources
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Parent positions may select any previously generated handle. New children
are prepended, so the available bank grows once per actual constructor. -/
def Choices : Nat → List (BorTag × Nat) → Prop
  | _, [] => True
  | count, (_, position)::rest => position < count ∧ Choices (count+1) rest

def parent {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len) (position : Nat) (valid : position < s.handles.length) :=
  s.handles[position]

theorem parent_mem {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len) (position : Nat) (valid : position < s.handles.length) :
    parent s position valid ∈ s.handles := List.getElem_mem valid

inductive Run {root : UniIndex} {offset len : UInt64} (nonzero : len ≠ 0) :
    GeneralBorrowSharedBankState.State root offset len → List (BorTag × Nat) →
      GeneralBorrowSharedBankState.State root offset len → Prop where
  | nil (s) : Run nonzero s [] s
  | cons (s) (tag : BorTag) (position : Nat) (rest : List (BorTag × Nat))
      (valid : position < s.handles.length)
      (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag)
      (room : s.tree.nodes.size+5 ≤ 4294967295)
      (readDone : (read (supplied (select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).status = .Completed)
      (childDone : (child (supplied (select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).outcome = .ok ())
      {final} (tail : Run nonzero
        (GeneralBorrowSharedBankAdvance.next s (parent s position valid) (parent_mem s position valid) tag fresh nonzero room) rest final) :
      Run nonzero s ((tag,position)::rest) final

/-- Finite arbitrary prior-parent branching is formed from initial metadata and
Read owners. Every real Read/constructor completes; every stage retains bank
ownership and allocator/forest resources. No operation-success premise occurs. -/
theorem generate {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len) (nonzero : len ≠ 0)
    (steps : List (BorTag × Nat)) (choices : Choices s.handles.length steps)
    (unique : (steps.map Prod.fst).Nodup)
    (fresh : ∀ tag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh s.tree.tagMapping tag)
    (room : s.tree.nodes.size+steps.length+4 ≤ 4294967295) :
    ∃ final, Run nonzero s steps final ∧
      final.handles.length = s.handles.length+steps.length ∧
      final.tree.nodes.size ≤ s.tree.nodes.size+steps.length ∧
      (∀ tag, tag ∉ steps.map Prod.fst → GeneralBorrowTagMap.Fresh s.tree.tagMapping tag →
        GeneralBorrowTagMap.Fresh final.tree.tagMapping tag) := by
  induction steps generalizing s with
  | nil => exact ⟨s,.nil s,rfl,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    rcases action with ⟨tag,position⟩
    have distinct := List.nodup_cons.mp unique
    have valid := choices.1
    let index := parent s position valid
    have member : index ∈ s.handles := parent_mem s position valid
    have available := fresh tag (by simp)
    have reserve : s.tree.nodes.size+5 ≤ 4294967295 := by simp only [List.length_cons] at room;omega
    let selected := select s index member
    let post := GeneralBorrowSharedBankAdvance.next s index member tag available nonzero reserve
    have facts := advance s.tree root s.resources index selected.node selected.present tag available offset len nonzero s.bounds
      {} false (fun _ => false) selected.owned reserve
    have growth := GeneralBorrowSharedBankAdvance.size s index member tag available nonzero reserve
    have count := GeneralBorrowSharedBankAdvance.handles_length s index member tag available nonzero reserve
    have laterChoices : Choices post.handles.length rest := by rw [show post.handles.length = s.handles.length+1 from count];exact choices.2
    have laterFresh : ∀ nextTag ∈ rest.map Prod.fst, GeneralBorrowTagMap.Fresh post.tree.tagMapping nextTag := by
      intro nextTag memberNext
      exact (metadata selected tag available nonzero false).freshTag nextTag (fresh nextTag (by simp [memberNext]))
        (fun same => distinct.1 (same ▸ memberNext))
    have laterRoom : post.tree.nodes.size+rest.length+4 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      change post.tree.nodes.size ≤ s.tree.nodes.size+1 at growth
      omega
    obtain ⟨final,history,length,bound,future⟩ := ih post laterChoices distinct.2 laterFresh laterRoom
    refine ⟨final,.cons s tag position rest valid available reserve facts.1 facts.2.1 history,?_,?_,?_⟩
    · change post.handles.length = _ at count
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      change post.tree.nodes.size ≤ s.tree.nodes.size+1 at growth
      omega
    · intro nextTag unused initial
      have parts : nextTag ≠ tag ∧ nextTag ∉ rest.map Prod.fst := by simpa only [List.map_cons,List.mem_cons,not_or] using unused
      exact future nextTag parts.2 ((metadata selected tag available nonzero false).freshTag nextTag initial (Ne.symm parts.1))
end DuplicatePrefix.GeneralBorrowSharedBankHistory
