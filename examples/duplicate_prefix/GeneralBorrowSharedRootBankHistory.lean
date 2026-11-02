import duplicate_prefix.GeneralBorrowSharedRootBankAdvance

namespace DuplicatePrefix.GeneralBorrowSharedRootBankHistory
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

def parent {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (position : Nat) (valid : position < s.bank.handles.length) :=
  s.bank.handles[position]

theorem parent_mem {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (position : Nat) (valid : position < s.bank.handles.length) :
    parent s position valid ∈ s.bank.handles := List.getElem_mem valid

inductive Run {root : UniIndex} {rootTag : BorTag} {offset len : UInt64} (nonzero : len ≠ 0) :
    GeneralBorrowSharedRootBankState.State root rootTag offset len → List (BorTag × Nat) →
      GeneralBorrowSharedRootBankState.State root rootTag offset len → Prop where
  | nil (s) : Run nonzero s [] s
  | cons (s) (tag : BorTag) (position : Nat) (rest : List (BorTag × Nat))
      (valid : position < s.bank.handles.length)
      (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
      (room : s.bank.tree.nodes.size+5 ≤ 4294967295)
      (readDone : (read (supplied (GeneralBorrowSharedRootBankState.select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).status = .Completed)
      (childDone : (child (supplied (GeneralBorrowSharedRootBankState.select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).outcome = .ok ())
      {final} (tail : Run nonzero
        (GeneralBorrowSharedRootBankAdvance.next s (parent s position valid) (parent_mem s position valid) tag fresh nonzero room) rest final) :
      Run nonzero s ((tag,position)::rest) final

/-- Finite arbitrary prior-parent branching is formed from initial metadata and
Read owners. Every real Read/constructor completes; every stage retains bank
ownership and allocator/forest resources. No operation-success premise occurs. -/
theorem generate {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (nonzero : len ≠ 0)
    (steps : List (BorTag × Nat)) (choices : Choices s.bank.handles.length steps)
    (unique : (steps.map Prod.fst).Nodup)
    (fresh : ∀ tag ∈ steps.map Prod.fst, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (room : s.bank.tree.nodes.size+steps.length+4 ≤ 4294967295) :
    ∃ final, Run nonzero s steps final ∧
      final.bank.handles.length = s.bank.handles.length+steps.length ∧
      final.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+steps.length ∧
      (∀ tag, tag ∉ steps.map Prod.fst → GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag →
        GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping tag) := by
  induction steps generalizing s with
  | nil => exact ⟨s,.nil s,rfl,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    rcases action with ⟨tag,position⟩
    have distinct := List.nodup_cons.mp unique
    have valid := choices.1
    let index := parent s position valid
    have member : index ∈ s.bank.handles := parent_mem s position valid
    have available := fresh tag (by simp)
    have reserve : s.bank.tree.nodes.size+5 ≤ 4294967295 := by simp only [List.length_cons] at room;omega
    let selected := GeneralBorrowSharedRootBankState.select s index member
    let post := GeneralBorrowSharedRootBankAdvance.next s index member tag available nonzero reserve
    have facts := advance s.bank.tree root s.bank.resources index selected.node selected.present tag available offset len nonzero s.bank.bounds
      {} false (GeneralBorrowSharedRootLabel.writable root) selected.owned reserve
    have growth := GeneralBorrowSharedRootBankAdvance.size s index member tag available nonzero reserve
    have count := GeneralBorrowSharedRootBankAdvance.handles_length s index member tag available nonzero reserve
    have laterChoices : Choices post.bank.handles.length rest := by rw [show post.bank.handles.length = s.bank.handles.length+1 from count];exact choices.2
    have laterFresh : ∀ nextTag ∈ rest.map Prod.fst, GeneralBorrowTagMap.Fresh post.bank.tree.tagMapping nextTag := by
      intro nextTag memberNext
      exact (metadata selected tag available nonzero false).freshTag nextTag (fresh nextTag (by simp [memberNext]))
        (fun same => distinct.1 (same ▸ memberNext))
    have laterRoom : post.bank.tree.nodes.size+rest.length+4 ≤ 4294967295 := by
      simp only [List.length_cons] at room
      change post.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+1 at growth
      omega
    obtain ⟨final,history,length,bound,future⟩ := ih post laterChoices distinct.2 laterFresh laterRoom
    refine ⟨final,.cons s tag position rest valid available reserve facts.1 facts.2.1 history,?_,?_,?_⟩
    · change post.bank.handles.length = _ at count
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      change post.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+1 at growth
      omega
    · intro nextTag unused initial
      have parts : nextTag ≠ tag ∧ nextTag ∉ rest.map Prod.fst := by simpa only [List.map_cons,List.mem_cons,not_or] using unused
      exact future nextTag parts.2 ((metadata selected tag available nonzero false).freshTag nextTag initial (Ne.symm parts.1))
end DuplicatePrefix.GeneralBorrowSharedRootBankHistory
