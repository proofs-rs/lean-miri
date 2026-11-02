import duplicate_prefix.GeneralBorrowSharedBankGcAction
namespace DuplicatePrefix.GeneralBorrowSharedBankGcHistory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankGcAction DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowRecursiveSharedResources
open DuplicatePrefix.GeneralBorrowSharedRootBankHistory (parent parent_mem)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

inductive Run {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (nonzero : len ≠ 0) (terminal : BorTag) :
    GeneralBorrowSharedRootBankState.State root rootTag offset len → List Action →
      GeneralBorrowSharedRootBankState.State root rootTag offset len → Prop where
  | nil (s) : Run nonzero terminal s [] s
  | borrow (s) (tag : BorTag) (position : Nat) (rest : List Action)
      (valid : position < s.bank.handles.length)
      (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
      (room : s.bank.tree.nodes.size+5 ≤ 4294967295)
      (readDone : (read (supplied (GeneralBorrowSharedRootBankState.select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).status = .Completed)
      (childDone : (child (supplied (GeneralBorrowSharedRootBankState.select s (parent s position valid) (parent_mem s position valid)) tag fresh nonzero) {} false).outcome = .ok ())
      {final} (tail : Run nonzero terminal
        (GeneralBorrowSharedRootBankAdvance.next s (parent s position valid) (parent_mem s position valid) tag fresh nonzero room) rest final) :
      Run nonzero terminal s (.borrow tag position :: rest) final
  | gc (s) (extra : Array BorTag) (rest : List Action)
      (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping terminal)
      (completed : (s.bank.tree.removeUnreachableTags (live s extra)).outcome = .ok ())
      {final} (tail : Run nonzero terminal (next s nonzero terminal fresh extra) rest final) :
      Run nonzero terminal s (.gc extra :: rest) final

/-- Any finite interleaving of arbitrary prior-parent shared constructors and
actual full GC is generated internally. Parent positions count constructors;
GC appends actual selectable handle tags to arbitrary extra liveness. Every
Read, constructor and GC success is an output of this Run, never a premise. -/
theorem generate {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (nonzero : len ≠ 0)
    (terminal : BorTag) (terminalFresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping terminal)
    (actions : List Action) (choices : Choices s.bank.handles.length actions)
    (unique : (tags actions).Nodup) (terminalUnused : terminal ∉ tags actions)
    (fresh : ∀ tag ∈ tags actions, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (room : s.bank.tree.nodes.size+(tags actions).length+4 ≤ 4294967295) :
    ∃ final, Run nonzero terminal s actions final ∧
      final.bank.handles.length = s.bank.handles.length+(tags actions).length ∧
      final.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+(tags actions).length ∧
      (∀ tag, tag ∉ tags actions → GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag →
        GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping tag) := by
  induction actions generalizing s with
  | nil => exact ⟨s,.nil s,rfl,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    cases action with
    | borrow tag position =>
      have distinct := List.nodup_cons.mp unique
      have unused : terminal ≠ tag ∧ terminal ∉ tags rest := by simpa only [tags,List.mem_cons,not_or] using terminalUnused
      have valid := choices.1
      let index := parent s position valid
      have member : index ∈ s.bank.handles := parent_mem s position valid
      have available := fresh tag (by simp [tags])
      have reserve : s.bank.tree.nodes.size+5 ≤ 4294967295 := by simp only [tags,List.length_cons] at room;omega
      let selected := GeneralBorrowSharedRootBankState.select s index member
      let post := GeneralBorrowSharedRootBankAdvance.next s index member tag available nonzero reserve
      have facts := advance s.bank.tree root s.bank.resources index selected.node selected.present tag available offset len nonzero s.bank.bounds
        {} false (GeneralBorrowSharedRootLabel.writable root) selected.owned reserve
      have growth := GeneralBorrowSharedRootBankAdvance.size s index member tag available nonzero reserve
      have count := GeneralBorrowSharedRootBankAdvance.handles_length s index member tag available nonzero reserve
      have laterChoices : Choices post.bank.handles.length rest := by rw [show post.bank.handles.length = s.bank.handles.length+1 from count];exact choices.2
      have laterFresh : ∀ nextTag ∈ tags rest, GeneralBorrowTagMap.Fresh post.bank.tree.tagMapping nextTag := by
        intro nextTag memberNext
        exact (metadata selected tag available nonzero false).freshTag nextTag (fresh nextTag (by simp [tags,memberNext]))
          (fun same => distinct.1 (same ▸ memberNext))
      have laterTerminal : GeneralBorrowTagMap.Fresh post.bank.tree.tagMapping terminal :=
        (metadata selected tag available nonzero false).freshTag terminal terminalFresh (Ne.symm unused.1)
      have laterRoom : post.bank.tree.nodes.size+(tags rest).length+4 ≤ 4294967295 := by
        simp only [tags,List.length_cons] at room
        change post.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+1 at growth
        omega
      obtain ⟨final,history,length,bound,future⟩ := ih post laterTerminal laterChoices distinct.2 unused.2 laterFresh laterRoom
      refine ⟨final,.borrow s tag position rest valid available reserve facts.1 facts.2.1 history,?_,?_,?_⟩
      · change post.bank.handles.length = _ at count
        simp only [tags,List.length_cons]
        omega
      · simp only [tags,List.length_cons]
        change post.bank.tree.nodes.size ≤ s.bank.tree.nodes.size+1 at growth
        omega
      · intro nextTag notUsed initial
        have parts : nextTag ≠ tag ∧ nextTag ∉ tags rest := by simpa only [tags,List.mem_cons,not_or] using notUsed
        exact future nextTag parts.2 ((metadata selected tag available nonzero false).freshTag nextTag initial (Ne.symm parts.1))
    | gc extra =>
      let post := next s nonzero terminal terminalFresh extra
      have count : post.bank.handles.length = s.bank.handles.length := congrArg List.length (handles s nonzero terminal terminalFresh extra)
      have capacity : post.bank.tree.nodes.size = s.bank.tree.nodes.size := size s nonzero terminal terminalFresh extra
      have laterChoices : Choices post.bank.handles.length rest := by rw [count];exact choices
      have laterFresh : ∀ tag ∈ tags rest, GeneralBorrowTagMap.Fresh post.bank.tree.tagMapping tag := by
        intro tag member
        exact fresh_tag s nonzero terminal terminalFresh extra tag (fresh tag member)
      have laterRoom : post.bank.tree.nodes.size+(tags rest).length+4 ≤ 4294967295 := by rw [capacity];exact room
      obtain ⟨final,history,length,bound,future⟩ := ih post
        (fresh_tag s nonzero terminal terminalFresh extra terminal terminalFresh) laterChoices unique terminalUnused laterFresh laterRoom
      refine ⟨final,.gc s extra rest terminalFresh (completed s nonzero extra) history,?_,?_,?_⟩
      · simpa only [tags,count] using length
      · simpa only [tags,capacity] using bound
      · intro tag notUsed initial
        exact future tag notUsed (fresh_tag s nonzero terminal terminalFresh extra tag initial)
end DuplicatePrefix.GeneralBorrowSharedBankGcHistory
