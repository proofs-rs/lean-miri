import duplicate_prefix.GeneralBorrowPhysicalReadableLifo
import duplicate_prefix.GeneralBorrowForestGeneratedRootEndFrames
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableLifoGlobal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowPhysicalReadableLifo GeneralBorrowForestGeneratedRootEndFrames
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem array_induct {α : Type} (P : Array α→Prop) (empty : P #[])
    (push : ∀xs x,P xs→P (xs.push x)) (xs : Array α) : P xs := by
  have aux : ∀rows : List α,P rows.reverse.toArray := by
    intro rows
    induction rows with
    | nil => exact empty
    | cons x rows ih => simpa using push rows.reverse.toArray x ih
  simpa using aux xs.toList.reverse

/-- The actual source run, after its real implicit releases succeed, has
precisely the global state obtained by LIFO endCall bookkeeping. This equality
connects the operational suffix to protector-removal facts. -/
theorem global (id : AllocId) (frames : Array (BorTag × FrameState)) :
    ∀tree global,Released id (⟨tree,global,frames⟩:Snapshot) frames.size→
      (GeneralBorrowForestGeneratedTagHistory.run id ⟨tree,global,frames⟩ (List.replicate frames.size .release)).state.global=
        endFrames global frames.toList.reverse := by
  induction frames using array_induct with
  | empty => intro tree global trace; rfl
  | push frames last ih =>
    intro tree global trace
    rw [Array.size_push,Released] at trace
    obtain ⟨tag,frame,back,completed,laterTrace⟩ := trace
    have equal : (tag,frame)=last := by simpa only [Array.back?_push,Option.some.injEq] using back.symm
    cases last with
    | mk lastTag lastFrame =>
      have tags := congrArg Prod.fst equal
      have frameEq := congrArg Prod.snd equal
      dsimp only at tags frameEq
      subst tag
      subst frame
      let next := (tree.releaseProtector lastTag global.protectedTags).tree
      have actual : step id ⟨tree,global,frames.push (lastTag,lastFrame)⟩ .release=
          ⟨⟨next,global.endCall lastFrame,frames⟩,true⟩ := by
        simp only [step,Array.back?_push,completed,beq_self_eq_true,↓reduceIte,Array.pop_push]
        rfl
      rw [actual] at laterTrace
      have later := ih next (global.endCall lastFrame) laterTrace
      simpa only [Array.size_push,List.replicate_succ,GeneralBorrowForestGeneratedTagHistory.run,actual,↓reduceIte,
        endFrames,Array.toList_push,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,List.foldl_cons] using later

/-- All held tags are absent only after the real tree-release/endCall suffix.
Actual frame coverage is used, never an assumed final empty protector table. -/
theorem unheld (id : AllocId) (state : Snapshot) (trace : Released id state state.frames.size)
    (covered : Covered state) (tag : BorTag) :
    (GeneralBorrowForestGeneratedTagHistory.run id state (List.replicate state.frames.size .release)).state.global.protectedTags.contains tag=false := by
  rw [global id state.frames state.tree state.global trace]
  exact closed_unheld state covered tag
end DuplicatePrefix.GeneralBorrowPhysicalReadableLifoGlobal
