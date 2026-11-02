import duplicate_prefix.GeneralBorrowSifaView
namespace DuplicatePrefix.GeneralBorrowSifaCacheFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- Range boundaries and exposure-cache data retained by the ancestor-SIFA stage. -/
def cacheShape (tree : BorrowTree) := tree.locations.entries.map (fun segment => (segment.range,segment.data.exposedCache))

/-- SIFA weakening updates only permissions and node default SIFA. -/
theorem weakened_cacheShape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) :
    cacheShape (GeneralBorrowSifa.weakened tree index node strongest) = cacheShape tree := by
  apply Array.ext
  · simp [cacheShape,GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll]
  · intro position left right
    have valid : position < tree.locations.entries.size := by simpa only [cacheShape,Array.size_map] using right
    simp only [cacheShape,GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll,Array.getElem_map]
    cases tree.locations.entries[position].data.perms.get index <;> rfl

def Preserves (before : BorrowTree) (state : GeneralBorrowSifa.LoopState) : Prop :=
  cacheShape state.2.1 = cacheShape before ∧
    ∀ returned, state.1 = some returned → cacheShape returned.1 = cacheShape before

def Measure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Every branch of the actual ancestor-SIFA loop preserves range boundaries and
exposure-cache data, including error results. No success premise is used. -/
theorem sifa_cache (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) :
    cacheShape (sourceUpdateSifa tree start strongest).1 = cacheShape tree := by
  unfold_source_sifa
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves tree state →
        (∃ final, scan () state = .done final ∧ Preserves tree final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves tree next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : cacheShape current = cacheShape tree := preserved.1
      cases active with
      | false => exact .inl ⟨_,rfl,⟨currentShape,by simp⟩⟩
      | true =>
        by_cases past : steps > current.nodes.size
        · refine .inl ⟨(some (current,.error (.ParentCycle (cursor.getD start))),current,cursor,steps,true),?_,?_⟩
          · simp [scan,past]
          · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
        · cases cursor with
          | none =>
            refine .inr ⟨(none,current,none,steps,false),?_,⟨currentShape,by simp⟩,?_⟩
            · simp [scan,past]
            · simp [Measure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_⟩
              · simp [scan,past,lookup]
              · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
            | some node =>
              let nextTree := weakened current index node strongest
              have nextShape : cacheShape nextTree = cacheShape tree :=
                (weakened_cacheShape current index node strongest).trans currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : Preserves tree (none,tree,some start,0,true) := ⟨rfl,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan Measure (Preserves tree) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual
end DuplicatePrefix.GeneralBorrowSifaCacheFrame
