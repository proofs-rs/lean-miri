import duplicate_prefix.GeneralBorrowSifaView
import duplicate_prefix.GeneralBorrowWildcardLeaf
import duplicate_prefix.GeneralBorrowFreshLocation
import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralBorrowSifaUniqueFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- Exact stored Unique state, including its accessed flag and None SIFA. -/
def UniqueAt (tree : BorrowTree) (query : UniIndex) : Prop :=
  GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get query = some GeneralBorrowWildcardLeaf.unique) tree.locations

/-- One real weakening preserves the fixed exact Unique state even when its
slot is visited: weakening None SIFA leaves it None. -/
theorem weakened_unique (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) (query : UniIndex) (good : UniqueAt tree query) :
    UniqueAt (GeneralBorrowSifa.weakened tree index node strongest) query := by
  intro position valid
  have previous : position < tree.locations.entries.size := by
    simpa only [GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll,Array.size_map] using valid
  have old := good position previous
  simp only [GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll,Array.getElem_map]
  by_cases equal : query = index
  · subst query
    rw [old]
    rw [GeneralBorrowFreshLocation.get_same]
    cases strongest <;> rfl
  · cases stored : (tree.locations.entries[position]'previous).data.perms.get index with
    | none => exact old
    | some state =>
      exact (GeneralBorrowFreshLocation.get_other _ index query _ equal).trans old

def Preserves (query : UniIndex) (state : GeneralBorrowSifa.LoopState) : Prop :=
  UniqueAt state.2.1 query ∧ ∀ returned, state.1 = some returned → UniqueAt returned.1 query

def Measure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Exact Unique permissions survive all actual ancestor-SIFA branches,
including missing-node and cycle errors, without a path or success premise. -/
theorem sifa_unique (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (query : UniIndex) (good : UniqueAt tree query) :
    UniqueAt (sourceUpdateSifa tree start strongest).1 query := by
  unfold_source_sifa
  split
  · exact good
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves query state →
        (∃ final, scan () state = .done final ∧ Preserves query final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves query next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : UniqueAt current query := preserved.1
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
              have nextShape : UniqueAt nextTree query :=
                weakened_unique current index node strongest query currentShape
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
    have initial : Preserves query (none,tree,some start,0,true) := ⟨good,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan Measure (Preserves query) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual
end DuplicatePrefix.GeneralBorrowSifaUniqueFrame
