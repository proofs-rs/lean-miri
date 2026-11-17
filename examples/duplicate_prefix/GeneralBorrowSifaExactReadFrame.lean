import duplicate_prefix.GeneralBorrowSifaView
import duplicate_prefix.GeneralBorrowFreshLocation
import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralBorrowSifaExactReadFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- A fixed optional stored state at every allocation location. -/
def ExactAt (tree : BorrowTree) (query : UniIndex) (expected : Option LocationState) : Prop :=
  GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get query = expected) tree.locations

/-- A real Read-SIFA weakening preserves None, and exact states whose SIFA is
already None or Read. This includes sparse vacant permissions. -/
theorem weakened_exact (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (query : UniIndex) (expected : Option LocationState)
    (stable : ∀ state, expected = some state →
      {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} = state)
    (good : ExactAt tree query expected) :
    ExactAt (GeneralBorrowSifa.weakened tree index node .Read) query expected := by
  intro position valid
  have previous : position < tree.locations.entries.size := by
    simpa only [GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll,Array.size_map] using valid
  have old := good position previous
  simp only [GeneralBorrowSifa.weakened,Miri.DataStructures.DedupRangeMap.modifyAll,Array.getElem_map]
  by_cases equal : query = index
  · subst query
    rw [old]
    cases expected with
    | none => exact old
    | some state =>
      rw [GeneralBorrowFreshLocation.get_same,stable state rfl]
  · cases stored : (tree.locations.entries[position]'previous).data.perms.get index with
    | none => exact old
    | some state => exact (GeneralBorrowFreshLocation.get_other _ index query _ equal).trans old

def Preserves (query : UniIndex) (expected : Option LocationState) (state : GeneralBorrowSifa.LoopState) : Prop :=
  ExactAt state.2.1 query expected ∧ ∀ returned, state.1 = some returned → ExactAt returned.1 query expected

def Measure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Fixed optional states survive all actual Read ancestor-SIFA branches,
including missing-node and cycle errors, without a path or success premise. -/
theorem sifa_exact (tree : BorrowTree) (start : UniIndex)
    (query : UniIndex) (expected : Option LocationState)
    (stable : ∀ state, expected = some state →
      {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} = state)
    (good : ExactAt tree query expected) :
    ExactAt (sourceUpdateSifa tree start .Read).1 query expected := by
  unfold_source_sifa
  split
  · exact good
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves query expected state →
        (∃ final, scan () state = .done final ∧ Preserves query expected final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves query expected next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : ExactAt current query expected := preserved.1
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
              let nextTree := weakened current index node .Read
              have nextShape : ExactAt nextTree query expected :=
                weakened_exact current index node query expected stable currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node .Read with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node .Read then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node .Read then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : Preserves query expected (none,tree,some start,0,true) := ⟨good,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan Measure (Preserves query expected) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual
end DuplicatePrefix.GeneralBorrowSifaExactReadFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSifaExactReadFrame.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exact Read SIFA dependency {dependency}"
