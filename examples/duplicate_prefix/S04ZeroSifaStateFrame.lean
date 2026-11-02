import duplicate_prefix.GeneralBorrowSifaCacheFrame
import duplicate_prefix.GeneralBorrowFreshLocation

namespace DuplicatePrefix.S04ZeroSifaStateFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowSifa GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def Reset (before after : Option IdempotentForeignAccess) : Prop :=
  after = before ∨ after = before.map (fun _ => .None)

theorem Reset.refl (value : Option IdempotentForeignAccess) : Reset value value := .inl rfl

theorem Reset.trans {before middle after : Option IdempotentForeignAccess}
    (first : Reset before middle) (second : Reset middle after) : Reset before after := by
  rcases first with same | reset
  · rw [same] at second
    exact second
  · rcases second with same | again
    · exact .inr (same.trans reset)
    · apply Or.inr
      rw [again,reset]
      cases before <;> rfl

def nodeSifa (tree : BorrowTree) (query : UniIndex) := (tree.nodes.get query).map TreeNode.defaultInitialSifa

def storedSifa (tree : BorrowTree) (position : Nat) (query : UniIndex) : Option IdempotentForeignAccess :=
  tree.locations.entries[position]?.bind fun segment => (segment.data.perms.get query).map LocationState.idempotentForeignAccess

/-- Only original SIFA or None may appear after the protected constructor's
actual ancestor weakening, both in lazy node defaults and stored row states. -/
def Frame (before after : BorrowTree) : Prop :=
  (∀ query,Reset (nodeSifa before query) (nodeSifa after query)) ∧
  ∀ position query,Reset (storedSifa before position query) (storedSifa after position query)

theorem Frame.refl (tree : BorrowTree) : Frame tree tree :=
  ⟨fun _ => Reset.refl _,fun _ _ => Reset.refl _⟩

theorem Frame.trans {before middle after : BorrowTree} (first : Frame before middle)
    (second : Frame middle after) : Frame before after :=
  ⟨fun query => (first.1 query).trans (second.1 query),
    fun position query => (first.2 position query).trans (second.2 position query)⟩

private theorem ensure_none (value : IdempotentForeignAccess) :
    (value.ensureNoStrongerThan .None).1 = .None := by cases value <;> rfl

theorem weakened_frame (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) : Frame tree (GeneralBorrowSifa.weakened tree index node .None) := by
  constructor
  · intro query
    by_cases same : query = index
    · subst query
      apply Or.inr
      simp only [nodeSifa,GeneralBorrowSifa.weakened,GeneralBorrowFreshLocation.get_same,present,
        Option.map_some,ensure_none]
    · apply Or.inl
      simp only [nodeSifa,GeneralBorrowSifa.weakened,GeneralBorrowFreshLocation.get_other _ index query _ same]
  · intro position query
    simp only [storedSifa,GeneralBorrowSifa.weakened,DedupRangeMap.modifyAll,Array.getElem?_map]
    cases selected : tree.locations.entries[position]? with
    | none => exact Reset.refl _
    | some row =>
      simp only [Option.map_some,Option.bind_some]
      by_cases same : query = index
      · subst query
        apply Or.inr
        cases stored : row.data.perms.get index with
        | none => simp only [stored,Option.map_none]
        | some state =>
          simp only [stored,GeneralBorrowFreshLocation.get_same,Option.map_some,ensure_none]
      · apply Or.inl
        cases stored : row.data.perms.get index with
        | none => rfl
        | some state =>
          simp only [GeneralBorrowFreshLocation.get_other _ index query _ same]

def Preserves (before : BorrowTree) (state : GeneralBorrowSifa.LoopState) : Prop :=
  Frame before state.2.1 ∧
    ∀ returned, state.1 = some returned → Frame before returned.1

def Measure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Every branch of the actual ancestor-SIFA loop preserves range boundaries and
exposure-cache data, including error results. No success premise is used. -/
theorem sifa_frame (tree : BorrowTree) (start : UniIndex)  :
    Frame tree (sourceUpdateSifa tree start .None).1 := by
  unfold_source_sifa
  split
  · exact Frame.refl tree
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves tree state →
        (∃ final, scan () state = .done final ∧ Preserves tree final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves tree next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : Frame tree current := preserved.1
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
              let nextTree := weakened current index node .None
              have nextShape : Frame tree nextTree :=
                Frame.trans currentShape (weakened_frame current index node lookup)
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node .None with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node .None then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node .None then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [Measure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : Preserves tree (none,tree,some start,0,true) := ⟨Frame.refl tree,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan Measure (Preserves tree) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual

end DuplicatePrefix.S04ZeroSifaStateFrame
