import duplicate_prefix.GeneralBorrowFreshMetadata
import duplicate_prefix.GeneralBorrowSifaView

namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildSifa
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exposure flags are separate from the permission/topology view: the latter
intentionally forgets them. This view retains sparse vacancies as well. -/
def exposureShape (tree : BorrowTree) := tree.nodes.data.map (Option.map (fun node => node.isExposed))

theorem weakened_exposure (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (strongest : IdempotentForeignAccess) :
    exposureShape (GeneralBorrowSifa.weakened tree index node strongest) = exposureShape tree :=
  GeneralBorrowView.insert_existing_shape (fun node : TreeNode => node.isExposed) tree.nodes index node
    {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1} present rfl

def PreservesExposure (before : BorrowTree) (state : GeneralBorrowSifa.LoopState) : Prop :=
  exposureShape state.2.1 = exposureShape before ∧
    ∀ returned, state.1 = some returned → exposureShape returned.1 = exposureShape before

def ExposureMeasure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- Every branch of the actual ancestor-SIFA loop preserves all node exposure
flags, including its error branches. No operation-success premise is used. -/
theorem sifa_exposure (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess) :
    exposureShape (sourceUpdateSifa tree start strongest).1 = exposureShape tree := by
  unfold_source_sifa
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, PreservesExposure tree state →
        (∃ final, scan () state = .done final ∧ PreservesExposure tree final) ∨
        ∃ next, scan () state = .yield next ∧ PreservesExposure tree next ∧ ExposureMeasure next < ExposureMeasure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : exposureShape current = exposureShape tree := preserved.1
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
            · simp [ExposureMeasure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_⟩
              · simp [scan,past,lookup]
              · exact ⟨currentShape,fun returned same => by cases same; exact currentShape⟩
            | some node =>
              let nextTree := weakened current index node strongest
              have nextShape : exposureShape nextTree = exposureShape tree :=
                (weakened_exposure current index node lookup strongest).trans currentShape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp [ExposureMeasure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged]
                  rfl
                refine .inr ⟨_,actual,⟨nextShape,by simp⟩,?_⟩
                simp only [ExposureMeasure,↓reduceIte]
                rw [sameSize]
                omega
    have initial : PreservesExposure tree (none,tree,some start,0,true) := ⟨rfl,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan ExposureMeasure (PreservesExposure tree) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual

private theorem map_lookup (nodes : UniValMap TreeNode) (index : UniIndex) :
    (UniValMap.get ⟨nodes.data.map (Option.map (fun node => node.isExposed))⟩ index) =
      (nodes.get index).map (fun node => node.isExposed) := by
  simp only [UniValMap.get,Array.getElem?_map]
  cases nodes.data[index.toNat]? <;> rfl

theorem lookup_exposure (before after : BorrowTree) (same : exposureShape after = exposureShape before)
    (index : UniIndex) :
    (after.nodes.get index).map (fun node => node.isExposed) =
      (before.nodes.get index).map (fun node => node.isExposed) := by
  rw [←map_lookup after.nodes index,←map_lookup before.nodes index]
  exact congrArg (fun values => UniValMap.get ⟨values⟩ index) same

/-- The actual SIFA result retains every structural field needed for a later
reborrow, and additionally the exposure flag omitted from treeShape. -/
theorem node_fields (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    ∃ next, (sourceUpdateSifa tree start strongest).1.nodeAt index = some next ∧
      next.tag = node.tag ∧ next.parent = node.parent ∧ next.children = node.children ∧
      next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,lookup,tag,parent,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields tree
    (sourceUpdateSifa tree start strongest).1 (GeneralBorrowSifaView.preserves tree start strongest) index node present
  have flags := lookup_exposure tree (sourceUpdateSifa tree start strongest).1 (sifa_exposure tree start strongest) index
  change tree.nodes.get index = some node at present
  rw [lookup,present] at flags
  exact ⟨next,lookup,tag,parent,children,permission,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

end DuplicatePrefix.GeneralBorrowFreshMetadataChildSifa
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildSifa." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual SIFA exposure preservation dependency {dependency}"
