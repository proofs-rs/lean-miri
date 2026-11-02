import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry
import duplicate_prefix.GeneralBorrowSifaView
import duplicate_prefix.GeneralBorrowFreshMetadata

namespace DuplicatePrefix.GeneralBorrowSifaOutsidePath
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowNodeUpdate GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] UniValMap.insert

def observation (tree : BorrowTree) (query : UniIndex) :=
  (tree.nodes.get query,tree.locations.entries.map (fun segment => (segment.range,segment.data.perms.get query)))

theorem weakened_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) (different : query ≠ index) :
    observation (weakened tree index node strongest) query = observation tree query := by
  apply Prod.ext
  · exact GeneralBorrowFreshLocation.get_other tree.nodes index query _ different
  · simp only [observation,weakened,DedupRangeMap.modifyAll,Array.map_map]
    apply congrArg (fun function => tree.locations.entries.map function)
    funext segment
    simp only [Function.comp_apply]
    cases stored : segment.data.perms.get index with
    | none => simp only [stored]
    | some state =>
      simp only [stored]
      exact congrArg (fun value => (segment.range,value))
        (GeneralBorrowFreshLocation.get_other segment.data.perms index query _ different)

structure Current (before : BorrowTree) (query start : UniIndex) (current : BorrowTree)
    (cursor : Option UniIndex) (active : Bool) : Prop where
  shape : treeShape current = treeShape before
  frame : observation current query = observation before query
  path : active = true → ∀ index,cursor = some index → Path before index start

def Preserves (before : BorrowTree) (query start : UniIndex) (state : GeneralBorrowSifa.LoopState) : Prop :=
  Current before query start state.2.1 state.2.2.1 state.2.2.2.2 ∧
    ∀ returned,state.1 = some returned → observation returned.1 query = observation before query

/-- Actual SIFA only writes ancestors of its initial parent. Exact optional
storage and full default node data outside that path survive all return paths;
no successful-operation, permission profile or stable-SIFA premise is needed. -/
theorem frame (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (start : UniIndex) (startNode : TreeNode) (present : tree.nodes.get start = some startNode)
    (query : UniIndex) (outside : ¬Path tree query start) (strongest : IdempotentForeignAccess) :
    observation (sourceUpdateSifa tree start strongest).1 query = observation tree query := by
  unfold_source_sifa
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves tree query start state →
        (∃ final, scan () state = .done final ∧ Preserves tree query start final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves tree query start next ∧
          GeneralBorrowSifaView.Measure next < GeneralBorrowSifaView.Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have good : Current tree query start current cursor active := preserved.1
      cases active with
      | false => exact .inl ⟨_,rfl,good,by simp⟩
      | true =>
        by_cases past : steps > current.nodes.size
        · refine .inl ⟨(some (current,.error (.ParentCycle (cursor.getD start))),current,cursor,steps,true),?_,?_,?_⟩
          · simp [scan,past]
          · exact good
          · intro returned same;cases same;exact good.frame
        · cases cursor with
          | none =>
            refine .inr ⟨(none,current,none,steps,false),?_,?_,?_⟩
            · simp [scan,past]
            · exact ⟨⟨good.shape,good.frame,by simp⟩,by simp⟩
            · simp [GeneralBorrowSifaView.Measure]
          | some index =>
            cases lookup : current.nodes.get index with
            | none =>
              refine .inl ⟨(some (current,.error (.MissingNode index)),current,some index,steps,true),?_,?_,?_⟩
              · simp [scan,past,lookup]
              · exact good
              · intro returned same;cases same;exact good.frame
            | some node =>
              let nextTree := weakened current index node strongest
              have indexPath : Path tree index start := good.path rfl index rfl
              have different : query ≠ index := by intro same;subst query;exact outside indexPath
              have nextFrame : observation nextTree query = observation tree query :=
                (weakened_other current index query node strongest different).trans good.frame
              have nextShape : treeShape nextTree = treeShape tree :=
                (weakened_tree_shape current index node lookup strongest).trans good.shape
              have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index node _ lookup
              cases actualChanged : changed current index node strongest with
              | false =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged];rfl
                refine .inr ⟨_,actual,⟨⟨nextShape,nextFrame,by simp⟩,by simp⟩,?_⟩
                simp [GeneralBorrowSifaView.Measure]
              | true =>
                have actual : scan () (returned,current,some index,steps,true) = .yield (none,nextTree,node.parent,steps+1,true) := by
                  simp only [scan,ite_eq_left rfl,ite_eq_right past,lookup]
                  change (if changed current index node strongest then _ else _) = _
                  rw [actualChanged];rfl
                refine .inr ⟨_,actual,⟨⟨nextShape,nextFrame,?_⟩,by simp⟩,?_⟩
                · intro active parent edge
                  obtain ⟨old,found,tag,parentSame,children,permission⟩ :=
                    GeneralBorrowFreshMetadata.node_fields current tree good.shape.symm index node lookup
                  have oldEdge : old.parent = some parent := parentSame.trans edge
                  obtain ⟨parentNode,parentFound,_⟩ := depth.parent index old found parent oldEdge
                  exact GeneralBorrowSharedAuthorizationGeometry.path_trans
                    (.step (.refl parent parentNode parentFound) old found oldEdge) indexPath
                · simp only [GeneralBorrowSifaView.Measure,↓reduceIte]
                  rw [sameSize];omega
    have initial : Preserves tree query start (none,tree,some start,0,true) :=
      ⟨⟨rfl,rfl,by intro _ index same;cases same;exact .refl start startNode present⟩,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan GeneralBorrowSifaView.Measure
      (Preserves tree query start) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1.frame
    | some returned => exact maintained.2 returned actual

end DuplicatePrefix.GeneralBorrowSifaOutsidePath
