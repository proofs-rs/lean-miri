import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.GeneralBorrowSifaView
namespace DuplicatePrefix.GeneralBorrowSifaProfileTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowSifa DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

private theorem weaken_location (tree : BorrowTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (strongest : IdempotentForeignAccess) (location : LocationTree) (initial : Profile tree location protections) :
    Profile {tree with nodes := tree.nodes.insert index {node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1}}
      (weakenLocation location index strongest) protections := by
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases same : query = index
    · subst query
      change (tree.nodes.insert index _).get index = some value at found
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      have old := initial.present index node present
      cases stored : location.perms.get index with
      | none =>
        simp only [weakenLocation,stored] at old ⊢
        exact GeneralBorrowSifaPermissionConsistency.weaken node.defaultLocationState (protections.contains node.tag) strongest old
      | some state =>
        simp only [stored,Option.getD_some] at old
        simp only [weakenLocation,stored,GeneralBorrowFreshLocation.get_same,Option.getD_some]
        exact GeneralBorrowSifaPermissionConsistency.weaken state (protections.contains node.tag) strongest old
    · have original : tree.nodeAt query = some value := by
        change (tree.nodes.insert index _).get query = some value at found
        rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
        exact found
      have old := initial.present query value original
      cases stored : location.perms.get index with
      | none => simpa only [weakenLocation,stored] using old
      | some state =>
        simpa only [weakenLocation,stored,GeneralBorrowFreshLocation.get_other _ index query _ same] using old
  · intro query missing
    have different : query ≠ index := by
      intro same;subst query
      change (tree.nodes.insert index _).get index = none at missing
      rw [GeneralBorrowFreshLocation.get_same] at missing
      cases missing
    have original : tree.nodes.get query = none := by
      change (tree.nodes.insert index _).get query = none at missing
      rw [GeneralBorrowFreshLocation.get_other _ index query _ different] at missing
      exact missing
    have clean := initial.vacant query original
    cases stored : location.perms.get index with
    | none => simpa only [weakenLocation,stored] using clean
    | some state => simpa only [weakenLocation,stored,GeneralBorrowFreshLocation.get_other _ index query _ different] using clean

/-- One real ancestor-SIFA weakening preserves every physical location profile,
including default SIFA and clean vacancies. -/
theorem weakened_profile (tree : BorrowTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (strongest : IdempotentForeignAccess)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    Every (fun location => Profile (weakened tree index node strongest) location protections)
      (weakened tree index node strongest).locations := by
  intro position valid
  have oldValid : position < tree.locations.entries.size := by
    simpa only [weakened,DedupRangeMap.modifyAll,Array.size_map] using valid
  have formedHere := weaken_location tree protections index node present strongest tree.locations.entries[position].data (initial position oldValid)
  have locationEq : (weakened tree index node strongest).locations.entries[position].data =
      weakenLocation tree.locations.entries[position].data index strongest := by
    simp only [weakened,DedupRangeMap.modifyAll,Array.getElem_map,weakenLocation]
    rfl
  rw [locationEq]
  exact ⟨formedHere.present,formedHere.vacant⟩

def Preserves (protections : ProtectedTags) (state : GeneralBorrowSifa.LoopState) : Prop :=
  Every (fun location => Profile state.2.1 location protections) state.2.1.locations ∧
    ∀ returned, state.1 = some returned → Every (fun location => Profile returned.1 location protections) returned.1.locations

def Measure (state : GeneralBorrowSifa.LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.nodes.size+1-state.2.2.2.1)+1 else 0

/-- The real ancestor-SIFA loop preserves physical profiles even on its
source error branches. Operation success is not assumed. -/
theorem sifa (tree : BorrowTree) (protections : ProtectedTags) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (formed : Every (fun location => Profile tree location protections) tree.locations) :
    Every (fun location => Profile (sourceUpdateSifa tree start strongest).1 location protections)
      (sourceUpdateSifa tree start strongest).1.locations := by
  unfold_source_sifa
  split
  · exact formed
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Preserves protections state →
        (∃ final, scan () state = .done final ∧ Preserves protections final) ∨
        ∃ next, scan () state = .yield next ∧ Preserves protections next ∧ Measure next < Measure state := by
      intro state preserved
      rcases state with ⟨returned,current,cursor,steps,active⟩
      have currentShape : Every (fun location => Profile current location protections) current.locations := preserved.1
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
              have nextShape : Every (fun location => Profile nextTree location protections) nextTree.locations :=
                weakened_profile current protections index node lookup strongest currentShape
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
    have initial : Preserves protections (none,tree,some start,0,true) := ⟨formed,by simp⟩
    have maintained := GeneralBorrowLoop.invariant scan Measure (Preserves protections) step _ initial
    cases actual : (Lean.Loop.forIn {} (none,tree,some start,0,true) scan).1 with
    | none => exact maintained.1
    | some returned => exact maintained.2 returned actual
end DuplicatePrefix.GeneralBorrowSifaProfileTransport
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSifaProfileTransport.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual SIFA profile transport dependency {dependency}"
