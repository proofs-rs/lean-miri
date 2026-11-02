import duplicate_prefix.GeneralBorrowNodeUpdate
namespace DuplicatePrefix.GeneralBorrowSifa
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.RangeMapNonempty
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected actual SIFA helper {suffix}"
elab "sourceUpdateSifa" : term => return mkConst (← sourceHelper ".BorrowTree.updateSifaAfterRetag")
elab "unfold_source_sifa" : tactic => do
  let name := mkIdent (← sourceHelper ".BorrowTree.updateSifaAfterRetag")
  evalTactic (← `(tactic| unfold $name:ident))
abbrev LoopState := Option (BorrowTree × Except BorrowTree.ChildInsertError Unit) × BorrowTree × Option UniIndex × Nat × Bool

def weakened (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : BorrowTree :=
  {tree with
    locations := (tree.locations.modifyAll fun _ location =>
      match location.perms.get index with
      | none => location
      | some state => {location with perms := location.perms.insert index ({state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1})})
    nodes := tree.nodes.insert index
      ({node with defaultInitialSifa := (node.defaultInitialSifa.ensureNoStrongerThan strongest).1})}

def changed (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (strongest : IdempotentForeignAccess) : Bool := Id.run do
  let mut result := (node.defaultInitialSifa.ensureNoStrongerThan strongest).2
  for segment in tree.locations.iterAll do
    if let some state := segment.data.perms.get index then
      result := result || (state.idempotentForeignAccess.ensureNoStrongerThan strongest).2
  return result

def Good (depth : UniIndex → Nat) (state : LoopState) : Prop :=
  state.1 = none ∧ ∃ certificate : ParentDepth state.2.1.nodes,
    certificate.depth = depth ∧ state.2.2.2.1 ≤ state.2.1.nodes.size ∧
      (state.2.2.2.2 = true → ∀ index, state.2.2.1 = some index → ∃ node,
        state.2.1.nodes.get index = some node ∧ state.2.2.2.1 + depth index < state.2.1.nodes.size)

def Measure (depth : UniIndex → Nat) (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.2.1.map (fun index => depth index + 2)).getD 1 else 0

theorem succeeds (tree : BorrowTree) (depth : ParentDepth tree.nodes) (start : UniIndex)
    (node : TreeNode) (present : tree.nodes.get start = some node)
    (strict : depth.depth start < tree.nodes.size) (strongest : IdempotentForeignAccess) :
    (sourceUpdateSifa tree start strongest).2 = .ok () := by
  unfold_source_sifa
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Good depth.depth state →
        (∃ final, scan () state = .done final ∧ Good depth.depth final) ∨
        ∃ next, scan () state = .yield next ∧ Good depth.depth next ∧ Measure depth.depth next < Measure depth.depth state := by
      intro state good
      rcases state with ⟨returned,current,cursor,steps,active⟩
      rcases good with ⟨returnedEq,certificate,depthEq,stepsBound,live⟩
      dsimp only at returnedEq stepsBound
      subst returned
      cases active with
      | false => exact .inl ⟨_,rfl,⟨rfl,certificate,depthEq,stepsBound,by simp⟩⟩
      | true =>
        have notPast : ¬ steps > current.nodes.size := by omega
        cases cursor with
        | none =>
          refine .inr ⟨(none,current,none,steps,false),?_,⟨rfl,certificate,depthEq,stepsBound,by simp⟩,?_⟩
          · simp [scan,notPast]
          · simp [Measure]
        | some index =>
          obtain ⟨currentNode,lookup,strictBound⟩ := live rfl index rfl
          dsimp only at strictBound
          let nextNode := {currentNode with defaultInitialSifa := (currentNode.defaultInitialSifa.ensureNoStrongerThan strongest).1}
          let nextTree := weakened current index currentNode strongest
          let nextCertificate := update_depth current.nodes certificate index currentNode nextNode lookup rfl
          have nextDepth : nextCertificate.depth = depth.depth := depthEq
          have sameSize : nextTree.nodes.size = current.nodes.size := insert_existing_size current.nodes index currentNode nextNode lookup
          have parentPresent : ∀ before, currentNode.parent = some before → ∃ earlier,
              nextTree.nodes.get before = some earlier ∧ depth.depth before < depth.depth index := by
            intro before edge
            obtain ⟨earlier,earlierLookup,smaller⟩ := nextCertificate.parent index nextNode
              (insert_existing_get_same current.nodes index currentNode nextNode lookup) before edge
            rw [nextDepth] at smaller
            exact ⟨earlier,earlierLookup,smaller⟩
          cases actualChanged : changed current index currentNode strongest with
          | false =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,some index,steps,false) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,by simp⟩,?_⟩
            · rw [sameSize]; exact stepsBound
            · simp [Measure]
          | true =>
            have actual : scan () (none,current,some index,steps,true) = .yield (none,nextTree,currentNode.parent,steps+1,true) := by
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup]
              change (if changed current index currentNode strongest then _ else _) = _
              rw [actualChanged]
              rfl
            refine .inr ⟨_,actual,⟨rfl,nextCertificate,nextDepth,?_,?_⟩,?_⟩
            · dsimp only; rw [sameSize]; omega
            · intro active before edge
              obtain ⟨earlier,earlierLookup,smaller⟩ := parentPresent before edge
              exact ⟨earlier,earlierLookup,by dsimp; rw [sameSize]; omega⟩
            · cases parentEq : currentNode.parent with
              | none => simp [Measure]
              | some before =>
                have smaller := (parentPresent before parentEq).choose_spec.2
                simp only [Measure,↓reduceIte,Option.map_some,Option.getD_some]
                omega
    have initial : Good depth.depth (none,tree,some start,0,true) := by
      refine ⟨rfl,depth,rfl,by simp,?_⟩
      intro active index same
      have indexEq : index = start := Option.some.inj same.symm
      subst index
      exact ⟨node,present,by simpa using strict⟩
    have maintained := GeneralBorrowLoop.invariant scan (Measure depth.depth) (Good depth.depth) step _ initial
    rw [maintained.1]
end DuplicatePrefix.GeneralBorrowSifa

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowSifa." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic SIFA dependency {dependency}"
