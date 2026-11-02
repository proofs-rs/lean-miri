import duplicate_prefix.RangeMapNonempty
import duplicate_prefix.GeneralBorrowLoop
import Miri.TreeBorrows.TreeState
namespace DuplicatePrefix.GeneralBorrowExposure
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
/-- Data-only ancestor validity and bounded descending depth. -/
structure ParentDepth (nodes : UniValMap TreeNode) where
  depth : UniIndex → Nat
  bounded : ∀ index node, nodes.get index = some node → depth index ≤ nodes.size
  parent : ∀ index node, nodes.get index = some node → ∀ before, node.parent = some before →
    ∃ earlier, nodes.get before = some earlier ∧ depth before < depth index

abbrev LoopState := ExposedCache × Option UniIndex × Nat × Except ExposedCacheError Unit × Bool

def Measure (depth : UniIndex → Nat) (state : LoopState) : Nat :=
  if state.2.2.2.2 then (state.2.1.map (fun index => depth index + 1)).getD 1 else 0

def Valid (nodes : UniValMap TreeNode) (depth : UniIndex → Nat) (state : LoopState) : Prop :=
  state.2.2.2.1 = .ok () ∧
    (state.2.2.2.2 = true → ∃ index node,
      state.2.1 = some index ∧ nodes.get index = some node ∧ state.2.2.1 + depth index ≤ nodes.size)

theorem update_exposure_succeeds (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (wellformed : ParentDepth nodes) (id : UniIndex) (node : TreeNode)
    (present : nodes.get id = some node) (oldLevel newLevel : WildcardAccessLevel) :
    (cache.updateExposure nodes id oldLevel newLevel).outcome = .ok () := by
  unfold ExposedCache.updateExposure
  split
  · rfl
  · simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step : ∀ state, Valid nodes wellformed.depth state →
        (∃ final, scan () state = .done final ∧ Valid nodes wellformed.depth final) ∨
        ∃ next, scan () state = .yield next ∧ Valid nodes wellformed.depth next ∧
          Measure wellformed.depth next < Measure wellformed.depth state := by
      intro state good
      rcases state with ⟨current,next,steps,outcome,active⟩
      rcases good with ⟨outcomeEq,live⟩
      dsimp only at outcomeEq
      subst outcome
      cases active with
      | false => exact .inl ⟨_,rfl,⟨rfl,by simp⟩⟩
      | true =>
        obtain ⟨index,currentNode,nextEq,lookup,bound⟩ := live rfl
        dsimp only at nextEq bound
        subst next
        have notPast : ¬ steps > nodes.size := by omega
        cases parentEq : currentNode.parent with
        | none =>
          have actual : ∃ updated, scan () (current,some index,steps,.ok (),true) =
              .yield (updated,none,steps+1,.ok (),false) := by
            refine ⟨?updated, ?actual⟩
            case actual =>
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup,parentEq,Option.isNone_none]
              rfl
          obtain ⟨updated,actual⟩ := actual
          refine .inr ⟨_,actual,⟨rfl,by simp⟩,?_⟩
          simp [Measure]
        | some before =>
          obtain ⟨earlier,earlierLookup,smaller⟩ := wellformed.parent index currentNode lookup before parentEq
          have actual : ∃ updated, scan () (current,some index,steps,.ok (),true) =
              .yield (updated,some before,steps+1,.ok (),true) := by
            refine ⟨?updated, ?actual⟩
            case actual =>
              simp only [scan,ite_eq_left rfl,ite_eq_right notPast,lookup,parentEq,Option.isNone_some]
              rfl
          obtain ⟨updated,actual⟩ := actual
          refine .inr ⟨_,actual,⟨rfl,?_⟩,?_⟩
          · intro active
            exact ⟨before,earlier,rfl,earlierLookup,by dsimp; omega⟩
          · simp only [Measure,↓reduceIte,Option.map_some,Option.getD_some]
            omega
    have initial : Valid nodes wellformed.depth (cache,some id,0,.ok (),true) :=
      ⟨rfl,fun _ => ⟨id,node,rfl,present,by simpa using wellformed.bounded id node present⟩⟩
    exact (GeneralBorrowLoop.invariant scan (Measure wellformed.depth) (Valid nodes wellformed.depth)
      step _ initial).1
end DuplicatePrefix.GeneralBorrowExposure

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowExposure." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general exposed-cache dependency {dependency}"
