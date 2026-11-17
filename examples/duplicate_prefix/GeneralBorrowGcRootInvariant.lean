import duplicate_prefix.GeneralBorrowGcRangeClean
namespace DuplicatePrefix.GeneralBorrowGcRootInvariant
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcRangeClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open Lean Elab Term in
elab "gc_root_children" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.removeUselessChildren" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected pinned GC child walker"

/-- Compose preservation for each real root walk and real GC postprocessing.
Error outcomes are included as data states, without a successful-GC claim. -/
theorem preserves (P : BorrowTree → Prop) (tree : BorrowTree) (liveTags : Array BorTag)
    (initial : P tree)
    (children : ∀ current root, P current → P (gc_root_children current root liveTags).tree)
    (finish : ∀ current, P current →
      let normalized := {current with locations := current.locations.modifyAll (fun _ location => gc_source_trim_location location)}
      P {normalized with locations := normalized.locations.mergeAdjacentThorough.state}) :
    P (tree.removeUnreachableTags liveTags).tree := by
  unfold BorrowTree.removeUnreachableTags
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  let property := fun state : Option BorrowTree.TreeGcResult × BorrowTree =>
    P state.2 ∧ ∀ result, state.1 = some result → P result.tree
  have step : ∀ root ∈ tree.roots.toList, ∀ state, property state → property (scan root state).value := by
    intro root _ state good
    rcases state with ⟨returned,current⟩
    have nextGood := children current root good.1
    cases outcome : (gc_root_children current root liveTags).outcome with
    | error error =>
      have preserved : property (some {tree := (gc_root_children current root liveTags).tree,outcome := .error error},
          (gc_root_children current root liveTags).tree) :=
        ⟨nextGood,fun result equal => by cases equal;exact nextGood⟩
      simpa only [scan,outcome,ForInStep.value] using preserved
    | ok unit =>
      cases unit
      have preserved : property (none,(gc_root_children current root liveTags).tree) := ⟨nextGood,by simp⟩
      simpa only [scan,outcome,ForInStep.value] using preserved
  have start : property (none,tree) := ⟨initial,by simp⟩
  have final := GeneralBorrowLoop.list_invariant tree.roots.toList scan property step (none,tree) start
  cases returned : (forIn tree.roots.toList (none,tree) scan).1 with
  | some result => exact final.2 result returned
  | none =>
    simp only [returned]
    have post := finish (forIn tree.roots.toList (none,tree) scan).2 final.1
    split <;> exact post
end DuplicatePrefix.GeneralBorrowGcRootInvariant
