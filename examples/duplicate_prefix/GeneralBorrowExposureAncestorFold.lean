import duplicate_prefix.GeneralBorrowExposure
namespace DuplicatePrefix.GeneralBorrowExposureAncestorFold
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def supportsRead : WildcardAccessLevel → Bool
  | .None => false | .Read | .Write => true

def supportsWrite : WildcardAccessLevel → Bool
  | .Write => true | .None | .Read => false

def delta (value : UInt16) (before after : Bool) : UInt16 :=
  if !before && after then value+1 else if before && !after then value-1 else value

def point (cache : ExposedCache) (index : UniIndex) (before after : WildcardAccessLevel) : ExposedCache :=
  let old := (cache.nodes.get index).getD {}
  let updated : ExposedCacheNode := {
    localWrites := delta old.localWrites (supportsWrite before) (supportsWrite after)
    localReads := delta old.localReads (supportsRead before) (supportsRead after)
  }
  {cache with nodes := cache.nodes.insert index updated}

/-- A finite ancestor walk over actual present nodes, including the source. -/
def walk (nodes : UniValMap TreeNode) : Nat → UniIndex → List UniIndex
  | 0,_ => []
  | fuel+1,index => index :: match nodes.get index with
    | none => []
    | some node => match node.parent with
      | none => []
      | some parent => walk nodes fuel parent

/-- Source-exact ancestral update. Malformed graphs are not replaced by this
specification: explicit ParentDepth/presence derive actual source completion. -/
theorem update (cache : ExposedCache) (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (before after : WildcardAccessLevel) :
    cache.updateExposure nodes index before after =
      ⟨if before == after then cache else
        (walk nodes (nodes.size+1) index).foldl (fun current index => point current index before after) cache,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  split
  · rfl
  · rename_i unequal
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have run : ∀ fuel current cursor currentNode steps,
        nodes.get cursor = some currentNode → depth.depth cursor < fuel →
        steps+depth.depth cursor ≤ nodes.size →
        let result := Lean.Loop.forIn {} (current,some cursor,steps,.ok (),true) scan
        (result.1,result.2.2.2.1) =
          ((walk nodes fuel cursor).foldl (fun cache index => point cache index before after) current,.ok ()) := by
      intro fuel
      induction fuel with
      | zero => intro current cursor currentNode steps found bound;omega
      | succ fuel ih =>
        intro current cursor currentNode steps found bound room
        have notPast : ¬ steps > nodes.size := by omega
        rw [Lean.Loop.forIn_eq_of_monadTail]
        cases parent : currentNode.parent with
        | none =>
          have first : scan () (current,some cursor,steps,.ok (),true) =
              .yield (point current cursor before after,none,steps+1,.ok (),false) := by
            simp only [scan,show ¬steps>nodes.size from notPast,↓reduceIte,found,parent,Option.isNone_none]
            rfl
          simp only [first,bind]
          rw [Lean.Loop.forIn_eq_of_monadTail]
          simp only [scan,Bool.false_eq_true,↓reduceIte,bind,pure,walk,found,parent,List.foldl_cons,List.foldl_nil]
        | some earlier =>
          obtain ⟨earlierNode,earlierFound,smaller⟩ := depth.parent cursor currentNode found earlier parent
          have first : scan () (current,some cursor,steps,.ok (),true) =
              .yield (point current cursor before after,some earlier,steps+1,.ok (),true) := by
            simp only [scan,show ¬steps>nodes.size from notPast,↓reduceIte,found,parent,Option.isNone_some]
            rfl
          simp only [first,bind,walk,found,parent,List.foldl_cons]
          exact ih _ earlier earlierNode (steps+1) earlierFound (by omega) (by omega)
    have completed := run (nodes.size+1) cache index node 0 present (by have bounded := depth.bounded index node present;omega)
      (by simpa using depth.bounded index node present)
    exact congrArg (fun pair : ExposedCache × Except ExposedCacheError Unit =>
      (⟨pair.1,pair.2⟩ : ExposedCacheUpdate)) completed
end DuplicatePrefix.GeneralBorrowExposureAncestorFold
