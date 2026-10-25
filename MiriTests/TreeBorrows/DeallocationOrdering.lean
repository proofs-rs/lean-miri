import Miri.TreeBorrows.TreeState

open Miri.TreeBorrows
open Miri.ABI
open Miri.DataStructures
open Miri.Memory

private def tag : Nat → BorTag
  | 1 => BorTag.one
  | 2 => ⟨2, by decide⟩
  | 3 => ⟨3, by decide⟩
  | _ => BorTag.one

private def node (n : Nat) (parent : Option Nat) (children : Array Nat)
    (permission : Permission) (exposed : Bool := false) : TreeNode := {
  tag := tag n
  parent := parent.map fun i => ⟨UInt32.ofNat i⟩
  children := children.map fun i => ⟨UInt32.ofNat i⟩
  defaultInitialPermission := permission
  defaultInitialSifa := .None
  isExposed := exposed
}

private def makeTree (nodes : Array (Option TreeNode)) (roots : Array Nat)
    (tags : Array BorTag)
    (states : Array (Nat × Tree.LocationState))
    (exposures : Array (Nat × WildcardAccessLevel) := #[]) : BorrowTree := Id.run do
  let mut mapping : UniValMap TreeNode := {}
  let mut perms : UniValMap Tree.LocationState := {}
  let mut cache : ExposedCache := {}
  for i in [:nodes.size] do
    if let some (some n) := nodes[i]? then
      mapping := mapping.insert ⟨UInt32.ofNat i⟩ n
  for (i, state) in states do
    perms := perms.insert ⟨UInt32.ofNat i⟩ state
  for (i, level) in exposures do
    cache := (cache.updateExposure mapping ⟨UInt32.ofNat i⟩ .None level).cache
  let location : LocationTree := { perms, exposedCache := cache }
  return {
    tagMapping := { mapping := tags.mapIdx fun i t => (t, ⟨UInt32.ofNat i⟩), deassigned := #[] }
    nodes := mapping
    locations := DedupRangeMap.new (Size.ofBytes 1) location
    roots := roots.map fun i => ⟨UInt32.ofNat i⟩
  }

private def require (holds : Bool) (message : String) : IO Unit := do
  if !holds then throw (IO.userError message)

private def makeProtectors (tags : List Nat) : ProtectedTags :=
  tags.foldl (fun ps n => ps.insert (tag n) .StrongProtector) {}

private def dealloc (tree : BorrowTree) (provenance : ProvenanceExtra)
    (protectors : ProtectedTags) :=
  tree.deallocateBorrowRange provenance (Size.ofBytes 0) (Size.ofBytes 1) protectors

private def reports (result : BorrowTree.BorrowTreeDeallocResult) (index : Nat) : Bool :=
  match result.status with
  | BorrowTree.BorrowTreeDeallocStatus.ProtectedDealloc _ node => node.toNat == index
  | _ => false

def main : IO Unit := do
  let parentFirstTree := makeTree
    #[some (node 1 none #[1] .Unique), some (node 2 (some 0) #[] .Unique)]
    #[0] #[tag 1, tag 2] #[(0, ⟨.Unique, true, .None⟩), (1, ⟨.Unique, true, .None⟩)]
  let parentFirst := dealloc parentFirstTree (.concrete (tag 2)) (makeProtectors [1, 2])
  require (reports parentFirst 1)
    s!"concrete deallocation must report accessed tag before protected parent; got {repr parentFirst.status}"
  IO.println "concrete child-before-parent: ProtectedDealloc node=1"

  let cellTree := makeTree
    #[some (node 1 none #[1] .Unique), some (node 2 (some 0) #[] .Cell)]
    #[0] #[tag 1, tag 2] #[(0, ⟨.Unique, true, .None⟩), (1, ⟨.Cell, true, .None⟩)]
  let cellResult := dealloc cellTree (.concrete (tag 2)) (makeProtectors [1, 2])
  require (reports cellResult 0)
    s!"Cell protector must be skipped so accessed protected parent is reported; got {repr cellResult.status}"
  IO.println "Cell protector skipped: ProtectedDealloc parent-node=0"

  let unaccessedTree := makeTree
    #[some (node 1 none #[1, 2] .Unique),
      some (node 2 (some 0) #[] .Unique),
      some (node 3 (some 0) #[] .Unique)]
    #[0] #[tag 1, tag 2, tag 3]
    #[(0, ⟨.Unique, true, .None⟩), (1, ⟨.Unique, true, .None⟩),
      (2, ⟨.Unique, false, .Write⟩)]
  let unaccessedResult := dealloc unaccessedTree (.concrete (tag 2)) (makeProtectors [3])
  require (unaccessedResult.status == .Deallocated)
    s!"strong protector whose location was not accessed must not block deallocation; got {repr unaccessedResult.status}"
  IO.println "unaccessed strong protector skipped: Deallocated"

  let rootsTree := makeTree
    #[some (node 1 none #[] .Unique true),
      some (node 2 none #[] .Unique true),
      some (node 3 none #[] .Cell true)]
    #[0, 1, 2] #[tag 1, tag 2, tag 3]
    #[(0, ⟨.Unique, true, .None⟩), (1, ⟨.Unique, true, .None⟩),
      (2, ⟨.Cell, true, .None⟩)]
    #[(0, .Write), (1, .Write), (2, .Write)]
  let rootsResult := dealloc rootsTree .wildcard (makeProtectors [1, 2, 3])
  require (reports rootsResult 1)
    s!"wildcard deallocation must scan other roots in reverse order and skip Cell; got {repr rootsResult.status}"
  IO.println "wildcard reverse roots with final Cell skipped: ProtectedDealloc node=1"
  IO.println "Tree Borrows deallocation ordering regressions passed"
