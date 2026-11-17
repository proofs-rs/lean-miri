import duplicate_prefix.GeneralBorrowExposedWildcardAccess
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowExposedWildcardStoredRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowWildcardVirtualLeaf
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Term in
elab "wildcard_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedWildcardAccess.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected unique source-bound exposed wildcard iterator"

/-- Existing permission rows eliminate even lazy materialization changes in
the actual positive wildcard Read; arbitrary protected supporting extra leaves
therefore keep their exact stored states as well as exposure counters. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (states : UniIndex → LocationState) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (present : tree.nodes.get primary = some primaryNode) (leaf : primaryNode.children = #[])
    (exposed : primaryNode.isExposed = true) (stored : location.perms.get primary = some unique)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      location.perms.get root = some (states root) ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) .Read = true) :
    source_access_location (source_tree_access_at tree location none .Read protections mode range) = location ∧
    source_access_status (source_tree_access_at tree location none .Read protections mode range) = none := by
  have support : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections primary primaryNode) .Read = true := by
    simp [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureCardinality.effective,stored,unique,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead]
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short primary primaryNode present exposed .Read support
  have first := GeneralBorrowExposedWildcardAccess.physical tree location primary primaryNode .Read protections present leaf exposed stored (Nat.ne_of_gt positive)
  have completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras location none .Read protections = ⟨location,.Completed⟩ := by
    have all : ∀ schedule : List UniIndex, (∀ root ∈ schedule, root ∈ extras) →
        GeneralBorrowWildcardVirtualLeafFold.run tree schedule location none .Read protections = ⟨location,.Completed⟩ := by
      intro schedule
      induction schedule with
      | nil => intro subset;rfl
      | cons root rest ih =>
        intro subset
        obtain ⟨present,leaf,exposed,stored,support⟩ := data root (subset root (by simp))
        have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
          (GeneralBorrowExposureCardinality.effective location protections) coherent short root (nodes root) present exposed .Read support
        have called := GeneralBorrowWildcardVirtualLeaf.either_access tree location root (nodes root) none .Read protections
          present leaf (Nat.ne_of_gt positive) rfl
        have materialized : materialized location root (nodes root) = location := by
          simp only [GeneralBorrowWildcardVirtualLeaf.materialized,UniValMap.orInsert,stored]
        rw [materialized] at called
        simpa only [GeneralBorrowWildcardVirtualLeafFold.run,called,beq_self_eq_true,ite_true] using
          ih (fun query member => subset query (by simp [member]))
    exact all extras (fun _ member => member)
  exact wildcard_iterator tree location location primary extras .Read protections mode range roots first completed

/-- Full positive homogeneous allocation: the real wildcard ranged Read
retains the exact tree, so all initial allocator/graph/cache resources remain
available to the ensuing constructor without post-access assumptions. -/
theorem ranged (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (states : UniIndex → LocationState) (capacity : UInt64) (nonzero : capacity ≠ 0)
    (locations : tree.locations = homogeneous capacity location)
    (roots : tree.roots = (primary::extras).toArray)
    (present : tree.nodes.get primary = some primaryNode) (leaf : primaryNode.children = #[])
    (exposed : primaryNode.isExposed = true) (stored : location.perms.get primary = some unique)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      location.perms.get root = some (states root) ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) .Read = true) :
    let read := tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ read.tree = tree := by
  have localAccess := access tree location protections primary primaryNode extras nodes states .VisitChildrenOfAccessed ⟨0,capacity⟩
    roots present leaf exposed stored coherent short data
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run,bind,pure,locations]
  rw [iter_mut_homogeneous_full capacity location nonzero]
  simp only [Array.size_singleton,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure,
    beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
  rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [localAccess.1,localAccess.2]
  constructor
  · trivial
  · cases tree
    simp_all [GeneralRangeMapState.replaced,homogeneous]
end DuplicatePrefix.GeneralBorrowExposedWildcardStoredRead
