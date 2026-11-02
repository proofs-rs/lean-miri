import duplicate_prefix.GeneralBorrowRootOnlyNormalCache
import duplicate_prefix.GeneralBorrowWriteActivationUnique
import duplicate_prefix.GeneralBorrowRangeProperty

namespace DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def StoredUnique (location : LocationTree) (root : UniIndex) : Prop :=
  ∃ state, location.perms.get root = some state ∧ state.permission = .Unique

theorem effective (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (stored : StoredUnique location root) (node : TreeNode) (state : LocationState)
    (present : tree.nodeAt root = some node) (found : tree.locationStateAt location root = some state) :
    state.permission = .Unique := by
  obtain ⟨old,oldStored,unique⟩ := stored
  have equal : state = old := by
    simpa only [BorrowTree.locationStateAt,present,oldStored,Option.getD_some,bind,pure,Option.bind,Option.some.injEq] using found.symm
  exact equal ▸ unique

/-- Unique root storage and the exact cache survive one actual normal root
Read or Write. All operational success follows from the supplied ownership. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (present : tree.nodeAt root = some node) (only : RootOnly tree root)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) root.toNat kind)
    (stored : StoredUnique location root) :
    StoredUnique (tree.performNormalAccessAt location root kind protections mode).location root ∧
    (tree.performNormalAccessAt location root kind protections mode).location.exposedCache = location.exposedCache := by
  refine ⟨?_,GeneralBorrowRootOnlyNormalCache.root_access tree location root kind protections mode only forest owned
    (effective tree location root stored)⟩
  cases kind with
  | Read =>
    apply GeneralBorrowReadUnique.normal_unique tree location protections root root node mode present stored
    intro event member same
    have selfPath : root.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath root.toNat := by
      have head := sourceAncestorHead (source_normal_projection tree location protections).topology
        (source_normal_projection tree location protections).topology.nodes.size root.toNat
      change ((source_normal_projection tree location protections).topology.ancestorPath root.toNat).head? = some root.toNat at head
      cases path : (source_normal_projection tree location protections).topology.ancestorPath root.toNat with
      | nil => simp only [path,List.head?_nil,reduceCtorEq] at head
      | cons first rest =>
        have equal : first = root.toNat := Option.some.inj (by simpa only [path,List.head?_cons] using head)
        simp only [List.mem_cons,equal,true_or]
    have relation := (GeneralBorrowTraversal.traversal_data (source_normal_projection tree location protections).topology
      forest root.toNat owned.anchorValid mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2 event member
    simpa only [same,ite_eq_left selfPath] using relation.2
  | Write =>
    apply GeneralBorrowWriteActivationUnique.normal tree location protections root mode forest owned
    intro state found
    have actual : tree.locationStateAt location root = some state := by
      rw [←projection_location_state tree location protections root node present]
      exact found
    rw [effective tree location root stored node state present actual]
    decide

/-- Exact cache/Unique storage predicate, usable on both initial and exposed
root-only histories without bounding the number of accesses. -/
def LocationInvariant (cache : ExposedCache) (root : UniIndex) (location : LocationTree) : Prop :=
  StoredUnique location root ∧ location.exposedCache = cache

/-- The actual range preparation, splitting, access and write-back preserve a
uniform exact cache and root Unique permission at every partition location. -/
theorem ranged (tree : BorrowTree) (tag : BorTag) (root : UniIndex) (node : TreeNode)
    (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (cache : ExposedCache) (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (present : tree.nodeAt root = some node) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (tagged : tree.indexOfTag tag = some root)
    (well : tree.locations.WellFormed) (only : RootOnly tree root)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections root kind) tree.locations)
    (initial : Every (LocationInvariant cache root) tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.performNormalAccessRange tag offset len kind protections mode).status = .Completed ∧
    Every (LocationInvariant cache root) (tree.performNormalAccessRange tag offset len kind protections mode).tree.locations := by
  have facts := GeneralBorrowRangeProperty.preserves (LocationInvariant cache root) tree protections tag root root
    offset len kind kind mode (fun same => same) fits depth children node present roots covered tagged well owned initial (by
      intro location good localOwned
      obtain ⟨⟨forest⟩,owner⟩ := localOwned
      have result := normal tree location root node kind protections mode present only forest owner good.1
      exact ⟨result.1,result.2.trans good.2⟩) bounds
  exact ⟨facts.1,facts.2.1⟩

end DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRootOnlyRangeCache." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root-only range-cache dependency {dependency}"
