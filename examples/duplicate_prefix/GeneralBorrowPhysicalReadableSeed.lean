import duplicate_prefix.GeneralBorrowPhysicalReadable
import duplicate_prefix.GeneralBorrowFullSharedSeed
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowPhysicalReadable
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Real allocation forms all per-location permission/SIFA bounds and clean
vacancies for every capacity/protector table, including the empty allocation. -/
theorem allocation (capacity : UInt64) (rootTag : BorTag) (protections : ProtectedTags) (unheld : protections.contains rootTag=false) :
    Every (fun location => Profile (BorrowTree.new rootTag (Size.ofBytes capacity)) location protections)
      (BorrowTree.new rootTag (Size.ofBytes capacity)).locations := by
  by_cases zero : capacity = 0
  · subst capacity
    intro position valid
    have impossible : position < 0 := by
      simpa only [BorrowTree.new,Id.run,bind,pure,DedupRangeMap.new,Size.ofBytes,beq_self_eq_true,ite_true,Array.size_empty] using valid
    omega
  · change Every (fun location => Profile (GeneralBorrowFullSharedSeed.tree capacity zero rootTag) location protections)
      (GeneralBorrowFullSharedSeed.tree capacity zero rootTag).locations
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    intro position valid
    have first : position = 0 := by change position < 1 at valid;omega
    subst position
    refine ⟨?_,?_⟩
    · intro query node present
      have bound := lookup_valid (⟨#[some (GeneralBorrowFullSharedSeed.node rootTag)]⟩ : UniValMap TreeNode) query node present
      have same : query = GeneralBorrowFullSharedSeed.root := index_injective _ _ (by change query.toNat = 0;change query.toNat < 1 at bound;omega)
      subst query
      change some (GeneralBorrowFullSharedSeed.node rootTag) = some node at present
      cases present
      simp [UniIndex.toNat,unheld,RangeMapNonempty.homogeneous,GeneralBorrowFullSharedSeed.root,UniValMap.get,GeneralBorrowWildcardLeaf.unique,GeneralBorrowProtectedReadInvariant.Readable,GeneralBorrowFullSharedSeed.location,GeneralBorrowFullSharedSeed.node,TreeNode.defaultLocationState,LocationState.possible,Permission.isUnique]
    · intro query missing
      have different : query.toNat ≠ 0 := by
        intro zeroIndex
        have same : query = GeneralBorrowFullSharedSeed.root := index_injective _ _ zeroIndex
        subst query
        change some (GeneralBorrowFullSharedSeed.node rootTag) = none at missing
        cases missing
      change GeneralBorrowFullSharedSeed.location.perms.get query = none
      simp [GeneralBorrowFullSharedSeed.location,UniValMap.get,different]

end DuplicatePrefix.GeneralBorrowPhysicalReadableSeed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowPhysicalReadableSeed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocation SIFA consistency dependency {dependency}"
