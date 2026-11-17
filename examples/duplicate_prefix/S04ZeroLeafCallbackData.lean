import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry
import duplicate_prefix.S04ZeroSifaAuthorization

namespace DuplicatePrefix.S04ZeroLeafCallbackData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A vacant physical node index has no exposed descendants or residual
contribution, regardless of permission storage or the finite removal set. -/
theorem vacant_count (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (query : UniIndex)
    (vacant : tree.nodes.get query = none) (kind : AccessKind) (removed : List UniIndex) :
    residualCount tree location protections kind removed query = 0 := by
  apply List.length_eq_zero_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨contributed,retained⟩ := List.mem_filter.mp member
  obtain ⟨listed,contributed⟩ := List.mem_filter.mp contributed
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp listed
  have walked : query ∈ walk tree.nodes (tree.nodes.size+1) row.1 := by
    simp only [contributes,Bool.and_eq_true] at contributed
    exact List.contains_iff_mem.mp contributed.2
  obtain ⟨⟨node,found⟩,_⟩ := GeneralBorrowExposureAncestorDistinct.present_depth tree.nodes depth
    (tree.nodes.size+1) row.1 row.2 present query walked
  rw [vacant] at found
  cases found

/-- A primary callback retains its eligible witness under every legal mask;
a later root additionally has a virtual foreign alternative. -/
theorem total_positive (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind support)
    (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    0 < residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
  by_cases primary : position = 0
  · obtain ⟨witness,node,inside,present,eligible⟩ := old.witness primary
    have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (old.covers witness inside)
    have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal
      root witness node present eligible path
    simpa [primary] using positive
  · have virtual : (position != 0) = true := by simp [primary]
    simp only [virtual,ite_true]
    omega

/-- Zero local alternatives and a nonempty global/virtual choice make the
actual numeric classifier foreign, including the above-cutoff branch. -/
theorem zero_foreign (rootCount : Nat) (virtual onlyForeign : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount 0 virtual onlyForeign = some .ForeignAccess := by
  cases virtual <;> cases onlyForeign <;> by_cases zero : rootCount = 0 <;>
    simp_all [classify]


/-- An untouched zero-extent reservation is safe for both callback kinds and
either protector bit under the foreign classification derived above. -/
theorem foreign_authorized (kind : AccessKind) (held : Bool) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized ⟨.ReservedFrz false,false,.None⟩ kind held
      (some .ForeignAccess) (some .ForeignAccess) := by
  cases kind <;> cases held <;> simplify_reset

end DuplicatePrefix.S04ZeroLeafCallbackData
