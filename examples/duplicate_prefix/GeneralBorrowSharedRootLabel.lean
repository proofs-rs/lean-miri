import duplicate_prefix.GeneralBorrowFreshReleaseMixed
import duplicate_prefix.GeneralBorrowFreshMixedChild

namespace DuplicatePrefix.GeneralBorrowSharedRootLabel
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowAnchor

def writable (root : UniIndex) (position : Nat) : Bool := decide (position = root.toNat)

/-- A root-only mutable label can be transferred between readable anchors
whose real ancestor paths both contain the original root. -/
theorem transfer (tree : BorrowTree) (location : LocationTree) (root source target : UniIndex)
    (sourceMixed : Mixed tree {} source (writable root) location)
    (targetRead : GeneralBorrowRange.LocationOwned tree {} target .Read location)
    (sourcePath : root.toNat ∈ (source_normal_projection tree location {}).topology.ancestorPath source.toNat)
    (targetPath : root.toNat ∈ (source_normal_projection tree location {}).topology.ancestorPath target.toNat) :
    Combined tree {} target (writable root) location := by
  refine ⟨targetRead,?_⟩
  intro position valid
  by_cases same : position = root.toNat
  · subst position
    obtain ⟨state,present,permission⟩ := sourceMixed root.toNat valid
    refine ⟨state,present,?_⟩
    simpa only [relation,sourcePath,targetPath,↓reduceIte] using permission
  · obtain ⟨state,present,permission⟩ := targetRead.2.permissions position (by rw [←targetRead.2.locationsAligned];exact valid)
    refine ⟨state,present,?_⟩
    simpa [Required,writable,same] using permission

/-- Shared insertion changes only its genuinely fresh label, so it retains the
root-only label function whenever its slot differs from the original root. -/
theorem extend (root : UniIndex) (index : Nat) (different : index ≠ root.toNat) :
    GeneralBorrowFreshMixedChild.extend (writable root) index = writable root := by
  funext position
  by_cases same : position = index
  · subst position
    simp [GeneralBorrowFreshMixedChild.extend,writable,different]
  · simp [GeneralBorrowFreshMixedChild.extend,same]
end DuplicatePrefix.GeneralBorrowSharedRootLabel
