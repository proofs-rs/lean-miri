import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableReuseInstallation
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReuseConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutableReuse
open GeneralBorrowFreshMixedChild (extend)
open GeneralBorrowExposedScopedMixedShape (Mixed)
open GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual ProtectedMutable vacant-slot reuse preserves selected-component mixed ownership
on the requested slice. The reused slot is overwritten even if stale location
permissions remain there. No operation-success or outside ownership is assumed. -/
theorem reuse_owned (input : Input) (protections : ProtectedTags) (support : Nat → Prop)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree default protections).topology)
    (owned : OwnedOn (Mixed input.tree protections input.parent support (fun _=>true))
      input.offset (input.offset+input.len) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    OwnedOn (Mixed (result input) protections (index input)
      (fun position => support position ∨ position = (index input).toNat) (fun _=>true))
      input.offset (input.offset+input.len) (result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  rw [tree_eq input]
  apply GeneralBorrowExposedScopedMixedShape.sifa_preserves
  have installed := GeneralBorrowExposedScopedProtectedMutableReuseInstallation.reuse_ranged_owned input.tree (index input)
    input.parent input.parentNode input.newTag input.valid input.vacant fits input.parentPresent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds protections support forest owned
  change OwnedOn (Mixed (stage input) protections (index input)
    (fun position => support position ∨ position = (index input).toNat) (fun _=>true))
    input.offset (input.offset+input.len) (stage input).locations
  dsimp only [stage, GeneralBorrowFreshMetadataChildAttach.staged]
  intro position valid positive start stop
  rw [GeneralBorrowExposedScopedMixedShape.context_eq]
  rw [←GeneralBorrowExposedScopedMixedShape.map_eq]
  exact installed position valid positive start stop
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReuseConstructor
