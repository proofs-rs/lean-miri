import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.GeneralBorrowGcForestEffectivePolicy
import duplicate_prefix.GeneralBorrowGcNodeMetadata

namespace DuplicatePrefix.GeneralBorrowGcSifaConsistency
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- FULL actual production GC preserves the COMPLETE physical permission/SIFA
profile, including vacant permission Clean, on arbitrary graphs/root arrays.
This data theorem includes error states and is NOT a successful-GC assertion.
No cache invariant, final profile, graph shape or operation success is assumed. -/
theorem collect (tree : BorrowTree) (protections : ProtectedTags) (live : Array BorTag)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    Every (fun location => Profile (tree.removeUnreachableTags live).tree location protections)
      (tree.removeUnreachableTags live).tree.locations := by
  let allowed := fun query state => ∀ node,tree.nodes.get query = some node →
    Consistent state (protections.contains node.tag)
  have seed : GeneralBorrowGcEffectivePolicy.Policy allowed tree := by
    constructor
    · intro query node present position valid old oldPresent
      have same := Option.some.inj (present.symm.trans oldPresent)
      subst old
      exact (initial position valid).present query node present
    · intro query missing position valid
      exact (initial position valid).vacant query missing
  have policy := GeneralBorrowGcForestEffectivePolicy.preserves allowed tree live seed
  have metadata := GeneralBorrowGcNodeMetadata.collect tree live
  intro position valid
  constructor
  · intro query node present
    obtain ⟨old,oldPresent,fields⟩ := metadata query node present
    have good := policy.live query node present position valid old oldPresent
    rw [fields.tag]
    exact good
  · intro query missing
    exact policy.vacant query missing position valid

end DuplicatePrefix.GeneralBorrowGcSifaConsistency
