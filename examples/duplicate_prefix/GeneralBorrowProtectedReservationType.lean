import duplicate_prefix.GeneralBorrowDefaultReservationType
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowProtectedReservationType
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowDefaultReservationType
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace Append
open GeneralBorrowFreshMetadataChildMutable
/-- The real reservation tree has reserved defaults and stored child states. -/
theorem formed (input : Input)
    (clean : Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    TreeTyped (result input) (index input) := by
  have typed := modified input.tree.locations (index input) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    GeneralBorrowFreshChild.inside input.well input.bounds (clean_typed _ _ clean) (by change (Permission.ReservedFrz false) = .ReservedFrz false;decide)
  have freshNode : (stage input).nodeAt (index input) = some (GeneralBorrowFreshChild.child input.newTag input.parent) := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using
      GeneralBorrowFreshGraph.new_lookup input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshChild.child input.newTag input.parent) (at_end input) input.parentPresent
  apply shape_preserves (stage input) (result input) (shape input) (index input)
  refine ⟨?_,typed⟩
  intro node present
  have same : node = GeneralBorrowFreshChild.child input.newTag input.parent := Option.some.inj (present.symm.trans freshNode)
  rw [same]
  change (Permission.ReservedFrz false) = .ReservedFrz false
  decide
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildMutableReuse

theorem formed (input : Input)
    (clean : Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    TreeTyped (result input) (index input) := by
  have typed := modified input.tree.locations (index input) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    GeneralBorrowFreshChild.inside input.well input.bounds (clean_typed _ _ clean) (by change (Permission.ReservedFrz false) = .ReservedFrz false;decide)
  have freshNode : (stage input).nodeAt (index input) = some (GeneralBorrowFreshChild.child input.newTag input.parent) := by
    simpa only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,index] using
      GeneralBorrowFreshMetadataChildReuseGraph.new_lookup input.tree input.index input.parent input.parentNode
        (GeneralBorrowFreshChild.child input.newTag input.parent) input.vacant input.parentPresent
  apply shape_preserves (stage input) (result input) (shape input) (index input)
  refine ⟨?_,typed⟩
  intro node present
  have same : node = GeneralBorrowFreshChild.child input.newTag input.parent := Option.some.inj (present.symm.trans freshNode)
  rw [same]
  change (Permission.ReservedFrz false) = .ReservedFrz false
  decide
end Reuse
end DuplicatePrefix.GeneralBorrowProtectedReservationType
