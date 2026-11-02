import duplicate_prefix.GeneralBorrowForestGeneratedSifaHistory
import duplicate_prefix.GeneralBorrowRangeSifaConsistency
import duplicate_prefix.GeneralBorrowProtectorReleaseSifaProfile
namespace DuplicatePrefix.GeneralBorrowForestGeneratedReadReleaseData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapOrigins
set_option autoImplicit false in
structure ReadData (state : Snapshot) (tag : BorTag) (offset len : Size) where
  anchor : UniIndex
  node : TreeNode
  root : UniIndex
  tagged : state.tree.indexOfTag tag=some anchor
  present : state.tree.nodeAt anchor=some node
  roots : state.tree.roots=#[root]
  lower : UInt64
  upper : UInt64
  owned : OwnedOn (GeneralBorrowRange.LocationOwned state.tree state.global.protectedTags anchor .Read) lower upper state.tree.locations
  requestLower : lower.toNat≤offset.bytes.toNat
  requestUpper : (offset.bytes+len.bytes).toNat≤upper.toNat

set_option autoImplicit false in
structure ReleaseData (state : Snapshot) where
  tag : BorTag
  frame : FrameState
  last : state.frames.back?=some (tag,frame)
  anchor : UniIndex
  node : TreeNode
  root : UniIndex
  tagged : state.tree.indexOfTag node.tag=some anchor
  sameTag : node.tag=tag
  present : state.tree.nodeAt anchor=some node
  roots : state.tree.roots=#[root]
  ownerKind : AccessKind
  lower : UInt64
  upper : UInt64
  positive : lower.toNat<upper.toNat
  active : GeneralBorrowFreshActiveWithin.ActiveWithin state.tree anchor ownerKind lower upper
  owned : OwnedOn (GeneralBorrowRange.LocationOwned state.tree state.global.protectedTags anchor ownerKind) lower upper state.tree.locations

/-- Raw slice permission/graph/activity checks for real concrete Reads and
real protector release. Physical SIFA and operation completion are not guards.
Counter allocation, registration and GC remain the identical generated steps. -/
def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedTagHistoryData.Applicable state event ∧ match event with
  | .access (.concrete tag) offset len .Read _ => Nonempty (ReadData state tag offset len)
  | .release => Nonempty (ReleaseData state)
  | .access .. => False
  | _ => GeneralBorrowForestGeneratedSifaHistory.Applicable state event
end DuplicatePrefix.GeneralBorrowForestGeneratedReadReleaseData
