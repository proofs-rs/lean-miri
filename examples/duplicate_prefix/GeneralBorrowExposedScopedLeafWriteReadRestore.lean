import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteReadClosed
import duplicate_prefix.GeneralBorrowExposedScopedWriteRestore
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteReadRestore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child target selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections child selected head tail)
    (targetNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (childPresent : tree.nodeAt child=some childNode) (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat) :
    GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections target selected head tail :=
  ⟨GeneralBorrowExposedScopedWriteRestore.restore tree location protections child target selected head tail data.write
    targetNode childNode targetPresent childPresent childUnheld paths,data.short,data.leaves,data.positive⟩

/-- Actual postcopy strengthening restores both raw callbacks at the older
original target. Positive Write counters and exposed supporting leaf metadata
survive the real copy; Read data is rebuilt through coherent support witnesses,
without an implication from arbitrary Write profiles to Read profiles. -/
theorem owned_on (tree : BorrowTree) (protections : ProtectedTags)
    (child target selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode childNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (childPresent : tree.nodeAt child=some childNode) (childUnheld : protections.contains childNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location protections).topology.ancestorPath child.toNat=
      child.toNat::(source_normal_projection tree location protections).topology.ancestorPath target.toNat)
    (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections child selected head tail)) lower upper tree.locations) :
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail) ∧
    (∀ kind,GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections target selected head tail kind)) lower upper tree.locations) := by
  let targetContext : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail :=
    {context with anchorNode:=targetNode,anchorPresent:=targetPresent}
  refine ⟨⟨targetContext⟩,?_⟩
  intro kind position valid positive beforeUpper afterLower
  obtain ⟨data⟩:=owned position valid positive beforeUpper afterLower
  let next:=restore tree _ protections child target selected head tail data targetNode childNode targetPresent childPresent childUnheld paths
  cases kind with
  | Read => exact ⟨GeneralBorrowExposedScopedLeafWriteReadClosed.read tree _ protections target selected head tail targetContext next⟩
  | Write => exact ⟨next.write⟩
end DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteReadRestore
