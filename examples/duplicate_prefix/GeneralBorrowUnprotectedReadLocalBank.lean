import duplicate_prefix.GeneralBorrowUnprotectedReadOther
import duplicate_prefix.GeneralBorrowRangeLocalProperty

namespace DuplicatePrefix.GeneralBorrowUnprotectedReadLocalBank
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins

/-- A genuine ranged Read through one owner preserves the Read contracts of
an arbitrary bank of other anchors. Completion is derived from source ownership. -/
theorem preserves (tree : BorrowTree) (tag : BorTag) (source root : UniIndex)
    (targets : List UniIndex) (offset len : Size) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (node : TreeNode) (present : tree.nodeAt source = some node)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some source)
    (well : tree.locations.WellFormed)
    (lower upper : UInt64)
    (sourceOwned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} source .Read) lower upper tree.locations)
    (bank : ∀ target ∈ targets, OwnedOn (GeneralBorrowRange.LocationOwned tree {} target .Read) lower upper tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read {} mode
    result.status = .Completed ∧
      (∀ target ∈ targets, OwnedOn (GeneralBorrowRange.LocationOwned tree {} target .Read) lower upper result.tree.locations) ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  let predicate := fun location => ∀ target ∈ targets,
    GeneralBorrowRange.LocationOwned tree {} target .Read location
  have initial : OwnedOn predicate lower upper tree.locations := by
    intro index valid positive before after target member
    exact bank target member index valid positive before after
  have result := GeneralBorrowRangeLocalProperty.preserves predicate tree {} tag source root offset len .Read .Read mode
    (by intro; rfl) fits depth children node present roots covered tagPresent well lower upper sourceOwned initial
    (by
      intro location owns _ target member
      exact GeneralBorrowUnprotectedReadOther.location tree location source target mode fits (owns target member)) bounds requestLower requestUpper
  refine ⟨result.1,?_,result.2.2⟩
  intro target member index valid positive before after
  exact result.2.1 index valid positive before after target member
end DuplicatePrefix.GeneralBorrowUnprotectedReadLocalBank
