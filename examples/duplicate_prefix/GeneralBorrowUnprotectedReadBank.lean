import duplicate_prefix.GeneralBorrowUnprotectedReadOther
import duplicate_prefix.GeneralBorrowRangeProperty

namespace DuplicatePrefix.GeneralBorrowUnprotectedReadBank
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState

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
    (sourceOwned : Every (GeneralBorrowRange.LocationOwned tree {} source .Read) tree.locations)
    (bank : ∀ target ∈ targets, Every (GeneralBorrowRange.LocationOwned tree {} target .Read) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read {} mode
    result.status = .Completed ∧
      (∀ target ∈ targets, Every (GeneralBorrowRange.LocationOwned tree {} target .Read) result.tree.locations) ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  let predicate := fun location => ∀ target ∈ targets,
    GeneralBorrowRange.LocationOwned tree {} target .Read location
  have initial : Every predicate tree.locations := by
    intro index valid target member
    exact bank target member index valid
  have result := GeneralBorrowRangeProperty.preserves predicate tree {} tag source root offset len .Read .Read mode
    (by intro; rfl) fits depth children node present roots covered tagPresent well sourceOwned initial
    (by
      intro location owns _ target member
      exact GeneralBorrowUnprotectedReadOther.location tree location source target mode fits (owns target member)) bounds
  refine ⟨result.1,?_,result.2.2⟩
  intro target member index valid
  exact result.2.1 index valid target member
end DuplicatePrefix.GeneralBorrowUnprotectedReadBank
