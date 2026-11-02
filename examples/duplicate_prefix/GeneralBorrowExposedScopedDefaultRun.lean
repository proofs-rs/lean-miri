import duplicate_prefix.GeneralBorrowExposedScopedMixedClosedRange
import duplicate_prefix.GeneralBorrowExposedScopedDefaultConstructor
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultRun
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedMixedRangeData (Data)
open GeneralBorrowExposedScopedMixedShape (Mixed)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real scoped parent Read followed by the real Default mutable
append constructor, from initial graph, cache and slice ownership resources. -/
theorem append (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent selected head : UniIndex) (tail : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree parent selected head tail)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree default protections).topology)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none) (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (support : Nat → Prop) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent selected head tail support (fun _=>true)))
      offset (offset+len) tree.locations) :
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    read.status = .Completed ∧ child.outcome = .ok () ∧
      GeneralRangeMapOrigins.OwnedOn (Mixed child.tree protections ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
        (fun position => support position ∨ position = (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat)
        (fun _=>true))
        offset (offset+len) child.tree.locations := by
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
  have nodeFits : tree.nodes.data.size ≤ 4294967296 := by omega
  have good := GeneralBorrowExposedScopedMixedClosedRange.access tree protections parentTag parent selected head tail
    (Size.ofBytes offset) (Size.ofBytes len) mode context support (fun _=>true) nodeFits tagPresent well offset (offset+len)
    owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
  change read.tree = {tree with locations := read.tree.locations} at frame
  have nodes : read.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : read.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := GeneralBorrowFreshReadFrame.depth_on tree read.tree nodes context.depth
  have mixed : GeneralRangeMapOrigins.OwnedOn (Mixed read.tree protections parent support (fun _=>true)) offset (offset+len) read.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := good.2.1 position valid positive lower upper
    exact data.mixed
  have result := GeneralBorrowExposedScopedDefaultConstructor.append_owned read.tree depth parentTag newTag parent context.anchorNode
    (by rw [frame];exact tagPresent) (by rw [frame];exact context.anchorPresent)
    (by rw [mapping];exact fresh) (by rw [mapping];exact noFree) (by rw [mapping,nodes];exact aligned)
    (by rw [mapping];exact fits) offset len nonzero good.2.2.1
    (by rw [good.2.2.2];exact bounds) protections support (by rw [frame];exact forest) mixed
  exact ⟨good.1,result.1,by simpa only [mapping] using result.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultRun
