import duplicate_prefix.GeneralBorrowExposedScopedDefaultInstallation
import duplicate_prefix.GeneralBorrowFreshDefaultChild
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowExposedScopedMixedShape (Mixed)
open DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
/-- The actual Default mutable constructor completes and makes the fresh
child own precisely the requested slice. This is the concrete-parent,
append-index case; arbitrary ownership outside the slice is allowed. The
parent forest/ownership history is supplied by the explicit input contract. -/
theorem append_owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree default protections).topology)
    (owned : OwnedOn (Mixed tree protections parent support (fun _=>true))
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧
      OwnedOn (Mixed result.tree protections
        ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
        (fun position => support position ∨ position = (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat)
        (fun _=>true)) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshDefaultChild.append_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds,?_⟩
  rw [GeneralBorrowFreshDefaultChild.append_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    exact aligned
  apply GeneralBorrowExposedScopedMixedShape.sifa_preserves
  have installed := GeneralBorrowExposedScopedDefaultInstallation.append_ranged_owned tree index parent parentNode newTag
    atEnd parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections support forest owned
  intro position valid positive start stop
  rw [GeneralBorrowExposedScopedMixedShape.context_eq]
  rw [←GeneralBorrowExposedScopedMixedShape.map_eq]
  exact installed position valid positive start stop


end DuplicatePrefix.GeneralBorrowExposedScopedDefaultConstructor
