import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSkipFrame
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadClosed
import duplicate_prefix.GeneralBorrowSparseExposedLeafState
import duplicate_prefix.GeneralBorrowExposedScopedLeafData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSkipAccessClosed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedScopedInactiveWritableAccessData (Data)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (kind : AccessKind) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat→Prop) (fits : tree.nodes.data.size≤4294967296)
    (data : Data tree location protections anchor selected head tail support) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range)=none ∧
    Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range))
      protections anchor selected head tail support) := by
  have result:=GeneralBorrowExposedScopedInactiveWritableSkipFrame.frame tree location protections anchor selected head tail kind range context support data
  let after:=source_access_location (source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range)
  let normal:=(tree.performNormalAccessAt location anchor kind protections .SkipChildrenOfAccessed).location
  have cache : after.exposedCache=location.exposedCache:=result.2.1
  have coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections:=result.2.2.2.1
  have outside : ∀query,¬area.support query→after.perms.get query=normal.perms.get query:=result.2.2.2.2
  have readable : GeneralBorrowExposedKnownRootState.Readable tree after protections := by
    apply GeneralBorrowExposedScopedLeafData.readable tree after protections coherent data.short
    intro index node included present
    obtain ⟨actual,found,leaf,exposed⟩:=data.leaves index included
    have same:=Option.some.inj (found.symm.trans present)
    subst actual
    have good:=result.2.2.1 index node included present
    exact ⟨exposed,GeneralBorrowSparseExposedLeafState.supports _ _ good .Read,good.1⟩
  have mixed : GeneralBorrowExposedScopedInactiveMixedRangeData.Mixed tree after protections anchor support (fun _=>true) := by
    have sizes:=GeneralBorrowProjection.projection_sizes tree location protections
    have topologySize : (source_normal_projection tree location protections).topology.nodes.size=tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    have valid : anchor.toNat<(source_normal_projection tree location protections).topology.nodes.size := by
      rw [topologySize];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor context.anchorNode context.anchorPresent
    have initial : GeneralBorrowExposedScopedOwnership.Pointwise data.base.base.component.support (source_normal_projection tree location protections)
        (fun _=>true) (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
      rw [data.base.support_eq];exact data.base.mixed
    have normalMixed:=GeneralBorrowExposedScopedOwnership.access_mixed tree location protections anchor kind .SkipChildrenOfAccessed (fun _=>true)
      fits data.base.base.forest valid (sizes.1.trans topologySize.symm) data.base.base.component initial (by intro index member bound impossible;cases impossible)
    have kept:=GeneralBorrowExposedScopedOwnership.row_frame tree normal after protections data.base.base.component.support (fun _=>true)
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) fits normalMixed
      (fun index member=>outside index (fun included=>data.base.base.separate index included member))
    rw [data.base.support_eq] at kept
    exact kept
  have exposures : GeneralBorrowExposedInactiveConstructor.Profile tree after anchor support := by
    intro query node member present exposed
    have inside : data.base.base.component.support query.toNat := by rw [data.base.support_eq];exact member
    have separate : ¬area.support query := by intro included;exact data.base.base.separate query included inside
    have same:=outside query separate
    have stored : tree.locationStateAt normal query=some ((after.perms.get query).getD node.defaultLocationState) := by
      simp only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,same]
    exact GeneralBorrowExposedScopedInactiveExposurePermission.preserves tree location protections anchor kind .SkipChildrenOfAccessed
      data.base.base.forest data.base.base.component (GeneralBorrowExposedScopedInactiveWritableAccessData.owned data kind)
      context.depth context.children context.anchorNode context.anchorPresent data.base.base.ancestors query node _ inside present exposed stored
  have base:=GeneralBorrowExposedScopedInactiveMixedRebase.rebase data.base after (by intro query;rw [cache]) coherent readable exposures mixed
  exact ⟨result.1,⟨base,data.short,data.leaves,result.2.2.1⟩⟩

end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSkipAccessClosed
