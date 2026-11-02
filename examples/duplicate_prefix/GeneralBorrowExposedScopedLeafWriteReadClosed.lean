import duplicate_prefix.GeneralBorrowExposedScopedWriteClosedData
import duplicate_prefix.GeneralBorrowExposedScopedWriteClosedMap
import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadWrite
import duplicate_prefix.GeneralBorrowExposedScopedLeafSeed
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteReadClosed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) where
  write : GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write
  short : tree.nodes.size<65536
  leaves : ∀ index,area.support index→∃node,tree.nodeAt index=some node ∧ node.children=#[] ∧ node.isExposed=true
  positive : ∀ index,area.support index→0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write

noncomputable def initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : GeneralBorrowExposedScopedUniqueReadData.Data tree location protections anchor selected head tail support (fun _=>true)) :
    Data tree location protections anchor selected head tail := by
  refine ⟨GeneralBorrowExposedScopedUniqueReadWrite.write tree location protections anchor selected head tail support context data,
    data.short,data.leaves,?_⟩
  intro index member
  obtain ⟨node,present,leaf,exposed⟩:=data.leaves index member
  exact GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) data.base.base.coherent data.short index node present exposed .Write (by
      simp [GeneralBorrowExposureCardinality.effective,data.unique index member,GeneralBorrowWildcardLeaf.unique,
        GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite])

noncomputable def read (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : Data tree location protections anchor selected head tail) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Read := by
  have mixed : GeneralBorrowExposedScopedMixedRangeData.Mixed tree location protections anchor data.write.component.support (fun _=>true) := by
    intro position supported bound
    have size : (source_normal_projection tree location protections).locationStates.size=(source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    obtain ⟨state,present,permission⟩:=data.write.owned position supported (by rw [←size];exact bound)
    exact ⟨state,present,by simpa only [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,Bool.true_eq,ite_true] using permission⟩
  have result:=GeneralBorrowExposedScopedLeafSeed.seed tree location protections anchor selected head tail data.write.component.support (fun _=>true)
    context data.write.forest data.write.component rfl mixed data.write.rootPath data.write.hidden data.write.separate data.write.coherent data.short (by
      intro index member
      obtain ⟨node,present,leaf,exposed⟩:=data.leaves index member
      have compatible:=GeneralBorrowExposedKnownRootWriteState.local_compatible tree location location protections (fun _=>rfl)
        data.write.profile index node present member (by have positive:=data.positive index member;omega)
      have allows:=GeneralBorrowExposedConditionalWritePermissions.local_allows _ _ compatible
      refine ⟨node,present,leaf,exposed,?_,compatible.1⟩
      change GeneralBorrowExposureCardinality.supports
        ((GeneralBorrowWildcardVirtualLeaf.effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read=true
      cases level : ((GeneralBorrowWildcardVirtualLeaf.effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) <;>
        simp_all [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead,WildcardAccessLevel.allows])
    (by intro different;let primary:=data.write.primary different;exact primary.base.included head primary.base.rooted)
    (by intro root member different;let virtual:=data.write.virtual root member different;exact virtual.included root virtual.rooted)
  exact result.base

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (fits : tree.nodes.data.size≤4294967296) (data : Data tree location protections anchor selected head tail) :
    source_access_status (source_tree_access_at tree location (some anchor) .Write protections mode range)=none ∧
    Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) .Write protections mode range))
      protections anchor selected head tail) := by
  have closed:=GeneralBorrowExposedScopedWriteClosedData.access tree location protections anchor selected head tail mode range context fits data.write
  obtain ⟨after,actual,status,frame,profile,coherent,outside⟩:=GeneralBorrowExposedScopedWriteFrameAccess.access tree location protections
    anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.write.forest data.write.component data.write.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.write.rootPath data.write.hidden data.write.separate
    data.write.coherent data.write.profile context.tags data.write.primary data.write.virtual
  obtain ⟨next⟩:=closed.2
  refine ⟨closed.1,⟨next,data.short,data.leaves,?_⟩⟩
  intro index member
  rw [actual]
  have equal:=congrArg UInt16.toNat (frame index)
  change GeneralBorrowWildcardRelatednessBounds.count after.exposedCache index .Write=GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write at equal
  rw [equal]
  exact data.positive index member

private theorem nonempty_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) :
    Nonempty (Data tree location protections anchor selected head tail) ↔
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write) ∧
      tree.nodes.size<65536 ∧
      (∀ index,area.support index→∃node,tree.nodeAt index=some node ∧ node.children=#[] ∧ node.isExposed=true) ∧
      (∀ index,area.support index→0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write) := by
  constructor
  · rintro ⟨data⟩;exact ⟨⟨data.write⟩,data.short,data.leaves,data.positive⟩
  · rintro ⟨⟨write⟩,short,leaves,positive⟩;exact ⟨⟨write,short,leaves,positive⟩⟩

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) :
    Nonempty (Data {tree with locations:=map} location protections anchor selected head tail)=Nonempty (Data tree location protections anchor selected head tail) := by
  apply propext
  rw [nonempty_iff,nonempty_iff,GeneralBorrowExposedScopedWriteClosedMap.post_map]
  rfl
end DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteReadClosed
