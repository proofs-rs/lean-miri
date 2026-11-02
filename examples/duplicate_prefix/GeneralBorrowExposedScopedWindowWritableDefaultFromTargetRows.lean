import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableDefaultFromTargetRows
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Fixed-tree formation from restored mixed writable target rows. A row in the requested
window supplies graph/component resources; separately preserved global profiles
and coherence supply the constructor metadata;
no exact-Unique family, successful Default operation or final Raw is assumed. -/
theorem build (tree : BorrowTree) (protections : ProtectedTags) (target selected head : UniIndex)
    (tail : List UniIndex) (support : Nat→Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags tree)
    (offset len : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (well : tree.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedWritableReadData.Data tree location protections target selected head tail support (fun _=>true)))
      offset (offset+len) tree.locations)
    (globals : GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧
      GeneralBorrowSifaWritableFrame.Profile tree protections area.support location) tree.locations)
    (certificates : GeneralBorrowFreshMetadataChildAttach.Certificates tree)
    (noFree : tree.tagMapping.deassigned.back?=none) (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size)
    (future : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping future)
    (room : tree.nodes.size+2<65536)
    (first : head≠selected→area.support head) (rest : ∀root∈tail,root≠selected→area.support root) :
    ∃data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data tree protections targetNode.tag future offset len selected head tail,
      data.input.parent=target ∧ data.input.offset=offset ∧ data.input.len=len := by
  have nonzeroNat : len.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
  have cap : tree.locations.size.bytes.toNat<2^64 := UInt64.toNat_lt_size _
  have sum : (offset+len).toNat=offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : offset.toNat+len.toNat<2^64)]
  obtain ⟨position,valid,lower,upper⟩:=GeneralRangeMapGeometry.covered tree.locations well offset (by omega)
  obtain ⟨sample⟩:=owned position valid (by rw [sum];omega) (by rw [sum];omega) upper
  have topology : (source_normal_projection tree tree.locations.entries[position].data protections).topology=
      (source_normal_projection tree default protections).topology := by unfold_general_projection;rfl
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree default protections).topology target.toNat:={
    support:=support
    anchor:=by rw [←sample.base.support_eq];exact sample.base.base.component.anchor
    parents:=by rw [←topology];simpa only [sample.base.support_eq] using sample.base.base.component.parents
    children:=by rw [←topology];simpa only [sample.base.support_eq] using sample.base.base.component.children}
  let input : GeneralBorrowFreshMetadataChildDefault.Input:={
    tree:=tree,depth:=certificates.depth,children:=certificates.children,covered:=certificates.covered,
    parentTag:=targetNode.tag,newTag:=future,parent:=target,parentNode:=targetNode,
    parentTagPresent:=nodeTags target targetNode targetPresent,parentPresent:=targetPresent,fresh:=fresh,noFree:=noFree,aligned:=aligned,
    fits:=by rw [aligned];change tree.nodes.size≤4294967295;omega,
    offset:=offset,len:=len,nonzero:=nonzero,well:=well,bounds:=bounds}
  let raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail:={
    forest:=sample.base.base.forest,component:=component,
    selectedNode:=context.selectedNode,selectedPresent:=context.selectedPresent,roots:=context.roots,
    rootPath:=sample.base.base.rootPath,
    hidden:=by intro index node supported present;apply sample.base.base.hidden index node _ present;rw [sample.base.support_eq];exact supported,
    separate:=by intro index included supported;apply sample.base.base.separate index included;rw [sample.base.support_eq];exact supported,
    tags:=context.tags,leaves:=sample.leaves,
    writableLeaves:=by intro position valid;exact (globals position valid).2,
    first:=first,rest:=rest,
    coherent:=by intro position valid;exact (globals position valid).1,
    owned:=by intro position valid positive start stop;obtain ⟨data⟩:=owned position valid positive start stop;exact data.base.mixed,
    room:=by change tree.nodes.size+1<65536;omega}
  exact ⟨⟨input,rfl,rfl,rfl,rfl,rfl,raw,nodeTags⟩,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableDefaultFromTargetRows
