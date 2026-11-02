import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultFromTargetRows
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem full_every (predicate : α→Prop) (map : DedupRangeMap α) (well : map.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 map.size.bytes map) : GeneralRangeMapState.Every predicate map := by
  intro position valid
  have facts:=GeneralRangeMapGeometry.facts map well (by omega)
  have lastValid : map.entries.size-1<map.entries.size:=by omega
  have lastPositive:=facts.2.1 (map.entries.size-1) lastValid
  have lastSize:=GeneralRangeMapGeometry.size_last map (by omega)
  have positive:=facts.2.1 position valid
  have startBound : map.entries[position].range.start.toNat<map.size.bytes.toNat := by
    rw [lastSize]
    by_cases same : position=map.entries.size-1
    · subst position;exact lastPositive
    · have before : position<map.entries.size-1:=by omega
      have separated:=GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) before lastValid
      omega
  exact owned position valid (by simp only [UInt64.toNat_zero];omega) startBound (by simp only [UInt64.toNat_zero];omega)

/-- Fixed-tree formation from restored mixed writable target rows. Full
allocation sampling supplies graph/component/profile/coherence resources;
no exact-Unique family, successful Default operation or final Raw is assumed. -/
theorem build (tree : BorrowTree) (protections : ProtectedTags) (target selected head : UniIndex)
    (tail : List UniIndex) (support : Nat→Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target=some targetNode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags tree)
    (offset len : UInt64) (nonzero : len≠0) (atBase : offset=0) (full : len=tree.locations.size.bytes)
    (well : tree.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedWritableReadData.Data tree location protections target selected head tail support (fun _=>true)))
      offset (offset+len) tree.locations)
    (certificates : GeneralBorrowFreshMetadataChildAttach.Certificates tree)
    (noFree : tree.tagMapping.deassigned.back?=none) (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size)
    (future : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping future)
    (room : tree.nodes.size+2<65536)
    (first : head≠selected→area.support head) (rest : ∀root∈tail,root≠selected→area.support root) :
    ∃data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data tree protections targetNode.tag future offset len selected head tail,
      data.input.parent=target ∧ data.input.offset=0 ∧ data.input.len=data.input.tree.locations.size.bytes := by
  have fullOwned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedWritableReadData.Data tree location protections target selected head tail support (fun _=>true)))
      0 tree.locations.size.bytes tree.locations := by
    simpa only [atBase,UInt64.zero_add,full] using owned
  have every:=full_every _ tree.locations well fullOwned
  have positive : 0<tree.locations.size.bytes.toNat := by
    rw [←full]
    have nz : len.toNat≠0:=by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    omega
  obtain ⟨position,valid,lower,upper⟩:=GeneralRangeMapGeometry.covered tree.locations well 0 positive
  obtain ⟨sample⟩:=every position valid
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
    offset:=offset,len:=len,nonzero:=nonzero,well:=well,bounds:=by rw [atBase,full];simp}
  let raw : GeneralBorrowExposedScopedWritableDefaultConstructor.Resources input protections selected head tail:={
    forest:=sample.base.base.forest,component:=component,
    selectedNode:=context.selectedNode,selectedPresent:=context.selectedPresent,roots:=context.roots,
    rootPath:=sample.base.base.rootPath,
    hidden:=by intro index node supported present;apply sample.base.base.hidden index node _ present;rw [sample.base.support_eq];exact supported,
    separate:=by intro index included supported;apply sample.base.base.separate index included;rw [sample.base.support_eq];exact supported,
    tags:=context.tags,leaves:=sample.leaves,
    writableLeaves:=by intro position valid;obtain ⟨data⟩:=every position valid;exact data.writableLeaves,
    first:=first,rest:=rest,
    coherent:=by intro position valid;obtain ⟨data⟩:=every position valid;exact data.base.base.coherent,
    owned:=by intro position valid positive start stop;obtain ⟨data⟩:=owned position valid positive start stop;exact data.base.mixed,
    room:=by change tree.nodes.size+1<65536;omega}
  exact ⟨⟨input,rfl,rfl,rfl,rfl,rfl,raw,nodeTags⟩,rfl,atBase,full⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultFromTargetRows
