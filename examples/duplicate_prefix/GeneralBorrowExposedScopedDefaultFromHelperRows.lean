import duplicate_prefix.GeneralBorrowExposedScopedSharedUniqueWriteRestore
import duplicate_prefix.GeneralBorrowExposedScopedMutableEntryRaw
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultFromHelperRows
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false

private theorem full_every (predicate : α → Prop) (map : DedupRangeMap α) (well : map.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 map.size.bytes map) : GeneralRangeMapState.Every predicate map := by
  intro position valid
  have facts:=GeneralRangeMapGeometry.facts map well (by omega)
  have lastValid : map.entries.size-1<map.entries.size := by omega
  have lastPositive:=facts.2.1 (map.entries.size-1) lastValid
  have lastSize:=GeneralRangeMapGeometry.size_last map (by omega)
  have positive:=facts.2.1 position valid
  have startBound : map.entries[position].range.start.toNat<map.size.bytes.toNat := by
    rw [lastSize]
    by_cases same : position=map.entries.size-1
    · subst position;exact lastPositive
    · have before : position<map.entries.size-1 := by omega
      have separation:=GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) before lastValid
      omega
  exact owned position valid (by simp only [UInt64.toNat_zero];omega) startBound (by simp only [UInt64.toNat_zero];omega)

theorem build (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (child expr target selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree child selected head tail)
    (targetNode exprNode childNode : TreeNode)
    (targetPresent : tree.nodeAt target=some targetNode) (exprPresent : tree.nodeAt expr=some exprNode)
    (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : ∀ index node,tree.nodeAt index=some node → tree.indexOfTag node.tag=some index)
    (exprUnheld : global.protectedTags.contains exprNode.tag=false)
    (paths : ∀ location : LocationTree,(source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat=
      child.toNat::expr.toNat::(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location : LocationTree,expr.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀ location : LocationTree,child.toNat∉(source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (offset len : UInt64) (nonzero : len≠0) (atBase : offset=0) (full : len=tree.locations.size.bytes)
    (well : tree.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedUniqueReadData.Data tree location global.protectedTags child selected head tail support
        (GeneralBorrowFreshSharedPrefix.labels expr child))) offset (offset+len) tree.locations)
    (certificates : GeneralBorrowFreshMetadataChildAttach.Certificates tree)
    (noFree : tree.tagMapping.deassigned.back?=none) (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size)
    (future : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping future)
    (room : tree.nodes.size+2<65536)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    let ended:=(global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags
    ∃ data : GeneralBorrowExposedScopedMutableEntryRaw.Data tree ended targetNode.tag future offset len selected head tail,
      data.input.parent=target ∧ data.input.offset=0 ∧ data.input.len=data.input.tree.locations.size.bytes := by
  let ended:=(global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags
  have fullOwned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedUniqueReadData.Data tree location global.protectedTags child selected head tail support
        (GeneralBorrowFreshSharedPrefix.labels expr child))) 0 tree.locations.size.bytes tree.locations := by
    simpa only [atBase,UInt64.zero_add,full] using owned
  have every:=full_every _ tree.locations well fullOwned
  have sizePositive : 0<tree.locations.size.bytes.toNat := by
    rw [←full]
    have nz : len.toNat≠0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    omega
  obtain ⟨position,valid,lower,upper⟩:=GeneralRangeMapGeometry.covered tree.locations well 0 sizePositive
  obtain ⟨sample⟩:=every position valid
  let targetContext : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail:={
    context with anchorNode:=targetNode,anchorPresent:=targetPresent }
  let written:=GeneralBorrowExposedScopedSharedUniqueWriteRestore.restore tree _ global allocation child expr target selected head tail support
    sample context targetNode exprNode childNode targetPresent exprPresent childPresent nodeTags exprUnheld paths exprOutside childOutside first rest
  have topology : (source_normal_projection tree tree.locations.entries[position].data global.protectedTags).topology=
      (source_normal_projection tree default ended).topology := by
    unfold_general_projection
    rfl
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree default ended).topology target.toNat:={
    support:=support
    anchor:=GeneralBorrowExposedScopedSharedWriteRestore.target_supported tree _ global.protectedTags child expr target selected head tail support _ sample.base (paths _)
    parents:=by rw [←topology];simpa only [sample.base.support_eq] using sample.base.base.component.parents
    children:=by rw [←topology];simpa only [sample.base.support_eq] using sample.base.base.component.children }
  let input : GeneralBorrowFreshMetadataChildDefault.Input:={
    tree:=tree,depth:=certificates.depth,children:=certificates.children,covered:=certificates.covered,
    parentTag:=targetNode.tag,newTag:=future,parent:=target,parentNode:=targetNode,
    parentTagPresent:=nodeTags target targetNode targetPresent,parentPresent:=targetPresent,fresh:=fresh,noFree:=noFree,aligned:=aligned,
    fits:=by rw [aligned];change tree.nodes.size≤4294967295;omega,
    offset:=offset,len:=len,nonzero:=nonzero,well:=well,bounds:=by rw [atBase,full];simp }
  have restoration:=GeneralBorrowFreshSharedPrefix.restore_data tree global (({} : FrameState).addProtector allocation childNode.tag)
    target expr child targetNode exprNode childNode targetPresent exprPresent childPresent allocation
    (by simp [FrameState.addProtector]) exprUnheld paths exprOutside childOutside
  let raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input ended selected head tail:={
    forest:=written.forest
    component:=component
    selectedNode:=targetContext.selectedNode,selectedPresent:=targetContext.selectedPresent,roots:=targetContext.roots,
    rootPath:=written.rootPath
    hidden:=by intro index node supported present;apply sample.base.base.hidden index node _ present;rw [sample.base.support_eq];exact supported
    separate:=by intro index included supported;apply sample.base.base.separate index included;rw [sample.base.support_eq];exact supported
    tags:=targetContext.tags,leaves:=sample.leaves,
    unique:=by intro query included position valid;obtain ⟨data⟩:=every position valid;exact data.unique query included,
    first:=first,rest:=rest,
    coherent:=by
      intro position valid
      obtain ⟨data⟩:=every position valid
      exact GeneralBorrowExposedScopedRestoredWriteData.coherent tree _ global allocation child selected head tail support
        (GeneralBorrowFreshSharedPrefix.labels expr child) data.base childNode childPresent nodeTags,
    owned:=by
      intro position valid positive start stop
      obtain ⟨data⟩:=owned position valid positive start stop
      exact GeneralBorrowExposedScopedRestore.location tree _ global.protectedTags ended (GeneralBorrowRelease.end_call_weakens global _)
        child target support (GeneralBorrowFreshSharedPrefix.labels expr child) restoration data.base.mixed,
    room:=by change tree.nodes.size+1<65536;omega }
  let data : GeneralBorrowExposedScopedMutableEntryRaw.Data tree ended targetNode.tag future offset len selected head tail:={
    input:=input,treeEq:=rfl,parentTagEq:=rfl,newTagEq:=rfl,offsetEq:=rfl,lenEq:=rfl,resources:=raw,nodeTags:=nodeTags }
  exact ⟨data,rfl,atBase,full⟩
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultFromHelperRows
