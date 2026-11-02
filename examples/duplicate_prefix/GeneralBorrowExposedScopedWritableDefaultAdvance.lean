import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultConstructor
import duplicate_prefix.GeneralBorrowFreshDefaultGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultAdvance
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedWritableDefaultConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Shared construction re-forms the allocator and graph/permission resources
for the next actual shared helper entry. The fresh next tag and node room are
initial raw resources; every post-constructor field is derived. -/
theorem advance (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) :
    ∃ next : Input, next.tree = result input ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : Resources next protections selected head tail,
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  let metadata := GeneralBorrowFreshMetadataChildDefault.append input
  let child := result input
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedWritableDefaultConstructor.construct input protections selected head tail raw
  have geometry := GeneralBorrowFreshDefaultGeometry.append_frame input
  have lenPositive : 0 < input.len.toNat := by
    have nonzero : input.len.toNat ≠ 0 := by
      intro zero
      exact input.nonzero (UInt64.toNat_inj.mp (by simpa using zero))
    omega
  have inside : input.offset.toNat < child.locations.size.bytes.toNat := by rw [congrArg Size.bytes geometry.2];have bound := input.bounds;omega
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered child.locations geometry.1 input.offset inside
  obtain ⟨data⟩ := owned position valid positive (by change child.locations.entries[position].range.start.toNat < (input.offset+input.len).toNat;omega) stop
  let component := data.base.base.component
  have nextFits : child.tagMapping.mapping.size ≤ 4294967295 := by
    rw [metadata.aligned]
    change child.nodes.size ≤ 4294967295
    rw [metadata.size]
    omega
  let next : Input := {
    tree := child
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    covered := metadata.certificates.covered
    parentTag := input.newTag
    newTag := future
    parent := index input
    parentNode := context.anchorNode
    parentTagPresent := metadata.freshLookup
    parentPresent := context.anchorPresent
    fresh := by
      rw [metadata.mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push input.tree.tagMapping input.newTag future (index input) input.tree.tagMapping.deassigned futureFresh different
    noFree := metadata.noFree
    aligned := metadata.aligned
    fits := nextFits
    offset := input.offset
    len := input.len
    nonzero := input.nonzero
    well := geometry.1
    bounds := by rw [geometry.2];exact input.bounds }
  have other : ∀ query,area.support query → ∃ old next,input.tree.nodeAt query = some old ∧ child.nodeAt query = some next ∧
      next.children = #[] ∧ next.isExposed = true := by
    intro query included
    obtain ⟨old,present,leaf,exposed⟩ := raw.leaves query included
    have different : query ≠ input.parent := by intro same;subst query;exact raw.separate input.parent included raw.component.anchor
    obtain ⟨next,found,tag,parent,children,permission,flag⟩ := GeneralBorrowExposedScopedDefaultOld.outside_parent input query old present different
    exact ⟨old,next,present,found,children.trans leaf,flag.trans exposed⟩
  have cache := GeneralBorrowDefaultConstructorExposureCache.append input protections raw.coherent
  have oldWritable:=GeneralBorrowExposedScopedWritableOldFrame.mutable input protections area.support
    (by intro query included;obtain ⟨node,found,_,_⟩:=raw.leaves query included;exact ⟨node,found⟩)
    (by intro query included same;apply raw.separate query included;rw [same];exact raw.component.anchor)
    raw.writableLeaves
  let nextRaw : Resources next protections selected head tail := {
    forest := data.base.base.forest
    component := component
    selectedNode := context.selectedNode
    selectedPresent := context.selectedPresent
    roots := context.roots
    rootPath := data.base.base.rootPath
    hidden := data.base.base.hidden
    separate := data.base.base.separate
    tags := context.tags
    leaves := by intro query included;obtain ⟨old,current,present,found,leaf,exposed⟩ := other query included;exact ⟨current,found,leaf,exposed⟩
    writableLeaves := oldWritable
    first := raw.first
    rest := raw.rest
    coherent := cache.2
    owned := by
      intro position valid positive lower upper
      obtain ⟨localData⟩ := owned position valid positive lower upper
      change GeneralBorrowExposedScopedMixedShape.Mixed child protections (index input) component.support
        (fun _=>true) _
      rw [show component.support = _ from data.base.support_eq]
      exact localData.base.mixed
    room := by change child.nodes.size+1<65536;rw [metadata.size];exact room }
  exact ⟨next,rfl,rfl,rfl,rfl,rfl,rfl,nextRaw,data.base.support_eq⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWritableDefaultAdvance
