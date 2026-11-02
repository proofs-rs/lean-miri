import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafConstructor
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafAdvance
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Shared construction re-forms the allocator and graph/permission resources
for the next actual shared helper entry. The fresh next tag and node room are
initial raw resources; every post-constructor field is derived. -/
theorem advance (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) (held : Bool) :
    ∃ next : Input, next.tree = result input ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.isProtected = held ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : Resources next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat),
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  let child := result input
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedSharedLeafConstructor.construct input protections selected head tail writable raw
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have lenPositive : 0 < input.len.toNat := by
    have nonzero : input.len.toNat ≠ 0 := by
      intro zero
      exact input.nonzero (UInt64.toNat_inj.mp (by simpa using zero))
    omega
  have inside : input.offset.toNat < child.locations.size.bytes.toNat := by rw [congrArg Size.bytes geometry.2];have bound := input.bounds;omega
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered child.locations geometry.1 input.offset inside
  obtain ⟨data⟩ := owned position valid positive (by change child.locations.entries[position].range.start.toNat < (input.offset+input.len).toNat;omega) stop
  let component := data.base.component
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
    fresh := GeneralBorrowFreshMetadataChildAllocator.append_fresh input future futureFresh different
    noFree := metadata.noFree
    aligned := metadata.aligned
    fits := nextFits
    isProtected := held
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
    obtain ⟨next,found,tag,parent,children,permission,flag⟩ := GeneralBorrowExposedScopedSharedOld.outside_parent input query old present different
    exact ⟨old,next,present,found,children.trans leaf,flag.trans exposed⟩
  have cache := GeneralBorrowSharedConstructorExposureCache.append input protections raw.coherent
  let nextRaw : Resources next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) := {
    forest := data.base.forest
    component := component
    selectedNode := context.selectedNode
    selectedPresent := context.selectedPresent
    roots := context.roots
    rootPath := data.base.rootPath
    hidden := data.base.hidden
    separate := data.base.separate
    tags := context.tags
    leaves := by intro query included;obtain ⟨old,current,present,found,leaf,exposed⟩ := other query included;exact ⟨current,found,leaf,exposed⟩
    unique := by
      intro query included
      obtain ⟨old,current,present,found,leaf,exposed⟩ := other query included
      exact GeneralBorrowExposedScopedSharedOld.unique input query old present (raw.unique query included)
    first := raw.first
    rest := raw.rest
    coherent := cache.2
    owned := by
      intro position valid positive lower upper
      obtain ⟨localData⟩ := owned position valid positive lower upper
      change GeneralBorrowExposedScopedMixedShape.Mixed child protections (index input) component.support
        (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) _
      rw [show component.support = _ from data.support_eq]
      exact localData.mixed
    room := by change child.nodes.size+1<65536;rw [metadata.size];exact room }
  exact ⟨next,rfl,rfl,rfl,rfl,rfl,rfl,rfl,nextRaw,data.support_eq⟩
end DuplicatePrefix.GeneralBorrowExposedScopedSharedLeafAdvance
