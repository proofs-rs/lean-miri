import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafConstructor
import duplicate_prefix.GeneralBorrowExposedScopedGlobalReadRange
import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowSharedLeafRun
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- On an arbitrary bounded positive slice, real ranged Read preserves the complete
raw leaf-family resources needed by the actual shared constructor. The result
contains a genuine next constructor input, not an operation-success premise. -/
theorem prepare (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (mode : ChildrenVisitMode) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    read.status = .Completed ∧ ∃ next : Input,
      next.tree = read.tree ∧ next.parentTag = input.parentTag ∧ next.newTag = input.newTag ∧
      next.parent = input.parent ∧ next.isProtected = input.isProtected ∧ next.offset = input.offset ∧ next.len = input.len ∧
      index next = index input ∧ ∃ nextRaw : Resources next protections selected head tail writable,
        nextRaw.component.support = raw.component.support := by
  let context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail := {
    anchorNode := input.parentNode
    selectedNode := raw.selectedNode
    anchorPresent := input.parentPresent
    selectedPresent := raw.selectedPresent
    roots := raw.roots
    depth := input.depth
    children := input.children
    tags := raw.tags }
  have nodeFits : input.tree.nodes.data.size ≤ 4294967296 := by
    have bound := input.fits
    have aligned := input.aligned
    omega
  have short : input.tree.nodes.size < 65536 := by have bound := raw.room;omega
  have owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data input.tree location protections
        input.parent selected head tail raw.component.support writable)) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    let location := (input.tree.locations.entries[position]'valid).data
    have mixed := raw.owned position valid positive lower upper
    have leaves : ∀ query,area.support query → ∃ node,input.tree.nodes.get query = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
        GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections query node) .Read = true ∧
        (GeneralBorrowWildcardVirtualLeaf.effective location query node).possible = true := by
      intro query included
      obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included
      have stored := raw.unique query included position valid
      change location.perms.get query = some GeneralBorrowWildcardLeaf.unique at stored
      refine ⟨node,present,leaf,exposed,?_,?_⟩
      · simp [GeneralBorrowExposureCardinality.effective,stored,GeneralBorrowWildcardLeaf.unique,Permission.strongestAllowedLocalAccess,
          GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
      · simp [GeneralBorrowWildcardVirtualLeaf.effective,stored,GeneralBorrowWildcardLeaf.unique,LocationState.possible]
    exact ⟨{
      base := GeneralBorrowExposedScopedLeafSeed.seed input.tree location protections input.parent selected head tail raw.component.support writable
        context raw.forest raw.component rfl mixed raw.rootPath raw.hidden raw.separate (raw.coherent position valid) short leaves raw.first raw.rest
      short := short
      leaves := raw.leaves
      unique := fun query included => raw.unique query included position valid }⟩
  let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
  have good := GeneralBorrowExposedScopedUniqueReadRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) mode context raw.component.support writable nodeFits input.parentTagPresent input.well
    input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
  change read.tree = {input.tree with locations := read.tree.locations} at frame
  have nodes : read.tree.nodes = input.tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : read.tree.tagMapping = input.tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := GeneralBorrowFreshReadFrame.depth_on input.tree read.tree nodes input.depth
  let next : Input := {
    tree := read.tree
    depth := depth
    children := by rw [frame];exact input.children
    covered := by rw [frame];exact input.covered
    parentTag := input.parentTag
    newTag := input.newTag
    parent := input.parent
    parentNode := input.parentNode
    parentTagPresent := by rw [frame];exact input.parentTagPresent
    parentPresent := by rw [frame];exact input.parentPresent
    fresh := by rw [mapping];exact input.fresh
    noFree := by rw [mapping];exact input.noFree
    aligned := by rw [mapping,nodes];exact input.aligned
    fits := by rw [mapping];exact input.fits
    isProtected := input.isProtected
    offset := input.offset
    len := input.len
    nonzero := input.nonzero
    well := good.2.2.1
    bounds := by rw [good.2.2.2];exact input.bounds }
  have indexEq : index next = index input := by simp only [index,next,mapping]
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection next.tree default protections).topology input.parent.toNat := {
    support := raw.component.support
    anchor := raw.component.anchor
    parents := by rw [show next.tree = read.tree from rfl,frame];exact raw.component.parents
    children := by rw [show next.tree = read.tree from rfl,frame];exact raw.component.children }
  have globalInitial : GeneralRangeMapState.Every
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent input.tree location protections ∧
        ∀ query,area.support query→location.perms.get query=some GeneralBorrowWildcardLeaf.unique) input.tree.locations := by
    intro position valid
    exact ⟨raw.coherent position valid,fun query included=>raw.unique query included position valid⟩
  have globalRead:=GeneralBorrowExposedScopedGlobalReadRange.ranged input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) mode context raw.component.support writable nodeFits input.parentTagPresent globalInitial
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have globals : GeneralRangeMapState.Every
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent next.tree location protections ∧
        ∀ query,area.support query→location.perms.get query=some GeneralBorrowWildcardLeaf.unique) next.tree.locations := by
    change GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent read.tree location protections ∧
      ∀ query,area.support query→location.perms.get query=some GeneralBorrowWildcardLeaf.unique) read.tree.locations
    rw [frame]
    exact globalRead.2
  let nextRaw : Resources next protections selected head tail writable := {
    forest := by rw [show next.tree = read.tree from rfl,frame];exact raw.forest
    component := component
    selectedNode := raw.selectedNode
    selectedPresent := by rw [show next.tree = read.tree from rfl,frame];exact raw.selectedPresent
    roots := by rw [show next.tree = read.tree from rfl,frame];exact raw.roots
    rootPath := by rw [show next.tree = read.tree from rfl,frame];exact raw.rootPath
    hidden := by intro query node included present;rw [show next.tree = read.tree from rfl,frame] at present;exact raw.hidden query node included present
    separate := raw.separate
    tags := by intro query node included present;rw [show next.tree = read.tree from rfl,frame] at present;exact raw.tags query node included present
    leaves := by intro query included;obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included;exact ⟨node,by rw [show next.tree = read.tree from rfl,frame];exact present,leaf,exposed⟩
    unique := by intro query included position valid;exact (globals position valid).2 query included
    first := raw.first
    rest := raw.rest
    coherent := by intro position valid;exact (globals position valid).1
    owned := by intro position valid positive lower upper;obtain ⟨data⟩ := good.2.1 position valid positive lower upper;exact data.base.mixed
    room := by rw [show next.tree = read.tree from rfl,frame];exact raw.room }
  exact ⟨good.1,next,rfl,rfl,rfl,rfl,rfl,rfl,rfl,indexEq,nextRaw,rfl⟩
/-- Complete physical permission pipeline on the arbitrary bounded positive slice:
actual concrete parent Read, actual shared child construction, and complete
child inputs for every resulting range row. All premises are initial data. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (mode : ChildrenVisitMode) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    read.status = .Completed ∧ child.outcome = .ok () ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data child.tree location protections
          (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)
          (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)))
          input.offset (input.offset+input.len) child.tree.locations := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    prepare input protections selected head tail writable raw mode
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedSharedLeafConstructor.construct next protections selected head tail writable nextRaw
  have childEq : result next =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  simp only [childEq,indexEq,supportEq,offsetEq,lenEq] at context owned
  refine ⟨readDone,?_,context,owned⟩
  simpa only [treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq] using success

end DuplicatePrefix.GeneralBorrowExposedScopedWindowSharedLeafRun
