import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableGlobalReadRange
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildMutable
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor (Resources ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- On an arbitrary bounded positive window, real ranged Read preserves the complete
raw leaf-family resources needed by the actual shared constructor. The result
contains a genuine next constructor input, not an operation-success premise. -/
theorem prepare (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ ∃ next : Input,
      next.tree = read.tree ∧ next.parentTag = input.parentTag ∧ next.newTag = input.newTag ∧
      next.parent = input.parent ∧ next.offset = input.offset ∧ next.len = input.len ∧
      index next = index input ∧ ∃ nextRaw : Resources next protections selected head tail,
        nextRaw.component.support = raw.component.support := by
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedInactiveWritableProtectedMutableData.build input protections selected head tail raw
  have nodeFits : input.tree.nodes.data.size≤4294967296 := by have bound:=input.fits;have aligned:=input.aligned;omega
  let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have good := GeneralBorrowExposedScopedInactiveWritableReadRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support (fun _=>true) nodeFits input.parentTagPresent input.well
    input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
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
        GeneralBorrowSifaWritableFrame.Profile input.tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile input.tree location input.parent raw.component.support) input.tree.locations := by
    intro position valid
    exact ⟨raw.coherent position valid,raw.writableLeaves position valid,raw.exposures position valid⟩
  have globalRead:=GeneralBorrowExposedScopedInactiveWritableGlobalReadRange.ranged input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support (fun _=>true) nodeFits input.parentTagPresent globalInitial
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have globals : GeneralRangeMapState.Every
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent next.tree location protections ∧
        GeneralBorrowSifaWritableFrame.Profile next.tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile next.tree location input.parent raw.component.support) next.tree.locations := by
    change GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent read.tree location protections ∧
      GeneralBorrowSifaWritableFrame.Profile read.tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile read.tree location input.parent raw.component.support) read.tree.locations
    rw [frame]
    exact globalRead.2
  let nextRaw : Resources next protections selected head tail := {
    forest := by rw [show next.tree = read.tree from rfl,frame];exact raw.forest
    component := component
    selectedNode := raw.selectedNode
    selectedPresent := by rw [show next.tree = read.tree from rfl,frame];exact raw.selectedPresent
    roots := by rw [show next.tree = read.tree from rfl,frame];exact raw.roots
    rootPath := by rw [show next.tree = read.tree from rfl,frame];exact raw.rootPath
    exposures := by intro position valid;exact (globals position valid).2.2
    separate := raw.separate
    tags := by intro query node included present;rw [show next.tree = read.tree from rfl,frame] at present;exact raw.tags query node included present
    leaves := by intro query included;obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included;exact ⟨node,by rw [show next.tree = read.tree from rfl,frame];exact present,leaf,exposed⟩
    writableLeaves := by intro position valid;exact (globals position valid).2.1
    first := raw.first
    rest := raw.rest
    coherent := by intro position valid;exact (globals position valid).1
    owned := by intro position valid positive lower upper;obtain ⟨data⟩ := good.2.1 position valid positive lower upper;exact data.base.mixed
    room := by rw [show next.tree = read.tree from rfl,frame];exact raw.room }
  exact ⟨good.1,next,rfl,rfl,rfl,rfl,rfl,rfl,indexEq,nextRaw,rfl⟩
/-- Complete physical permission pipeline on an arbitrary bounded positive window:
actual concrete parent Read, actual shared child construction, and complete
child inputs for every resulting range row. All premises are initial data. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data child.tree location protections
          (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)
          (fun _=>true)))
          input.offset (input.offset+input.len) child.tree.locations := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    prepare input protections selected head tail raw
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.construct next protections selected head tail nextRaw
  have childEq : result next =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  simp only [childEq,indexEq,supportEq,offsetEq,lenEq] at context owned
  refine ⟨readDone,?_,context,owned⟩
  simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using success


/-- Actual permission pipeline for either explicit profile scope; all
operation outcomes remain conclusions, and prepare retains the supplied mode. -/
theorem prepare_mode {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor input protections selected head tail profileMode)
    :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ ∃ next : Input,
      next.tree = read.tree ∧ next.parentTag = input.parentTag ∧ next.newTag = input.newTag ∧
      next.parent = input.parent ∧ next.offset = input.offset ∧ next.len = input.len ∧
      index next = index input ∧ ∃ nextRaw : ResourcesFor next protections selected head tail profileMode,
        nextRaw.component.support = raw.component.support := by
  cases profileMode with
  | global => exact prepare input protections selected head tail raw
  | window =>
    obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
      GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun.prepare input protections selected head tail
        (ResourcesFor.toWindow input protections selected head tail raw)
    exact ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,ResourcesFor.ofWindow next protections selected head tail nextRaw,supportEq⟩

/-- Actual permission pipeline for either explicit profile scope; all
operation outcomes remain conclusions, and prepare retains the supplied mode. -/
theorem run_mode {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor input protections selected head tail profileMode)
    :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data child.tree location protections
          (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)
          (fun _=>true)))
          input.offset (input.offset+input.len) child.tree.locations := by
  exact GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun.run input protections selected head tail
    (ResourcesFor.toWindow input protections selected head tail raw)

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
