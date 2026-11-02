import duplicate_prefix.GeneralBorrowExposedScopedInactiveDefaultConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveUniqueReadRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveDefaultRun
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveDefaultConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem full_every (predicate : α → Prop) (map : DedupRangeMap α) (well : map.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 map.size.bytes map) : GeneralRangeMapState.Every predicate map := by
  intro position valid
  have facts := GeneralRangeMapGeometry.facts map well (by omega)
  have lastValid : map.entries.size-1 < map.entries.size := by omega
  have lastPositive := facts.2.1 (map.entries.size-1) lastValid
  have lastSize := GeneralRangeMapGeometry.size_last map (by omega)
  have positive := facts.2.1 position valid
  have startBound : map.entries[position].range.start.toNat < map.size.bytes.toNat := by
    rw [lastSize]
    by_cases same : position = map.entries.size-1
    · subst position;exact lastPositive
    · have before : position < map.entries.size-1 := by omega
      have separation := GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) before lastValid
      omega
  exact owned position valid (by simp only [UInt64.toNat_zero];omega) startBound (by simp only [UInt64.toNat_zero];omega)

/-- On the positive whole allocation, real ranged Read preserves the complete
raw leaf-family resources needed by the actual shared constructor. The result
contains a genuine next constructor input, not an operation-success premise. -/
theorem prepare (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (atBase : input.offset = 0) (full : input.len = input.tree.locations.size.bytes)  :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ ∃ next : Input,
      next.tree = read.tree ∧ next.parentTag = input.parentTag ∧ next.newTag = input.newTag ∧
      next.parent = input.parent ∧ next.offset = input.offset ∧ next.len = input.len ∧
      index next = index input ∧ ∃ nextRaw : Resources next protections selected head tail,
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
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveUniqueReadData.Data input.tree location protections
        input.parent selected head tail raw.component.support (fun _ => true))) input.offset (input.offset+input.len) input.tree.locations := by
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
    have ancestors : ∀ query node state,raw.component.support query.toNat → input.tree.nodeAt query=some node → node.isExposed=true →
        input.tree.locationStateAt location query=some state →
        (query.toNat ∈ (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat ∧ state.permission=.Unique) ∨
        (query.toNat ∉ (source_normal_projection input.tree location protections).topology.ancestorPath input.parent.toNat ∧ state.permission=.Disabled) := by
      intro query node state member present exposed statePresent
      have stateEq : ((location.perms.get query).getD node.defaultLocationState)=state := by
        simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using statePresent
      have current := raw.exposures position valid query node member present exposed
      rw [stateEq] at current
      exact current
    exact ⟨{
      base := {
        base := GeneralBorrowExposedScopedInactiveLeafSeed.seed input.tree location protections input.parent selected head tail raw.component.support (fun _ => true)
          context raw.forest raw.component rfl mixed raw.rootPath ancestors raw.separate (raw.coherent position valid) short leaves raw.first raw.rest
        support_eq := rfl
        mixed := mixed }
      short := short
      leaves := raw.leaves
      unique := fun query included => raw.unique query included position valid }⟩
  let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have good := GeneralBorrowExposedScopedInactiveUniqueReadRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support (fun _ => true) nodeFits input.parentTagPresent input.well
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
  have every : GeneralRangeMapState.Every
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveUniqueReadData.Data read.tree location protections input.parent selected head tail raw.component.support (fun _ => true))) read.tree.locations := by
    refine full_every (fun location => Nonempty (GeneralBorrowExposedScopedInactiveUniqueReadData.Data read.tree location protections
      input.parent selected head tail raw.component.support (fun _ => true))) read.tree.locations good.2.2.1 ?_
    have size := congrArg Size.bytes good.2.2.2
    rw [size,←full]
    simpa only [read,atBase,UInt64.zero_add] using good.2.1
  let nextRaw : Resources next protections selected head tail := {
    forest := by rw [show next.tree = read.tree from rfl,frame];exact raw.forest
    component := component
    selectedNode := raw.selectedNode
    selectedPresent := by rw [show next.tree = read.tree from rfl,frame];exact raw.selectedPresent
    roots := by rw [show next.tree = read.tree from rfl,frame];exact raw.roots
    rootPath := by rw [show next.tree = read.tree from rfl,frame];exact raw.rootPath
    exposures := by
      intro position valid
      obtain ⟨data⟩ := every position valid
      exact GeneralBorrowExposedScopedInactiveRangeData.initial data.base.base
    separate := raw.separate
    tags := by intro query node included present;rw [show next.tree = read.tree from rfl,frame] at present;exact raw.tags query node included present
    leaves := by intro query included;obtain ⟨node,present,leaf,exposed⟩ := raw.leaves query included;exact ⟨node,by rw [show next.tree = read.tree from rfl,frame];exact present,leaf,exposed⟩
    unique := by intro query included position valid;obtain ⟨data⟩ := every position valid;exact data.unique query included
    first := raw.first
    rest := raw.rest
    coherent := by intro position valid;obtain ⟨data⟩ := every position valid;exact data.base.base.coherent
    owned := by intro position valid positive lower upper;obtain ⟨data⟩ := good.2.1 position valid positive lower upper;exact data.base.mixed
    room := by rw [show next.tree = read.tree from rfl,frame];exact raw.room }
  exact ⟨good.1,next,rfl,rfl,rfl,rfl,rfl,rfl,indexEq,nextRaw,rfl⟩
/-- Complete physical permission pipeline on the positive full allocation:
actual concrete parent Read, actual shared child construction, and complete
child inputs for every resulting range row. All premises are initial data. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (atBase : input.offset = 0) (full : input.len = input.tree.locations.size.bytes)  :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    read.status = .Completed ∧ child.outcome = .ok () ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveRangeData.Data child.tree location protections
          (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)))
          input.offset (input.offset+input.len) child.tree.locations := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    prepare input protections selected head tail raw atBase full
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveDefaultConstructor.construct next protections selected head tail nextRaw
  have childEq : result next =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  simp only [childEq,indexEq,supportEq,offsetEq,lenEq] at context owned
  refine ⟨readDone,?_,context,owned⟩
  simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using success

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveDefaultRun
