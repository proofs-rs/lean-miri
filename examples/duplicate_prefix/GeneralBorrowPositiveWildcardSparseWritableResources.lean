import duplicate_prefix.GeneralBorrowPositiveWildcardWritablePartitionResources
import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedProtect
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseWritableResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowStructuralHistoryState (State)
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedWritableSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def readTree (tree : BorrowTree) (protections : ProtectedTags) (capacity : UInt64) :=
  (tree.performBorrowAccessRange .wildcard Size.ZERO (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed).tree

def result (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (capacity : UInt64) :=
  let index : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  GeneralBorrowPositiveWildcardConstructor.result (readTree tree protections capacity)
    ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity

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

/-- The actual wildcard Read and protected FnEntry constructor form the next
shared-expression resources for mixed/sparse old rows. No materialized/default
replacement, exact-Unique family or operation-success hypothesis is used. -/
theorem build (tree : BorrowTree) (initial : State tree) (capacity : UInt64)
    (nonzero : capacity≠0) (full : tree.locations.size.bytes=capacity)
    (head : UniIndex) (extras : List UniIndex)
    (geometry : GeneralBorrowSparseExposedLeafState.Geometry tree head extras)
    (scope : ∀index,area.support index↔index∈head::extras)
    (tag futureTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping futureTag) (different : tag≠futureTag)
    (noFree : tree.tagMapping.deassigned.back?=none)
    (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size) (room : tree.nodes.size+8<65536)
    (protections : ProtectedTags)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) tree.locations)
    (leaves : ∀root∈head::extras,∃node,tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧ node.tag.value≤tag.value) :
    let index : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let after:=result tree protections tag capacity
    ∃input : Input,input.tree=after ∧ input.parentTag=tag ∧ input.newTag=futureTag ∧ input.parent=index ∧
      input.isProtected=false ∧ input.offset=0 ∧ input.len=capacity ∧
      ∃raw : Resources input protections index head (extras++[index]) (fun _=>true),
        raw.component.support=(fun position=>position=index.toNat) ∧ State after := by
  dsimp only
  let accessed:=readTree tree protections capacity
  have bounds : (0 : UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by
    rw [full];simpa only [UInt64.toNat_zero,Nat.zero_add] using Nat.le_refl capacity.toNat
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) 0 capacity tree.locations := by
    intro position valid _ _ _;exact sourceRaw position valid
  have read:=GeneralBorrowSparseExposedLeafRange.access tree protections head extras geometry Size.ZERO (Size.ofBytes capacity) .Read .VisitChildrenOfAccessed
    initial.well 0 capacity owned bounds (by simp [Size.ZERO]) (by simp [Size.ZERO,Size.ofBytes])
  have frame : accessed={tree with locations:=accessed.locations}:=GeneralBorrowFreshReadFrame.frame tree .wildcard Size.ZERO
    (Size.ofBytes capacity) .Read protections .VisitChildrenOfAccessed
  have readState : State accessed := by
    rw [frame]
    exact ⟨GeneralBorrowStructuralHistoryState.graph_locations tree accessed.locations initial.toGraphState,read.2.2.1⟩
  have readFull : accessed.locations.size.bytes=capacity := (congrArg Size.bytes read.2.2.2).trans full
  have readRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw accessed location protections) accessed.locations := by
    exact full_every (fun location=>GeneralBorrowSparseExposedLeafState.Raw accessed location protections) accessed.locations read.2.2.1 (by
      rw [readFull]
      exact read.2.1)
  have coherent : GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent accessed location protections) accessed.locations :=
    fun position valid=>(readRaw position valid).1
  have writable : GeneralRangeMapState.Every (GeneralBorrowSifaWritableFrame.Profile accessed protections area.support) accessed.locations := by
    intro position valid query node included present
    exact (readRaw position valid).2 query node present
  have readFresh : GeneralBorrowTagMap.Fresh accessed.tagMapping tag := by rw [frame];exact fresh
  have readFuture : GeneralBorrowTagMap.Fresh accessed.tagMapping futureTag := by rw [frame];exact futureFresh
  have readFree : accessed.tagMapping.deassigned.back?=none := by rw [frame];exact noFree
  have readAligned : accessed.tagMapping.mapping.size=accessed.nodes.data.size := by rw [frame];exact aligned
  have readRoom : accessed.nodes.size+8<65536 := by rw [frame];exact room
  have readRoots : accessed.roots=(head::extras).toArray := by rw [frame];exact geometry.roots
  have readLeaves : ∀root∈head::extras,∃node,accessed.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧ node.tag.value≤tag.value := by
    intro root member
    obtain ⟨node,present,leaf,exposed,bound⟩:=leaves root member
    exact ⟨node,by rw [frame];exact present,leaf,exposed,bound⟩
  have next:=GeneralBorrowPositiveWildcardWritablePartitionResources.build accessed readState capacity nonzero readFull head extras readRoots scope tag futureTag
    readFresh readFuture different readFree readAligned readRoom protections coherent readLeaves writable
  have mapping : accessed.tagMapping=tree.tagMapping := by rw [frame]
  have mapping' : (readTree tree protections capacity).tagMapping=tree.tagMapping := mapping
  dsimp only at next
  dsimp only [accessed] at next
  rw [mapping'] at next
  simpa only [result] using next

/-- A real fresh bool-slot Strong registration preserves the derived complete
mixed resources. Its table extension is the actual ProtectorMap insertion. -/
theorem build_registered (tree : BorrowTree) (initial : State tree) (capacity : UInt64)
    (nonzero : capacity≠0) (full : tree.locations.size.bytes=capacity)
    (head : UniIndex) (extras : List UniIndex)
    (geometry : GeneralBorrowSparseExposedLeafState.Geometry tree head extras)
    (scope : ∀index,area.support index↔index∈head::extras)
    (tag futureTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping futureTag) (different : tag≠futureTag)
    (noFree : tree.tagMapping.deassigned.back?=none)
    (aligned : tree.tagMapping.mapping.size=tree.nodes.data.size) (room : tree.nodes.size+8<65536)
    (registrationTag : BorTag) (registrationFresh : GeneralBorrowTagMap.Fresh tree.tagMapping registrationTag)
    (registrationDifferent : tag≠registrationTag)
    (protections : ProtectedTags)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) tree.locations)
    (leaves : ∀root∈head::extras,∃node,tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧ node.tag.value≤tag.value) :
    let index : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let after:=result tree protections tag capacity
    ∃input : Input,input.tree=after ∧ input.parentTag=tag ∧ input.newTag=futureTag ∧ input.parent=index ∧
      input.isProtected=false ∧ input.offset=0 ∧ input.len=capacity ∧
      ∃raw : Resources input (protections.insert registrationTag .StrongProtector) index head (extras++[index]) (fun _=>true),
        raw.component.support=(fun position=>position=index.toNat) ∧ State after := by
  dsimp only
  obtain ⟨input,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,raw,supportEq,state⟩:=
    build tree initial capacity nonzero full head extras geometry scope tag futureTag fresh futureFresh different noFree aligned room protections sourceRaw leaves
  let index : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have nextFresh : GeneralBorrowTagMap.Fresh (result tree protections tag capacity).tagMapping registrationTag :=
    GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag registrationTag index tree.tagMapping.deassigned registrationFresh registrationDifferent
  have absent : (result tree protections tag capacity).indexOfTag registrationTag=none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ nextFresh,Option.map_none]
  obtain ⟨next,support⟩:=GeneralBorrowExposedScopedWritableSharedProtect.protect input protections registrationTag index head (extras++[index]) (fun _=>true) raw (by
    intro query node present equal
    rw [treeEq] at present
    have tagged:=state.allocator.nodeTags query node present
    change (result tree protections tag capacity).indexOfTag node.tag=some query at tagged
    rw [equal,absent] at tagged
    cases tagged)
  exact ⟨input,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,next,support.trans supportEq,state⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseWritableResources
