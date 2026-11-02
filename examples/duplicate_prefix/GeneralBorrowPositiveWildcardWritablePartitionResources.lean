import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedConstructor
import duplicate_prefix.GeneralBorrowExposedIsolatedComponent
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
import duplicate_prefix.GeneralBorrowWildcardRootInstalled
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWritablePartitionResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedWritableSharedConstructor (Resources)
open GeneralBorrowStructuralHistoryState (State)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual positive wildcard FnEntry result supplies the next concrete
shared-borrow Resources. Old roots are exposed leaves with arbitrary writable effective rows;
the appended protected mutable root is the selected last component. All graph,
permission, cache, allocator and future-tag premises concern the initial tree. -/
theorem build (tree : BorrowTree) (initial : State tree) (capacity : UInt64)
    (nonzero : capacity ≠ 0) (full : tree.locations.size.bytes=capacity)
    (head : UniIndex) (extras : List UniIndex) (roots : tree.roots = (head::extras).toArray)
    (scope : ∀ index,area.support index ↔ index ∈ head::extras)
    (tag futureTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping futureTag) (different : tag ≠ futureTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (room : tree.nodes.size+8 < 65536)
    (protections : ProtectedTags)
    (coherent : GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent tree location protections) tree.locations)
    (leaves : ∀ root ∈ head::extras, ∃ node,tree.nodeAt root = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      node.tag.value ≤ tag.value)
    (writableLeaves : GeneralRangeMapState.Every (GeneralBorrowSifaWritableFrame.Profile tree protections area.support) tree.locations) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
    ∃ input : Input, input.tree = after ∧ input.parentTag = tag ∧ input.newTag = futureTag ∧ input.parent = index ∧
      input.isProtected = false ∧ input.offset = 0 ∧ input.len = capacity ∧
      ∃ raw : Resources input protections index head (extras++[index]) (fun _ => true),
        raw.component.support = (fun position => position = index.toNat) ∧ State after := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
  let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have indexFits : tree.tagMapping.mapping.size < 2^32 := by
    change tree.nodes.data.size+8<65536 at room
    omega
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt indexFits]
    exact aligned
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by change tree.nodes.data.size+8<65536 at room;omega
  have bounds : (0 : UInt64).toNat+capacity.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [full]
    simpa only [UInt64.toNat_zero,Nat.zero_add] using (Nat.le_refl capacity.toNat)
  have actual := GeneralBorrowPositiveWildcardConstructor.append tree tag fresh noFree fits (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl 0 capacity nonzero initial.well bounds
  change tree.newChild (Size.ofBytes 0) .wildcard tag (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true = ⟨after,.ok ()⟩ at actual
  have structural := GeneralBorrowStructuralHistoryWildcard.construct tree initial tag fresh (by omega) 0 capacity bounds
  dsimp only at structural
  rw [actual] at structural
  have afterState : State after := structural.2.1
  have bytes : after.locations.size = tree.locations.size := structural.2.2.1
  have vacant : tree.nodes.get index = none := by
    unfold UniValMap.get
    rw [atEnd]
    simp
  have size : after.nodes.size = tree.nodes.size+1 := GeneralBorrowFreshNode.append_size tree.nodes index node atEnd
  have grows : tree.nodes.size ≤ (tree.nodes.insert index node).size := by rw [GeneralBorrowFreshNode.append_size tree.nodes index node atEnd];omega
  have present : after.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  have oldDifferent : ∀ query old,tree.nodeAt query = some old → query ≠ index := by
    intro query old found same
    have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes query old found
    rw [same,atEnd] at bound
    omega
  have oldPresent : ∀ query old,tree.nodeAt query = some old → after.nodeAt query = some old := by
    intro query old found
    exact (GeneralBorrowFreshLocation.get_other tree.nodes index query node (oldDifferent query old found)).trans found
  have nextNoFree : after.tagMapping.deassigned.back? = none := noFree
  have nextAligned : after.tagMapping.mapping.size = after.nodes.data.size :=
    GeneralBorrowFreshStagePool.empty_aligned after afterState.allocator.accounting nextNoFree
  have nextFits : after.tagMapping.mapping.size ≤ 4294967295 := by rw [nextAligned];change after.nodes.size≤_;rw [size];omega
  obtain ⟨depth⟩ := afterState.depth
  let input : Input := {
    tree := after
    depth := depth
    children := afterState.children
    covered := afterState.covered
    parentTag := tag
    newTag := futureTag
    parent := index
    parentNode := node
    parentTagPresent := GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh index tree.tagMapping.deassigned
    parentPresent := present
    fresh := GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag futureTag index tree.tagMapping.deassigned futureFresh different
    noFree := nextNoFree
    aligned := nextAligned
    fits := nextFits
    isProtected := false
    offset := 0
    len := capacity
    nonzero := nonzero
    well := afterState.well
    bounds := by rw [bytes];exact bounds }
  let component := GeneralBorrowExposedIsolatedComponent.component after default protections index node present rfl rfl
  have oldLeaves : ∀ query,area.support query → ∃ old,tree.nodeAt query = some old ∧ old.children = #[] ∧ old.isExposed = true ∧
      old.tag.value ≤ tag.value := by
    intro query included
    exact leaves query ((scope query).mp included)
  have initialProfile : GeneralRangeMapState.Every (GeneralBorrowSifaWritableFrame.Profile after protections area.support) tree.locations := by
    intro position valid query actual included found
    obtain ⟨old,oldFound,leaf,exposed,bounded⟩:=oldLeaves query included
    have same := Option.some.inj ((oldPresent query old oldFound).symm.trans found)
    subst actual
    exact writableLeaves position valid query old included oldFound
  have profiles : GeneralRangeMapState.Every (GeneralBorrowSifaWritableFrame.Profile after protections area.support) after.locations := by
    apply GeneralBorrowExposureChildAttach.modify_every _ tree.locations (Size.ofBytes 0) (Size.ofBytes capacity)
      (fun _ location=>{location with perms:=location.perms.insert index GeneralBorrowFreshChild.inside}) initial.well bounds initialProfile
    intro range location profile query actual included found
    obtain ⟨old,oldFound,leaf,exposed,bounded⟩:=oldLeaves query included
    have same := Option.some.inj ((oldPresent query old oldFound).symm.trans found)
    subst actual
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,
      GeneralBorrowFreshLocation.get_other _ index query GeneralBorrowFreshChild.inside (oldDifferent query old oldFound)]
      using profile query old included (oldPresent query old oldFound)
  have initialCache : GeneralRangeMapState.Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections) tree.locations := coherent
  obtain ⟨oldDepth⟩ := initial.depth
  have cache := GeneralBorrowWildcardRootCache.constructor tree oldDepth mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside
    0 capacity vacant grows initial.well bounds protections initialCache
  have installed := GeneralBorrowWildcardRootInstalled.installed tree.locations index GeneralBorrowFreshChild.inside (Size.ofBytes 0)
    (Size.ofBytes capacity) initial.well bounds
  let raw : Resources input protections index head (extras++[index]) (fun _ => true) := {
    forest := Classical.choice (afterState.forest default protections)
    component := component
    selectedNode := node
    selectedPresent := present
    roots := by
      change tree.roots.push index = (head::(extras++[index])).toArray
      rw [roots]
      simpa only [List.cons_append] using List.push_toArray (head::extras) index
    rootPath := by rw [GeneralBorrowExposedIsolatedComponent.root_path after default protections index node present rfl];rfl
    hidden := by
      intro query actual included found
      have same : query = index := GeneralBorrowNodeUpdate.index_injective query index included
      subst query
      have equal := Option.some.inj (present.symm.trans found)
      subst actual
      rfl
    separate := by
      intro query included same
      obtain ⟨old,found,_,_,_⟩ := oldLeaves query included
      exact oldDifferent query old found (GeneralBorrowNodeUpdate.index_injective query index same)
    tags := by
      intro query actual included found
      obtain ⟨old,oldFound,_,_,bound⟩ := oldLeaves query included
      have equal := Option.some.inj ((oldPresent query old oldFound).symm.trans found)
      subst actual
      exact bound
    leaves := by
      intro query included
      obtain ⟨old,found,leaf,exposed,_⟩ := oldLeaves query included
      exact ⟨old,oldPresent query old found,leaf,exposed⟩
    writableLeaves := profiles
    first := fun _ => (scope head).mpr (by simp)
    rest := by
      intro root member different
      rcases List.mem_append.mp member with old | fresh
      · exact (scope root).mpr (by simp [old])
      · have same : root = index := by simpa only [List.mem_singleton] using fresh
        exact False.elim (different same)
    coherent := cache
    owned := by
      intro position valid positive lower upper
      exact GeneralBorrowExposedIsolatedComponent.reserved after _ protections index node present (installed position valid positive lower upper)
    room := by change after.nodes.size+1<65536;rw [size];omega }
  exact ⟨input,rfl,rfl,rfl,rfl,rfl,rfl,rfl,raw,rfl,afterState⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardWritablePartitionResources
