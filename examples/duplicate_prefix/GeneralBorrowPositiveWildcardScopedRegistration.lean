import duplicate_prefix.GeneralBorrowPositiveWildcardScopedResources
import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafProtect
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardScopedRegistration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
open GeneralBorrowStructuralHistoryState (State)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- The real positive wildcard FnEntry constructor also supplies complete scoped
resources after a separate fresh return-slot Strong registration. Freshness,
cache coherence and mixed ownership across registration are derived internally. -/
theorem build_registered (tree : BorrowTree) (initial : State tree) (location : LocationTree) (capacity : UInt64)
    (nonzero : capacity ≠ 0) (locations : tree.locations = RangeMapNonempty.homogeneous capacity location)
    (head : UniIndex) (extras : List UniIndex) (roots : tree.roots = (head::extras).toArray)
    (scope : ∀ index,area.support index ↔ index ∈ head::extras)
    (tag futureTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping futureTag) (different : tag ≠ futureTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (room : tree.nodes.size+8 < 65536)
    (registrationTag : BorTag) (registrationFresh : GeneralBorrowTagMap.Fresh tree.tagMapping registrationTag)
    (registrationDifferent : tag ≠ registrationTag)
    (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (leaves : ∀ root ∈ head::extras, ∃ node,tree.nodeAt root = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      location.perms.get root = some GeneralBorrowWildcardLeaf.unique ∧ node.tag.value ≤ tag.value) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
    ∃ input : Input, input.tree = after ∧ input.parentTag = tag ∧ input.newTag = futureTag ∧ input.parent = index ∧
      input.isProtected = false ∧ input.offset = 0 ∧ input.len = capacity ∧
      ∃ raw : Resources input (protections.insert registrationTag .StrongProtector) index head (extras++[index]) (fun _ => true),
        raw.component.support = (fun position => position = index.toNat) := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
  let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
  obtain ⟨input,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,raw,supportEq⟩ :=
    GeneralBorrowPositiveWildcardScopedResources.build tree initial location capacity nonzero locations head extras roots scope tag futureTag fresh
      futureFresh different noFree aligned room protections coherent leaves
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    change tree.nodes.data.size+8<65536 at room
    omega
  have bounds : (0 : UInt64).toNat+capacity.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [locations]
    simp [RangeMapNonempty.homogeneous,DedupRangeMap.size,Size.ofBytes]
  have actual := GeneralBorrowPositiveWildcardConstructor.append tree tag fresh noFree fits (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl 0 capacity nonzero initial.well bounds
  change tree.newChild (Size.ofBytes 0) .wildcard tag (DedupRangeMap.new (Size.ofBytes capacity) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true = ⟨after,.ok ()⟩ at actual
  have structural := GeneralBorrowStructuralHistoryWildcard.construct tree initial tag fresh (by omega) 0 capacity bounds
  dsimp only at structural
  rw [actual] at structural
  have state : State after := structural.2.1
  have registrationFreshAfter : GeneralBorrowTagMap.Fresh after.tagMapping registrationTag :=
    GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping tag registrationTag index tree.tagMapping.deassigned registrationFresh registrationDifferent
  have absent : after.indexOfTag registrationTag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find after.tagMapping registrationTag registrationFreshAfter,Option.map_none]
  obtain ⟨next,sameSupport⟩ := GeneralBorrowExposedScopedSharedLeafProtect.protect input protections registrationTag index head (extras++[index]) (fun _ => true) raw (by
    intro query node present equal
    rw [treeEq] at present
    have mapped := state.allocator.nodeTags query node present
    change after.indexOfTag node.tag = some query at mapped
    rw [equal,absent] at mapped
    cases mapped)
  exact ⟨input,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,next,sameSupport.trans supportEq⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardScopedRegistration
