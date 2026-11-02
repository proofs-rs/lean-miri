import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionRegistration
import duplicate_prefix.GeneralBorrowRangePrepareState
import duplicate_prefix.GeneralBorrowExposedScopedSharedLeafProtect
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionPreparedRegistration
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
theorem build_registered (tree : BorrowTree) (initial : State tree) (capacity : UInt64)
    (nonzero : capacity ≠ 0) (full : tree.locations.size.bytes=capacity)
    (head : UniIndex) (extras : List UniIndex) (roots : tree.roots = (head::extras).toArray)
    (scope : ∀ index,area.support index ↔ index ∈ head::extras)
    (tag futureTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping futureTag) (different : tag ≠ futureTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (room : tree.nodes.size+8 < 65536)
    (registrationTag : BorTag) (registrationFresh : GeneralBorrowTagMap.Fresh tree.tagMapping registrationTag)
    (registrationDifferent : tag ≠ registrationTag)
    (protections : ProtectedTags)
    (coherent : GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent tree location protections) tree.locations)
    (leaves : ∀ root ∈ head::extras, ∃ node,tree.nodeAt root = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      node.tag.value ≤ tag.value)
    (unique : ∀ root∈head::extras,GeneralBorrowSifaUniqueFrame.UniqueAt tree root) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    let after := GeneralBorrowPositiveWildcardConstructor.result (GeneralBorrowRangePrepareState.prepared tree Size.ZERO (Size.ofBytes capacity)) mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
    ∃ input : Input, input.tree = after ∧ input.parentTag = tag ∧ input.newTag = futureTag ∧ input.parent = index ∧
      input.isProtected = false ∧ input.offset = 0 ∧ input.len = capacity ∧
      ∃ raw : Resources input (protections.insert registrationTag .StrongProtector) index head (extras++[index]) (fun _ => true),
        raw.component.support = (fun position => position = index.toNat) := by
  let prepared:=GeneralBorrowRangePrepareState.prepared tree Size.ZERO (Size.ofBytes capacity)
  have bounds : (0 : UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by
    rw [full]
    simpa only [UInt64.toNat_zero,Nat.zero_add] using (Nat.le_refl capacity.toNat)
  have preparedState:=GeneralBorrowRangePrepareState.state tree Size.ZERO (Size.ofBytes capacity) initial bounds
  have preparedFull : prepared.locations.size.bytes=capacity :=
    (congrArg Size.bytes preparedState.2).trans full
  have preparedCoherent : GeneralRangeMapState.Every
      (fun location=>GeneralBorrowExposureCardinality.LocationCoherent prepared location protections) prepared.locations :=
    GeneralBorrowRangePrepareState.every tree Size.ZERO (Size.ofBytes capacity) _ initial.well coherent bounds
  have preparedUnique : ∀ root∈head::extras,GeneralBorrowSifaUniqueFrame.UniqueAt prepared root := by
    intro root member
    exact GeneralBorrowRangePrepareState.every tree Size.ZERO (Size.ofBytes capacity) _ initial.well (unique root member) bounds
  exact GeneralBorrowPositiveWildcardPartitionRegistration.build_registered prepared preparedState.1 capacity nonzero preparedFull
    head extras roots scope tag futureTag fresh futureFresh different noFree aligned room registrationTag registrationFresh registrationDifferent
    protections preparedCoherent leaves preparedUnique
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionPreparedRegistration
