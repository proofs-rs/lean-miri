import duplicate_prefix.GeneralBorrowObserverDirectReadRow
import duplicate_prefix.GeneralBorrowObserverReadRange
namespace DuplicatePrefix.GeneralBorrowObserverDirectReadRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProjection
open GeneralBorrowSnapshotWildcardRangeBoth (Runtime VacantFrame)
open GeneralBorrowObserverReadRange (Observer observer_locations)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual bounded shared temporary Read, including range splitting and all
root callbacks, keeps the original mutable observer under REAL protections. -/
theorem access (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (observer : UniIndex) (observerNode : TreeNode)
    (edge : anchorNode.parent = some observer) (observerPresent : tree.nodeAt observer = some observerNode)
    (hidden : anchorNode.isExposed = false) (unprotected : global.protectedTags.contains anchorNode.tag = false)
    (observerPath : ((source_normal_projection tree default global.protectedTags).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (offset len : Size) (mode : ChildrenVisitMode) (sliceStart sliceLen : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum sliceStart sliceLen)
    (observerOwned : OwnedOn (Observer tree global.protectedTags observer)
      sliceStart (sliceStart+sliceLen) tree.locations)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestStop : offset.bytes.toNat + len.bytes.toNat ≤ sliceStart.toNat + sliceLen.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode
    result.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧
    Nonempty (GeneralBorrowReadRowRange.Positive result.tree global.protectedTags anchor selected maximum sliceStart sliceLen) ∧
    OwnedOn (Observer result.tree global.protectedTags observer)
      sliceStart (sliceStart+sliceLen) result.tree.locations := by
  let rowPred := fun current => GeneralBorrowReadRowRange.Row tree global.protectedTags anchor selected maximum current ∧
    Observer tree global.protectedTags observer current
  have rows : OwnedOn rowPred sliceStart (sliceStart+sliceLen) tree.locations := by
    intro position valid positiveWindow start stop
    exact ⟨positive.rows position valid positiveWindow start stop,observerOwned position valid positiveWindow start stop⟩
  have all : Every (Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  have bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    have ownerBounds := positive.bounds
    omega
  have fits : offset.bytes.toNat+len.bytes.toNat < 2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
  have ownerFits : sliceStart.toNat+sliceLen.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have requestUpper : (offset.bytes+len.bytes).toNat ≤ (sliceStart+sliceLen).toNat := by
    rw [UInt64.toNat_add,UInt64.toNat_add,Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt ownerFits]
    exact requestStop
  have localCallback : ∀ current, rowPred current → Runtime tree global.protectedTags current → ∀ range,
      let accessed := source_tree_access_at tree current (some anchor) .Read global.protectedTags mode range
      source_access_status accessed = none ∧ rowPred (source_access_location accessed) ∧
        Runtime tree global.protectedTags (source_access_location accessed) ∧ VacantFrame tree current (source_access_location accessed) := by
    intro current good runtime range
    obtain ⟨⟨currentRow⟩,⟨currentObserver⟩⟩ := good
    obtain ⟨complete,coherent,profile,possible,afterRow,afterObserver⟩ :=
      GeneralBorrowObserverDirectReadRow.access tree current global before anchor selected anchorNode present
        observer observerNode edge observerPresent hidden unprotected currentObserver observerPath maximum currentRow distinct order
        runtime.coherent runtime.profile runtime.possible short mode range
    refine ⟨complete,⟨afterRow,afterObserver⟩,⟨coherent,profile,possible⟩,?_⟩
    intro query missing
    rw [profile.vacant query missing,runtime.profile.vacant query missing]
  have composed := GeneralBorrowConcreteRangeInvariant.access tree global.protectedTags tag anchor tagPresent offset len
    .Read mode rowPred (Runtime tree global.protectedTags) (VacantFrame tree) (by intro current query missing;rfl)
    localCallback sliceStart (sliceStart+sliceLen) rows before.formed.well all bounds requestLower requestUpper
  have same := GeneralBorrowConcreteRangeInvariant.Contract.tree_eq composed
  obtain ⟨contract,runtime,sourceAfter⟩ := GeneralBorrowReadRowRange.access tree global before tag anchor selected maximum tagPresent
    offset len mode sliceStart sliceLen positive distinct order short requestLower requestStop
  refine ⟨contract.completed,runtime,sourceAfter,?_⟩
  intro position valid positiveWindow start stop
  have transported := observer_locations tree
    (tree.performBorrowAccessRange (.concrete tag) offset len .Read global.protectedTags mode).tree.locations
    _ global.protectedTags observer
    (composed.rows position valid positiveWindow start stop).2
  simpa only [←same] using transported

end DuplicatePrefix.GeneralBorrowObserverDirectReadRange
