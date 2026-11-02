import duplicate_prefix.GeneralBorrowForestRejectedTreeData
import duplicate_prefix.GeneralBorrowForestEntrySharedAttach
import duplicate_prefix.GeneralBorrowForestEntrySharedTargetActivity
namespace DuplicatePrefix.GeneralBorrowForestRejectedTreeBuild
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def build (before : BorrowTree) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootTag : BorTag) (target primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (first : GeneralBorrowForestEntrySharedInput.First before tracker.global.protectedTags rootTag tracker.global.nextPointerTag
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag target primary extras offset len)
    (nonzero : len ≠ 0) (exprFree : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false) :
    GeneralBorrowForestRejectedTreeData.Data before tracker fresh rootTag target primary extras offset len first := by
  have different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag := by
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have bound : tracker.global.nextPointerTag.value.toNat < 18446744073709551615 := by simpa [UInt64.lt_iff_toNat_lt] using fresh
    change tracker.global.nextPointerTag.value.toNat = (tracker.global.nextPointerTag.value+1).toNat at eq
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)] at eq
    change tracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at eq
    omega
  let next := GeneralBorrowForestMixedSharedResources.build before tracker.global.protectedTags rootTag tracker.global.nextPointerTag
    (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag target primary extras offset len first.context first.covered
    first.tagPresent first.fresh first.slot first.fits nonzero first.well first.bounds (fun _ => true) first.allocator first.owned
    first.vacantClean first.helperFresh different first.room
  have targetResult := GeneralBorrowForestEntrySharedAttach.old_node before tracker.global.protectedTags tracker.global.nextPointerTag
    rootTag target primary extras offset len first.context first.covered first.tagPresent first.fresh first.slot first.fits (fun _ => true)
    nonzero first.well first.bounds first.owned target first.context.anchorNode first.context.anchorPresent
  let targetNode := Classical.choose targetResult
  have targetFacts := Classical.choose_spec targetResult
  have targetPresent := targetFacts.1
  have targetTag := targetFacts.2.1
  have exprResult := GeneralBorrowForestEntrySharedAttach.new_node before tracker.global.protectedTags tracker.global.nextPointerTag
    rootTag target primary extras offset len first.context first.covered first.tagPresent first.fresh first.slot first.fits (fun _ => true)
    nonzero first.well first.bounds first.owned
  let exprNode := Classical.choose exprResult
  have exprFacts := Classical.choose_spec exprResult
  have exprPresent := exprFacts.1
  have exprTag := exprFacts.2.1
  have attached := fun location => GeneralBorrowForestEntrySharedAttach.attach before tracker.global.protectedTags tracker.global.nextPointerTag
    rootTag target primary extras offset len first.context first.covered first.tagPresent first.fresh first.slot first.fits (fun _ => true)
    nonzero first.well first.bounds first.owned location location tracker.global.protectedTags
  have oldRoot : ∀ location, ((source_normal_projection before location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat := by
    intro location
    have lenNat : 0 < len.toNat := by have nz : len.toNat ≠ 0 := fun zero => nonzero (UInt64.toNat_inj.mp (by simpa using zero));omega
    have addition : (offset+len).toNat = offset.toNat+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bound := UInt64.toNat_lt_size before.locations.size.bytes;change before.locations.size.bytes.toNat < 18446744073709551616 at bound;have bounds := first.bounds;omega)]
    have inside : offset.toNat < before.locations.size.bytes.toNat := by have bounds := first.bounds;omega
    obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered before.locations first.well offset inside
    obtain ⟨data⟩ := first.owned position valid (by omega) (by omega) upper
    have root := data.base.rootPath
    rw [GeneralBorrowFreshSharedStagePaths.topology_any before before.locations.entries[position].data location tracker.global.protectedTags tracker.global.protectedTags] at root
    exact root
  have resources := GeneralBorrowForestForeignSharedResources.preserves before tracker.global.protectedTags rootTag tracker.global.nextPointerTag false
    target primary extras offset len .VisitChildrenOfAccessed first.context first.covered first.tagPresent first.fresh first.slot first.fits nonzero first.well first.bounds first.allocator
    (by intro position valid positive low high;obtain ⟨data⟩ := first.owned position valid positive low high;exact ⟨data.base⟩)
  exact {
    next := next,targetNode := targetNode,targetPresent := targetPresent,targetTag := targetTag.trans first.anchorTag,
    exprFree := by
      have same : next.context.anchorNode = exprNode := Option.some.inj (next.context.anchorPresent.symm.trans exprPresent)
      rw [same,exprTag]
      exact exprFree,
    prefixPath := by intro location;unfold GeneralBorrowForestRejectedTreeData.tree;rw [(attached location).childPath,(attached location).oldPath target.toNat (attached location).parentValid (attached location).parentDifferent],
    exprOutside := by intro location;exact (attached location).outsideOld target.toNat (attached location).parentValid (attached location).parentDifferent,
    rootPath := by intro location;unfold GeneralBorrowForestRejectedTreeData.tree;rw [(attached location).oldPath target.toNat (attached location).parentValid (attached location).parentDifferent];exact oldRoot location,
    targetActive := GeneralBorrowForestEntrySharedTargetActivity.preserves_target before tracker.global.protectedTags rootTag tracker.global.nextPointerTag offset len
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag target primary extras first nonzero first.bounds target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) first.active,
    capacity := resources.2.2.1 }
end
end DuplicatePrefix.GeneralBorrowForestRejectedTreeBuild
