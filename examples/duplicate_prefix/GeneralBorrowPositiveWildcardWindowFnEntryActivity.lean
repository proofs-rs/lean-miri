import duplicate_prefix.GeneralBorrowPositiveWildcardWindowOriginalInput
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowArgumentCopy
import duplicate_prefix.GeneralBorrowStructuralHistoryActivityGenericRange
import duplicate_prefix.GeneralBorrowSparseExposedLeafCleanRange
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFnEntryActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowFreshActiveWithin GeneralBorrowStructuralHistoryActivityGenericRange
attribute [local irreducible] UniValMap.insert UniValMap.orInsert
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The actual root constructor materializes permissions only in the reference
window; its lazy outside default does not create release activity. -/
theorem construct_read (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (vacant : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get index=none) tree.locations) :
    ActiveWithin (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len)
      index .Read offset (offset+len) := by
  have initial:=GeneralBorrowStructuralHistoryActivityGenericRange.clean tree index .Read offset (offset+len) vacant
  have actual:=GeneralBorrowStructuralHistoryActivityGenericRange.materialize tree index ChildBorrow.fnEntryLocation .Read offset (offset+len)
    (Size.ofBytes offset) (Size.ofBytes len) well bounds (Nat.le_refl _) (Nat.le_refl _) initial (by intro mode accessed kind associated;cases associated;rfl)
  exact actual

variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Initial raw source rows and vacant-slot hygiene derive the real original
FnEntry target's activity confinement after its actual NONE Read/constructor. -/
theorem source_read (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    ActiveWithin (GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.offset s.len)
      ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ .Read s.offset (s.offset+s.len) := by
  let tree:=s.entry.allocation.extra
  let protections:=(TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags
  let read:=tree.performBorrowAccessRange .wildcard (Size.ofBytes s.offset) (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  let index : UniIndex:=⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have indexNat : index.toNat=tree.nodes.size := by
    change (UInt32.ofNat tree.tagMapping.mapping.size).toNat=tree.nodes.size
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by have fits:=s.fits;change tree.tagMapping.mapping.size≤4294967295 at fits;omega),s.mapAligned]
    rfl
  have vacant : tree.nodes.get index=none := by unfold UniValMap.get;rw [indexNat];simp [UniValMap.size]
  have bounds : s.offset.toNat+s.len.toNat≤tree.locations.size.bytes.toNat := by rw [s.allocationCapacity];exact s.bounds
  have fits : s.offset.toNat+s.len.toNat<18446744073709551616 := by
    have cap:=UInt64.toNat_lt_size s.capacity;have request:=s.bounds;change s.capacity.toNat<18446744073709551616 at cap;omega
  have upper : (s.offset+s.len).toNat≤s.capacity.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits];exact s.bounds
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) 0 s.capacity tree.locations := by
    intro position valid _ _ _;exact s.sourceRaw position valid
  have good:=GeneralBorrowSparseExposedLeafRange.access tree protections s.head s.extraRoots s.leafGeometry (Size.ofBytes s.offset) (Size.ofBytes s.len)
    .Read .VisitChildrenOfAccessed s.initialState.well 0 s.capacity owned bounds (by change 0≤s.offset.toNat;omega) upper
  have cleanAfter:=GeneralBorrowSparseExposedLeafCleanRange.ranged tree protections s.head index s.extraRoots s.leafGeometry
    (Size.ofBytes s.offset) (Size.ofBytes s.len) .Read .VisitChildrenOfAccessed vacant (clean index vacant) s.initialState.well 0 s.capacity owned bounds
    (by change 0≤s.offset.toNat;omega) upper
  exact construct_read read.tree ⟨tree.tagMapping.mapping.push (s.tracker.global.nextPointerTag,index),tree.tagMapping.deassigned⟩ index s.tracker.global.nextPointerTag s.offset s.len good.2.2.1
    (by rw [good.2.2.2];exact bounds) cleanAfter.2
theorem source (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    ActiveWithin (GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.offset s.len)
      ⟨UInt32.ofNat s.entry.allocation.extra.tagMapping.mapping.size⟩ .Write s.offset (s.offset+s.len) :=
  GeneralBorrowFreshActiveWithin.to_write _ _ _ _ (source_read s clean)
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFnEntryActivity
