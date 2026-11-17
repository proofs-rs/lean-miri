import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableActivity
import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedRelease
import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutConstructorReleaseData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowReleaseActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The real release predicate is false outside the bytewise active window.
This allows explicitly stored default reservations; absence is not required. -/
theorem outside_guard (tree : BorrowTree) (anchor : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree anchor ownerKind lower upper)
    (point : UInt64) (location : LocationTree) (atPoint : ValueAt tree.locations point location)
    (state : LocationState) (stored : location.perms.get anchor=some state)
    (outside : point.toNat<lower.toNat ∨ upper.toNat≤point.toNat) :
    (state.permission.associatedAccess.isSome && state.accessed)=false := by
  cases accessed : state.accessed with
  | false=>simp only [accessed,Bool.and_false]
  | true=>
    cases associated : state.permission.associatedAccess with
    | none=>simp only [associated,Option.isSome_none,Bool.false_and]
    | some kind=>
      have within:=active point location atPoint state stored accessed kind associated
      rcases outside with before | after <;>omega

/-- No callback can be triggered at a disjoint row in the actual release scan;
only the selected window needs the callback's permission contract. -/
theorem row_guard (tree : BorrowTree) (anchor : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed) (active : ActiveWithin tree anchor ownerKind lower upper)
    (position : Nat) (valid : position<tree.locations.entries.size) (state : LocationState)
    (stored : tree.locations.entries[position].data.perms.get anchor=some state)
    (outside : tree.locations.entries[position].range.stop.toNat≤lower.toNat ∨
      upper.toNat≤tree.locations.entries[position].range.start.toNat) :
    (state.permission.associatedAccess.isSome && state.accessed)=false := by
  have positive:=(GeneralRangeMapGeometry.facts tree.locations well (by omega)).2.1 position valid
  apply outside_guard tree anchor ownerKind lower upper active tree.locations.entries[position].range.start _
    ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr after

theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildShared.index input)=none) input.tree.locations) :
    ActiveWithin (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.index input)
      .Read input.offset (input.offset+input.len) := by
  exact GeneralBorrowExposedScopedSharedActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len
    input.nonzero input.well input.bounds clean

theorem mutable (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input)=none) input.tree.locations) :
    ActiveWithin (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.index input)
      .Read input.offset (input.offset+input.len) := by
  exact GeneralBorrowExposedScopedProtectedMutableActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.offset input.len
    input.nonzero input.well input.bounds clean

/-- Actual partial shared construction and release need raw owners only on the
selected interval. The outside inactive predicate follows from the constructor,
not from an allocation-wide owner or a successful callback assumption. -/
theorem shared_release (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex) (writable : Nat→Bool)
    (raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input protections selected head tail writable)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildShared.index input)=none) input.tree.locations) :
    ((GeneralBorrowFreshMetadataChildShared.result input).releaseProtector input.newTag protections).status=.Released ∧
    ActiveWithin (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.index input)
      .Read input.offset (input.offset+input.len) :=
  ⟨(GeneralBorrowExposedScopedWritableSharedRelease.release input protections selected head tail writable raw positive clean).1,shared input clean⟩

/-- The protected mutable constructor initially associates Read, including at
nonzero offsets. Its actual release plan is formed from the bounded window. -/
theorem mutable_release (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input)=none) input.tree.locations) :
    ((GeneralBorrowFreshMetadataChildMutable.result input).releaseProtector input.newTag protections).status=.Released ∧
    ActiveWithin (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.index input)
      .Read input.offset (input.offset+input.len) := by
  let plan:=GeneralBorrowExposedScopedWritableAsMutConstructorReleaseData.build input protections selected head tail raw positive clean
  exact ⟨GeneralBorrowExposedScopedWritableAsMutReleasePlan.released _ _ _ plan,mutable input clean⟩

end
end DuplicatePrefix.GeneralBorrowExposedScopedWindowReleaseActivity
