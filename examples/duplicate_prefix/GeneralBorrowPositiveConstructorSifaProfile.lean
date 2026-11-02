import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultReuse
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse
namespace DuplicatePrefix.GeneralBorrowPositiveConstructorSifaProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

namespace Shared

/-- Actual positive Shared append forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem append (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildShared.result input) location protections) (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildShared.append input).success,?_⟩
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent).defaultLocationState (protections.contains input.newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen false _
  have newInside : Consistent GeneralBorrowFreshAnchor.sharedState (protections.contains input.newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen true _
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildShared.index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) GeneralBorrowFreshAnchor.sharedState (GeneralBorrowFreshMetadataChildShared.mapping input)
    vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .Read
  rw [GeneralBorrowFreshMetadataChildShared.tree_eq input]
  exact formed

/-- Actual positive Shared reuse forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (protections : ProtectedTags)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildSharedReuse.result input) location protections) (GeneralBorrowFreshMetadataChildSharedReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).success,?_⟩
  have newDefault : Consistent (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent).defaultLocationState (protections.contains input.newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen false _
  have newInside : Consistent GeneralBorrowFreshAnchor.sharedState (protections.contains input.newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen true _
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildSharedReuse.index input) input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) GeneralBorrowFreshAnchor.sharedState (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
    input.vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .Read
  rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq input]
  exact formed

end Shared

namespace Default

/-- Actual positive Default append forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem append (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (alignedProtection : protections.contains input.newTag = false)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildDefault.result input) location protections) (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildDefault.append input).success,?_⟩
  have atEnd := GeneralBorrowFreshMetadataChildDefault.at_end input
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshDefaultChild.child input.newTag input.parent).defaultLocationState (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false
  have newInside : Consistent GeneralBorrowFreshDefaultChild.inside (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation true
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildDefault.index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) GeneralBorrowFreshDefaultChild.inside (GeneralBorrowFreshMetadataChildDefault.mapping input)
    vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .Read
  rw [GeneralBorrowFreshMetadataChildDefault.tree_eq input]
  exact formed

/-- Actual positive Default reuse forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) (protections : ProtectedTags)
    (alignedProtection : protections.contains input.newTag = false)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildDefaultReuse.result input) location protections) (GeneralBorrowFreshMetadataChildDefaultReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).success,?_⟩
  have newDefault : Consistent (GeneralBorrowFreshDefaultChild.child input.newTag input.parent).defaultLocationState (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false
  have newInside : Consistent GeneralBorrowFreshDefaultChild.inside (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation true
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildDefaultReuse.index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) GeneralBorrowFreshDefaultChild.inside (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input)
    input.vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .Read
  rw [GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq input]
  exact formed

end Default

namespace Protected

/-- Actual positive Protected append forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (alignedProtection : protections.contains input.newTag = true)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildMutable.result input) location protections) (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutable.append input).success,?_⟩
  have atEnd := GeneralBorrowFreshMetadataChildMutable.at_end input
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshChild.child input.newTag input.parent).defaultLocationState (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  have newInside : Consistent GeneralBorrowFreshChild.inside (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation true
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside (GeneralBorrowFreshMetadataChildMutable.mapping input)
    vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .None
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq input]
  exact formed

/-- Actual positive Protected reuse forms/preserves physical permission/SIFA
profiles and clean vacancies from initial profiles and source allocator data. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (protections : ProtectedTags)
    (alignedProtection : protections.contains input.newTag = true)
    (initial : Every (fun location => Profile input.tree location protections) input.tree.locations) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Every (fun location => Profile (GeneralBorrowFreshMetadataChildMutableReuse.result input) location protections) (GeneralBorrowFreshMetadataChildMutableReuse.result input).locations := by
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  have newDefault : Consistent (GeneralBorrowFreshChild.child input.newTag input.parent).defaultLocationState (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  have newInside : Consistent GeneralBorrowFreshChild.inside (protections.contains input.newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation true
  have formed := GeneralBorrowConstructorSifaProfile.stage input.tree protections (GeneralBorrowFreshMetadataChildMutableReuse.index input) input.parent input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) GeneralBorrowFreshChild.inside (GeneralBorrowFreshMetadataChildMutableReuse.mapping input)
    input.vacant input.parentPresent input.offset input.len input.well input.bounds initial newDefault newInside .None
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input]
  exact formed

end Protected

end DuplicatePrefix.GeneralBorrowPositiveConstructorSifaProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowPositiveConstructorSifaProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved positive constructor physical profile dependency {dependency}"
