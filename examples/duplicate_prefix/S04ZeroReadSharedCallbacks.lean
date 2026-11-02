import duplicate_prefix.S04ZeroReadSharedAttach
import duplicate_prefix.S04ZeroReadSifaCallbacks
import duplicate_prefix.S04ZeroReadSharedEntry
import duplicate_prefix.GeneralBorrowConstructorSifaProfile

namespace DuplicatePrefix.S04ZeroReadSharedCallbacks
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowNodeUpdate
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- Runtime metadata for the actual zero-constructor stage: original range
rows, coherent fresh-index reuse, and the genuine parent-depth certificate. -/
noncomputable def stage_depth (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) :
    GeneralBorrowExposure.ParentDepth input.stage.nodes :=
  GeneralBorrowFreshMetadata.parent_depth input.after input.stage
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read).symm input.afterDepth

theorem stage_profile (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag)
    (location : LocationTree) (protections : ProtectedTags)
    (before : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    GeneralBorrowLocationSifaConsistency.Profile input.stage location protections := by
  have freshDefault : GeneralBorrowSifaPermissionConsistency.Consistent
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent).defaultLocationState (protections.contains tag) := by
    change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.Frozen,false,.Read⟩ (protections.contains tag)
    cases held : protections.contains tag
    · exact ⟨.Read,rfl,by decide⟩
    · exact ⟨.Read,rfl,by decide⟩
  have attached := GeneralBorrowConstructorSifaProfile.attach tree location protections input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present before freshDefault
  exact ⟨attached.present,attached.vacant⟩

/-- Full callback authorization survives the REAL zero shared Frozen
newChild, in both allocator branches. The constructor parent may be inside
this callback's support: the fresh leaf is then added to support. No old
component separation, operation success, or post-operation safety is assumed. -/
theorem actual (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) (offset : UInt64) (isProtected : Bool)
    (protections : ProtectedTags) (position : Nat) (valid : position < tree.locations.entries.size)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree (tree.locations.entries[position]'valid).data protections)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (old : Authorization tree (tree.locations.entries[position]'valid).data protections root rootPosition maximum kind support) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    result.outcome = .ok () ∧ ∃ nextValid : position < result.tree.locations.entries.size,
      Authorization result.tree (result.tree.locations.entries[position]'nextValid).data protections root rootPosition maximum kind
        (S04ZeroReadSharedAttach.extended support input.parent input.index) := by
  have stageDepth := stage_depth tree parentTag tag input
  have size : tree.nodes.size ≤ (attachedNodes tree.nodes input.index input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).size := by
    change tree.nodes.size ≤ input.stage.nodes.size
    rw [input.stage_size]
    omega
  have first := S04ZeroReadSharedAttach.authorization tree input.depth input.index input.parent input.parentNode tag input.vacant
    input.present size stageDepth (tree.locations.entries[position]'valid).data protections (profile.vacant input.index input.vacant)
    root rootPosition maximum kind support old
  have staged : Authorization input.stage (tree.locations.entries[position]'valid).data protections root rootPosition maximum kind
      (S04ZeroReadSharedAttach.extended support input.parent input.index) :=
    GeneralBorrowSharedCallbacksData.authorization_context _ input.mapping tree.locations _ protections root rootPosition maximum kind _ first
  rw [input.child offset isProtected]
  refine ⟨rfl,?_⟩
  exact S04ZeroReadSifaCallbacks.at_row input.stage stageDepth input.parent protections position valid
    (stage_profile tree parentTag tag input _ protections profile) root rootPosition maximum kind _ staged

end DuplicatePrefix.S04ZeroReadSharedCallbacks
