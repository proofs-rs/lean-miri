import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowSifaProtectionProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Physical profiles depend on node metadata and stored permissions, while
other tree and location fields are framed explicitly. -/
theorem nodes (before after : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (same : after.nodes = before.nodes) (initial : Profile before location protections) : Profile after location protections := by
  refine ⟨?_,?_⟩
  · intro index node present
    change after.nodes.get index = some node at present
    rw [same] at present
    exact initial.present index node present
  · intro index vacant
    rw [same] at vacant
    exact initial.vacant index vacant

theorem perms (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (same : after.perms = before.perms) (initial : Profile tree before protections) : Profile tree after protections := by
  refine ⟨?_,?_⟩
  · intro index node present
    rw [same]
    exact initial.present index node present
  · intro index vacant
    rw [same]
    exact initial.vacant index vacant

/-- Fresh actual global/frame protector registration preserves physical SIFA
profiles on the existing graph. Real map freshness and node/tag accounting
exclude an already-present node with this tag; global absence is not inferred. -/
theorem register (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (initial : Every (fun location => Profile tree location global.protectedTags) tree.locations) :
    Every (fun location => Profile tree location (global.addProtector frame allocation tag kind).1.protectedTags) tree.locations := by
  have absent : tree.indexOfTag tag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh,Option.map_none]
  intro position valid
  refine ⟨?_,(initial position valid).vacant⟩
  intro query node present
  have different : node.tag ≠ tag := by
    intro same
    have lookup := nodeTags query node present
    rw [same,absent] at lookup;cases lookup
  have heldSame : (global.addProtector frame allocation tag kind).1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    simp only [GlobalState.addProtector,ProtectedTags.contains,
      GeneralBorrowProtectorCacheMap.insert_other global.protectedTags tag node.tag kind different]
  rw [heldSame]
  exact (initial position valid).present query node present

/-- Actual protector deletion preserves the scalar SIFA profile and Clean,
without assuming cache coherence or the removed tag's prior membership. -/
theorem remove (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (tag : BorTag)
    (initial : Profile tree location protections) : Profile tree location (protections.remove tag) := by
  refine ⟨?_,initial.vacant⟩
  intro index node present
  have formed := initial.present index node present
  by_cases same : node.tag = tag
  · rw [same] at formed ⊢
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    cases held : protections.contains tag with
    | false => simpa only [held] using formed
    | true => exact GeneralBorrowSifaPermissionConsistency.unprotect _ (by simpa only [held] using formed)
  · simpa only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.remove_other protections tag node.tag same] using formed

/-- Source endCall folds all frame removals in actual array order. Unlike
exposure-cache cardinality, scalar permission/SIFA bounds survive arbitrary
intermediate protector removals directly. -/
theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (initial : Every (fun location => Profile tree location global.protectedTags) tree.locations) :
    Every (fun location => Profile tree location (global.endCall frame).protectedTags) tree.locations := by
  have fold : ∀ (rows : List (AllocId × BorTag)) (protections : ProtectedTags) (location : LocationTree),
      Profile tree location protections → Profile tree location (rows.foldl (fun tags pair => tags.remove pair.2) protections) := by
    intro rows
    induction rows with
    | nil => intro protections location good;exact good
    | cons row rest ih =>
      intro protections location good
      exact ih (protections.remove row.2) location (remove tree location protections row.2 good)
  intro position valid
  simpa only [GlobalState.endCall,Array.foldl_toList] using
    fold frame.protectedTags.toList global.protectedTags tree.locations.entries[position].data (initial position valid)

end DuplicatePrefix.GeneralBorrowSifaProtectionProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSifaProtectionProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protector SIFA profile dependency {dependency}"
