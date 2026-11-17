import duplicate_prefix.GeneralBorrowExposurePermissionUpdate
import duplicate_prefix.GeneralBorrowTagMap
namespace DuplicatePrefix.GeneralBorrowProtectorCacheMap
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Removing one actual protector retains every other tag's lookup, including
maps with arbitrary existing entries and both protector strengths. -/
theorem remove_other (protections : ProtectedTags) (tag query : BorTag) (different : query ≠ tag) :
    (protections.remove tag).get query = protections.get query := by
  have predicate : (fun entry : BorTag × ProtectorKind => decide ((entry.1 != tag) = true ∧ (entry.1 == query) = true)) =
      (fun entry => entry.1 == query) := by
    funext entry
    by_cases same : entry.1 = query
    · simp [same,different]
    · simp [same]
  simp only [ProtectedTags.get,ProtectedTags.remove,Array.find?_filter,predicate]

theorem insert_other (protections : ProtectedTags) (tag query : BorTag) (kind : ProtectorKind) (different : query ≠ tag) :
    (protections.insert tag kind).get query = protections.get query := by
  change (((protections.remove tag).entries.push (tag,kind)).find? (fun entry => entry.1 == query)).map Prod.snd = _
  rw [Array.find?_push]
  simp only [beq_eq_false_iff_ne.mpr (Ne.symm different),Bool.false_eq_true,↓reduceIte,Option.or_none]
  exact remove_other protections tag query different

/-- Cache coherence depends on protector membership only at exposed nodes. -/
theorem frame (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (initial : LocationCoherent tree location before)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true →
      after.contains node.tag = before.contains node.tag) : LocationCoherent tree location after := by
  intro query kind
  rw [initial query kind]
  apply congrArg UInt16.ofNat
  unfold cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  cases exposed : row.2.isExposed with
  | false => simp only [contributes,exposed,Bool.false_and]
  | true => simp only [contributes,effective,same row.1 row.2 present exposed]

/-- Actual insertion of a protector for a fresh or currently unexposed tag
preserves all caches. Exposed existing tags are deliberately excluded. -/
theorem register (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (kind : ProtectorKind) (initial : LocationCoherent tree location protections)
    (hidden : ∀ index node,tree.nodeAt index = some node → node.tag = tag → node.isExposed = false) :
    LocationCoherent tree location (protections.insert tag kind) := by
  apply frame tree location protections _ initial
  intro index node present exposed
  have different : node.tag ≠ tag := by
    intro same
    have unexposed := hidden index node present same
    rw [unexposed] at exposed
    cases exposed
  unfold ProtectedTags.contains
  rw [insert_other protections tag node.tag kind different]

/-- Actual protector removal for a currently unexposed tag also leaves all
count witnesses unchanged; its held permission strength is unobservable here. -/
theorem remove_hidden (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (initial : LocationCoherent tree location protections)
    (hidden : ∀ index node,tree.nodeAt index = some node → node.tag = tag → node.isExposed = false) :
    LocationCoherent tree location (protections.remove tag) := by
  apply frame tree location protections _ initial
  intro index node present exposed
  have different : node.tag ≠ tag := by
    intro same
    have unexposed := hidden index node present same
    rw [unexposed] at exposed
    cases exposed
  unfold ProtectedTags.contains
  rw [remove_other protections tag node.tag different]

/-- Actual global/frame protector registration for a fresh tag preserves
all existing tree caches. Node/tag accounting and real map freshness derive
that no present node can already carry the registered tag. -/
theorem register_fresh_global (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (initial : DuplicatePrefix.GeneralRangeMapState.Every
      (fun location => LocationCoherent tree location global.protectedTags) tree.locations) :
    DuplicatePrefix.GeneralRangeMapState.Every (fun location => LocationCoherent tree location
      (global.addProtector frame allocation tag kind).1.protectedTags) tree.locations := by
  have absent : tree.indexOfTag tag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh,Option.map_none]
  intro position valid
  apply register tree _ global.protectedTags tag kind (initial position valid)
  intro index node present same
  have lookup := nodeTags index node present
  rw [same,absent] at lookup
  cases lookup

end DuplicatePrefix.GeneralBorrowProtectorCacheMap
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectorCacheMap.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protector/cache map dependency {dependency}"
