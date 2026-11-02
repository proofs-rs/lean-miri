import duplicate_prefix.GeneralBorrowProtectedPendingReleaseCache
import duplicate_prefix.GeneralBorrowProtectedReleaseHistory
import duplicate_prefix.StackPopRelease
namespace DuplicatePrefix.GeneralBorrowProtectedReleaseCacheHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedReleaseHistory (Tags execute AllReleased)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The virtual table records source exposure adjustments already performed;
the actual table passed to every permission operation remains unchanged. -/
def pendingAfter (virtual : ProtectedTags) : List BorTag → ProtectedTags
  | [] => virtual
  | tag::rest => pendingAfter (virtual.remove tag) rest

/-- Arbitrary finite, duplicate-free full-table release schedules preserve
coherent counts under the correctly threaded virtual table. Previously released
exposed permissions must be Read-stable; here this is formed uniformly for all
exposed nodes initially and preserved by each source Read. Unconflicted exposed
reservations are deliberately excluded, rather than silently treated as safe. -/
theorem run (tree : BorrowTree) (actual virtual : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (distinct : tags.Nodup) (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (mapped : Tags tree actual tags) (virtualHeld : ∀ tag ∈ tags,virtual.contains tag = true)
    (initial : Every (Profile tree actual) tree.locations)
    (coherent : Every (fun location => LocationCoherent tree location virtual) tree.locations)
    (stable : Every (GeneralBorrowProtectedReadStable.AllExposed tree) tree.locations) :
    AllReleased tree actual tags ∧
      execute tree actual tags = {tree with locations := (execute tree actual tags).locations} ∧
      Every (Profile (execute tree actual tags) actual) (execute tree actual tags).locations ∧
      Every (fun location => LocationCoherent (execute tree actual tags) location (pendingAfter virtual tags)) (execute tree actual tags).locations ∧
      Every (GeneralBorrowProtectedReadStable.AllExposed (execute tree actual tags)) (execute tree actual tags).locations := by
  induction tags generalizing tree virtual with
  | nil => exact ⟨True.intro,rfl,initial,coherent,stable⟩
  | cons tag rest ih =>
    obtain ⟨index,node,present,tagged,nodeTag,held⟩ := mapped tag (by simp)
    have released := GeneralBorrowProtectedPendingReleaseCache.release tree actual virtual index root node present
      (by rw [nodeTag];exact tagged) (by rw [nodeTag];exact held) (by rw [nodeTag];exact virtualHeld tag (by simp))
      nodeTags fits depth children roots covered initial coherent stable
    rw [nodeTag] at released
    let next := (tree.releaseProtector tag actual).tree
    have frame : next = {tree with locations := next.locations} := released.2.1
    have nodes : next.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
    have nextMapped : Tags next actual rest := by
      intro other member
      obtain ⟨query,value,found,lookup,valueTag,held⟩ := mapped other (by simp [member])
      exact ⟨query,value,by rw [frame];exact found,by rw [frame];exact lookup,valueTag,held⟩
    have nextVirtual : ∀ other ∈ rest,(virtual.remove tag).contains other = true := by
      intro other member
      have different : other ≠ tag := by
        intro same;subst other;exact (List.nodup_cons.mp distinct).1 member
      unfold ProtectedTags.contains
      rw [GeneralBorrowProtectorCacheMap.remove_other virtual tag other different]
      exact virtualHeld other (by simp [member])
    have nextNodeTags : ∀ query value,next.nodeAt query = some value → next.indexOfTag value.tag = some query := by
      intro query value found
      rw [frame] at found ⊢
      exact nodeTags query value found
    have tail := ih next (virtual.remove tag) (List.nodup_cons.mp distinct).2 (by rw [nodes];exact fits)
      (GeneralBorrowFreshReadFrame.depth_on tree next nodes depth) (by rw [frame];exact children)
      (by rw [frame];exact roots) (by rw [frame];exact covered) nextNodeTags nextMapped nextVirtual
      released.2.2.1 released.2.2.2.1 released.2.2.2.2
    refine ⟨⟨released.1,tail.1⟩,?_,tail.2.2.1,tail.2.2.2.1,tail.2.2.2.2⟩
    change execute next actual rest = {tree with locations := (execute next actual rest).locations}
    rw [tail.2.1,frame]

/-- The virtual table after the exact frame order equals the real endCall
bookkeeping table. This equality concerns tag maps, not permission operations. -/
theorem pending_end_call (global : GlobalState) (frame : FrameState) (id : AllocId) (tags : List BorTag)
    (rows : frame.protectedTags.toList = tags.map (fun tag => (id,tag))) :
    (global.endCall frame).protectedTags = pendingAfter global.protectedTags tags := by
  unfold GlobalState.endCall
  simp only [←Array.foldl_toList,rows]
  have fold : ∀ tags (protections : ProtectedTags),
      (tags.map (fun tag => (id,tag))).foldl (fun current pair => current.remove pair.2) protections = pendingAfter protections tags := by
    intro tags
    induction tags with
    | nil => intro protections;rfl
    | cons tag rest ih => intro protections;exact ih (protections.remove tag)
  exact fold tags global.protectedTags
end DuplicatePrefix.GeneralBorrowProtectedReleaseCacheHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReleaseCacheHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected cache release history dependency {dependency}"
