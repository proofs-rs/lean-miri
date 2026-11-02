import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseCache
import duplicate_prefix.GeneralBorrowProtectedReleaseCacheHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedReleaseHistory (Tags execute AllReleased)
open DuplicatePrefix.GeneralBorrowProtectedReleaseCacheHistory (pendingAfter)
open DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseStable (ForTags)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Full-table release/cache history with a selected stable prior-tag set.
Every nonfinal release tag must belong to that set; the final tag may be an
exposed, still-unconflicted reservation. No stability is demanded after its
virtual removal, because no later permission operation follows it. -/
theorem run (tree : BorrowTree) (actual virtual : ProtectedTags) (tags safeTags : List BorTag) (root : UniIndex)
    (coverage : ∀ tag,actual.contains tag ≠ virtual.contains tag → tag ∈ safeTags)
    (prior : ∀ tag ∈ tags.dropLast,tag ∈ safeTags) (distinct : tags.Nodup)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (mapped : Tags tree actual tags) (virtualHeld : ∀ tag ∈ tags,virtual.contains tag = true)
    (initial : Every (Profile tree actual) tree.locations)
    (coherent : Every (fun location => LocationCoherent tree location virtual) tree.locations)
    (stable : Every (ForTags safeTags tree) tree.locations) :
    AllReleased tree actual tags ∧
      execute tree actual tags = {tree with locations := (execute tree actual tags).locations} ∧
      Every (Profile (execute tree actual tags) actual) (execute tree actual tags).locations ∧
      Every (fun location => LocationCoherent (execute tree actual tags) location (pendingAfter virtual tags)) (execute tree actual tags).locations ∧
      Every (ForTags safeTags (execute tree actual tags)) (execute tree actual tags).locations := by
  induction tags generalizing tree virtual with
  | nil => exact ⟨True.intro,rfl,initial,coherent,stable⟩
  | cons tag rest ih =>
    obtain ⟨index,node,present,tagged,nodeTag,held⟩ := mapped tag (by simp)
    have released := GeneralBorrowProtectedSiblingReleaseCache.release tree actual virtual safeTags coverage index root node present
      (by rw [nodeTag];exact tagged) (by rw [nodeTag];exact held) (by rw [nodeTag];exact virtualHeld tag (by simp))
      nodeTags fits depth children roots covered initial coherent stable
    rw [nodeTag] at released
    let next := (tree.releaseProtector tag actual).tree
    have frame : next = {tree with locations := next.locations} := released.2.1
    have nodes : next.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
    cases rest with
    | nil => exact ⟨⟨released.1,True.intro⟩,released.2.1,released.2.2.1,released.2.2.2.1,released.2.2.2.2⟩
    | cons later tail =>
      have currentSafe : tag ∈ safeTags := prior tag (by simp)
      have nextCoverage : ∀ query,actual.contains query ≠ (virtual.remove tag).contains query → query ∈ safeTags := by
        intro query different
        by_cases same : query = tag
        · subst query;exact currentSafe
        · have flags : (virtual.remove tag).contains query = virtual.contains query := by
            unfold ProtectedTags.contains
            rw [GeneralBorrowProtectorCacheMap.remove_other virtual tag query same]
          exact coverage query (fun equal => different (equal.trans flags.symm))
      have nextPrior : ∀ query ∈ (later::tail).dropLast,query ∈ safeTags := by
        intro query member
        exact prior query (by simp only [List.dropLast_cons_cons,List.mem_cons];exact Or.inr member)
      have nextMapped : Tags next actual (later::tail) := by
        intro other member
        obtain ⟨query,value,found,lookup,valueTag,held⟩ := mapped other (by simp [member])
        exact ⟨query,value,by rw [frame];exact found,by rw [frame];exact lookup,valueTag,held⟩
      have nextVirtual : ∀ other ∈ later::tail,(virtual.remove tag).contains other = true := by
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
      have after := ih next (virtual.remove tag) nextCoverage nextPrior (List.nodup_cons.mp distinct).2 (by rw [nodes];exact fits)
        (GeneralBorrowFreshReadFrame.depth_on tree next nodes depth) (by rw [frame];exact children)
        (by rw [frame];exact roots) (by rw [frame];exact covered) nextNodeTags nextMapped nextVirtual
        released.2.2.1 released.2.2.2.1 released.2.2.2.2
      refine ⟨⟨released.1,after.1⟩,?_,after.2.2.1,after.2.2.2.1,after.2.2.2.2⟩
      change execute next actual (later::tail) = {tree with locations := (execute next actual (later::tail)).locations}
      rw [after.2.1,frame]

/-- Source-order releases with only the initially earlier tags conflicted.
The last selected exposed reservation is unrestricted by the stable predicate;
a one-element history therefore needs no stable permission assumption at all. -/
theorem complete (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (distinct : tags.Nodup) (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (mapped : Tags tree protections tags) (initial : Every (Profile tree protections) tree.locations)
    (coherent : Every (fun location => LocationCoherent tree location protections) tree.locations)
    (stableEarlier : Every (ForTags tags.dropLast tree) tree.locations) :
    AllReleased tree protections tags ∧
      Every (fun location => LocationCoherent (execute tree protections tags) location (pendingAfter protections tags))
        (execute tree protections tags).locations := by
  have held : ∀ tag ∈ tags,protections.contains tag = true := by
    intro tag member;obtain ⟨_,_,_,_,_,held⟩ := mapped tag member;exact held
  have result := run tree protections protections tags tags.dropLast root (fun _ different => False.elim (different rfl))
    (fun _ member => member) distinct fits depth children roots covered nodeTags mapped held initial coherent stableEarlier
  exact ⟨result.1,result.2.2.2.1⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sibling release cache history dependency {dependency}"
