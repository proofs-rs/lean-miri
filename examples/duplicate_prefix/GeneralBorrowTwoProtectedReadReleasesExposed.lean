import duplicate_prefix.GeneralBorrowProtectedReadReleaseExposed
import duplicate_prefix.GeneralBorrowProtectedReadProfile
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowTwoProtectedReadReleasesExposed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real chronological suffix: both releases use the entire still-held table;
only their owning frame's final endCall removes the two registrations. -/
def operation (tree : BorrowTree) (global : GlobalState) (allocation : AllocId) (firstTag secondTag : BorTag) :=
  let first := global.addProtector {} allocation firstTag .StrongProtector
  let second := first.1.addProtector first.2 allocation secondTag .StrongProtector
  let releasedFirst := tree.releaseProtector firstTag second.1.protectedTags
  let releasedSecond := releasedFirst.tree.releaseProtector secondTag second.1.protectedTags
  (releasedFirst,releasedSecond,second.1.endCall second.2)

def protections (global : GlobalState) (allocation : AllocId) (firstTag secondTag : BorTag) :=
  ((global.addProtector {} allocation firstTag .StrongProtector).1.addProtector
    (global.addProtector {} allocation firstTag .StrongProtector).2 allocation secondTag .StrongProtector).1.protectedTags

/-- Both actual full release scans complete with active sibling reservations
allowed by the initial readable profile. The second tag remains globally held
during the first scan; the first tag remains held during the second scan.
Both exposure flags and initial readable/profile/tree resources are supported. This
is a release suffix, not yet a constructor-generated whole lifetime theorem. -/
theorem completes (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (first second root : UniIndex) (firstNode secondNode : TreeNode)
    (firstPresent : tree.nodeAt first = some firstNode) (secondPresent : tree.nodeAt second = some secondNode)
    (firstTagged : tree.indexOfTag firstNode.tag = some first) (secondTagged : tree.indexOfTag secondNode.tag = some second)
    (different : firstNode.tag ≠ secondNode.tag)
    (empty : global.protectedTags = {}) (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : Every (GeneralBorrowProtectedReadRelease.Profile tree (protections global allocation firstNode.tag secondNode.tag)) tree.locations) :
    let result := operation tree global allocation firstNode.tag secondNode.tag
    result.1.status = .Released ∧ result.2.1.status = .Released ∧ result.2.2.protectedTags = {} ∧
      Every (GeneralBorrowProtectedReadRelease.Profile result.2.1.tree (protections global allocation firstNode.tag secondNode.tag)) result.2.1.tree.locations := by
  let registeredFirst := global.addProtector {} allocation firstNode.tag .StrongProtector
  let registeredSecond := registeredFirst.1.addProtector registeredFirst.2 allocation secondNode.tag .StrongProtector
  let tags := registeredSecond.1.protectedTags
  have firstHeld : tags.contains firstNode.tag = true :=
    GeneralBorrowProtectedReadProfile.earlier_held global {} allocation allocation firstNode.tag secondNode.tag
      .StrongProtector .StrongProtector different
  have secondHeld : tags.contains secondNode.tag = true := by
    simp only [tags,registeredSecond,GlobalState.addProtector,ProtectedTags.contains,ProtectedTags.get_insert_same,Option.isSome_some]
  have firstRelease := GeneralBorrowProtectedReadReleaseExposed.release tree tags first root firstNode firstPresent firstTagged firstHeld
    fits depth children roots covered initial
  let middle := (tree.releaseProtector firstNode.tag tags).tree
  have frame : middle = {tree with locations := middle.locations} := firstRelease.2.1
  have nodes : middle.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have secondRelease := GeneralBorrowProtectedReadReleaseExposed.release middle tags second root secondNode
    (by rw [frame];exact secondPresent) (by rw [frame];exact secondTagged) secondHeld
    (by rw [nodes];exact fits) (GeneralBorrowFreshReadFrame.depth_on tree middle nodes depth)
    (by rw [frame];exact children) (by rw [frame];exact roots) (by rw [frame];exact covered) firstRelease.2.2
  have ended : (registeredSecond.1.endCall registeredSecond.2).protectedTags = {} := by
    simp [registeredFirst,registeredSecond,GlobalState.addProtector,FrameState.addProtector,GlobalState.endCall,empty,
      ProtectedTags.insert,ProtectedTags.remove]
  exact ⟨firstRelease.1,secondRelease.1,ended,secondRelease.2.2⟩
end DuplicatePrefix.GeneralBorrowTwoProtectedReadReleasesExposed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedReadReleasesExposed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two protected Read releases dependency {dependency}"
