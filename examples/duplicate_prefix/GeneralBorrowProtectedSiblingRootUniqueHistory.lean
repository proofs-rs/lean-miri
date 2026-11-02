import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseRootUnique
import duplicate_prefix.GeneralBorrowProtectedReleaseHistory
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingRootUniqueHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseRootUnique (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

open GeneralBorrowProtectedReleaseHistory (Tags execute AllReleased)
/-- Any finite full-table release history completes from initial readable
profiles and initially held mapped tags. Actual permission/cache updates retain
all metadata and the recurring profile, so no per-step success, tree, ownership
or retained-tag premise is supplied. Exposure flags may vary arbitrarily. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (mapped : Tags tree protections tags)
    (rootNode : TreeNode) (rootPresent : tree.nodeAt root = some rootNode)
    (initial : Every (Profile root tree protections) tree.locations) :
    AllReleased tree protections tags ∧
      execute tree protections tags = {tree with locations := (execute tree protections tags).locations} ∧
      Every (Profile root (execute tree protections tags) protections) (execute tree protections tags).locations := by
  induction tags generalizing tree with
  | nil => exact ⟨True.intro,rfl,initial⟩
  | cons tag rest ih =>
    obtain ⟨index,node,present,tagged,nodeTag,held⟩ := mapped tag (by simp)
    have released := GeneralBorrowProtectedSiblingReleaseRootUnique.release tree protections index root node present
      (by rw [nodeTag];exact tagged) (by rw [nodeTag];exact held) fits depth children roots covered rootNode rootPresent initial
    rw [nodeTag] at released
    let next := (tree.releaseProtector tag protections).tree
    have frame : next = {tree with locations := next.locations} := released.2.1
    have nodes : next.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
    have nextMapped : Tags next protections rest := by
      intro other member
      obtain ⟨query,value,found,lookup,valueTag,protectedTag⟩ := mapped other (by simp [member])
      exact ⟨query,value,by rw [frame];exact found,by rw [frame];exact lookup,valueTag,protectedTag⟩
    have tail := ih next (by rw [nodes];exact fits) (GeneralBorrowFreshReadFrame.depth_on tree next nodes depth)
      (by rw [frame];exact children) (by rw [frame];exact roots) (by rw [frame];exact covered) nextMapped (by rw [frame];exact rootPresent) released.2.2
    refine ⟨⟨released.1,tail.1⟩,?_,tail.2.2⟩
    change execute next protections rest = {tree with locations := (execute next protections rest).locations}
    rw [tail.2.1,frame]
/-- Arbitrary actual protector release history retains the original root's
stored Unique permission from its initial readable profile. -/
theorem unique (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (mapped : Tags tree protections tags)
    (rootNode : TreeNode) (rootPresent : tree.nodeAt root = some rootNode)
    (initial : Every (GeneralBorrowProtectedReadRelease.Profile tree protections) tree.locations)
    (unique : Every (GeneralBorrowConstructorPriorPermission.At root (some .Unique)) tree.locations) :
    Every (GeneralBorrowConstructorPriorPermission.At root (some .Unique)) (execute tree protections tags).locations := by
  have combined : Every (Profile root tree protections) tree.locations := fun position valid => ⟨initial position valid,unique position valid⟩
  have result := run tree protections tags root fits depth children roots covered mapped rootNode rootPresent combined
  exact fun position valid => (result.2.2 position valid).2

end DuplicatePrefix.GeneralBorrowProtectedSiblingRootUniqueHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingRootUniqueHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected release history dependency {dependency}"
