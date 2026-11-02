import duplicate_prefix.GeneralBorrowProtectedReadReleaseExposed
namespace DuplicatePrefix.GeneralBorrowProtectedReleaseHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- All selected release tags are initially mapped to actual held nodes. -/
def Tags (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) : Prop :=
  ∀ tag ∈ tags,∃ index node,tree.nodeAt index = some node ∧ tree.indexOfTag tag = some index ∧
    node.tag = tag ∧ protections.contains tag = true

/-- Actual source releases in list order, always using the entire unchanged
protector table. The table is removed by endCall only after this history. -/
def execute (tree : BorrowTree) (protections : ProtectedTags) : List BorTag → BorrowTree
  | [] => tree
  | tag::rest => execute (tree.releaseProtector tag protections).tree protections rest

def AllReleased (tree : BorrowTree) (protections : ProtectedTags) : List BorTag → Prop
  | [] => True
  | tag::rest => (tree.releaseProtector tag protections).status = .Released ∧
      AllReleased (tree.releaseProtector tag protections).tree protections rest

/-- Any finite full-table release history completes from initial readable
profiles and initially held mapped tags. Actual permission/cache updates retain
all metadata and the recurring profile, so no per-step success, tree, ownership
or retained-tag premise is supplied. Exposure flags may vary arbitrarily. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) (root : UniIndex)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (mapped : Tags tree protections tags)
    (initial : Every (Profile tree protections) tree.locations) :
    AllReleased tree protections tags ∧
      execute tree protections tags = {tree with locations := (execute tree protections tags).locations} ∧
      Every (Profile (execute tree protections tags) protections) (execute tree protections tags).locations := by
  induction tags generalizing tree with
  | nil => exact ⟨True.intro,rfl,initial⟩
  | cons tag rest ih =>
    obtain ⟨index,node,present,tagged,nodeTag,held⟩ := mapped tag (by simp)
    have released := GeneralBorrowProtectedReadReleaseExposed.release tree protections index root node present
      (by rw [nodeTag];exact tagged) (by rw [nodeTag];exact held) fits depth children roots covered initial
    rw [nodeTag] at released
    let next := (tree.releaseProtector tag protections).tree
    have frame : next = {tree with locations := next.locations} := released.2.1
    have nodes : next.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
    have nextMapped : Tags next protections rest := by
      intro other member
      obtain ⟨query,value,found,lookup,valueTag,protectedTag⟩ := mapped other (by simp [member])
      exact ⟨query,value,by rw [frame];exact found,by rw [frame];exact lookup,valueTag,protectedTag⟩
    have tail := ih next (by rw [nodes];exact fits) (GeneralBorrowFreshReadFrame.depth_on tree next nodes depth)
      (by rw [frame];exact children) (by rw [frame];exact roots) (by rw [frame];exact covered) nextMapped released.2.2
    refine ⟨⟨released.1,tail.1⟩,?_,tail.2.2⟩
    change execute next protections rest = {tree with locations := (execute next protections rest).locations}
    rw [tail.2.1,frame]
end DuplicatePrefix.GeneralBorrowProtectedReleaseHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReleaseHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected release history dependency {dependency}"
