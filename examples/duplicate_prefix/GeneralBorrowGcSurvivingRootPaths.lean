import duplicate_prefix.GeneralBorrowGcSurvivingPathFormation
import duplicate_prefix.GeneralBorrowGcForestComplete

namespace DuplicatePrefix.GeneralBorrowGcSurvivingRootPaths
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowGcForestRootFold DuplicatePrefix.GeneralBorrowGcSurvivingPaths
open DuplicatePrefix.GeneralBorrowGcRangeClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exact ancestry equivalences compose whenever no fresh node was allocated. -/
theorem compose (original middle after : UniValMap TreeNode)
    (first : Valid original middle) (second : Valid middle after)
    (origins : ∀ index node,after.get index = some node → ∃ old,middle.get index = some old) : Valid original after := by
  obtain ⟨_,before⟩ := first
  obtain ⟨depth,next⟩ := second
  refine ⟨depth,?_⟩
  intro source node present query value found
  obtain ⟨old,oldPresent⟩ := origins source node present
  obtain ⟨oldQuery,oldFound⟩ := origins query value found
  exact (next source node present query value found).trans (before source old oldPresent query oldQuery oldFound)

/-- One REAL source root callback composes its exact surviving paths with the
paths already formed by preceding component traversals. -/
theorem step (original tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : original.nodes.size ≤ 4294967296) (root : UniIndex) (member : root ∈ original.roots.toList)
    (live : Array BorTag) (ready : Ready original location protections tree) (paths : Valid original.nodes tree.nodes) :
    ∃ after,scan live root (none,tree) = .yield (none,after) ∧ Ready original location protections after ∧ Valid original.nodes after.nodes := by
  obtain ⟨after,actual,afterReady⟩ := GeneralBorrowGcForestRootFold.step original tree location protections fits root member live ready
  obtain ⟨depth⟩ := ready.depth
  obtain ⟨forest⟩ := ready.forest
  obtain ⟨node,present,_⟩ := ready.roots root member
  obtain ⟨same,component,localPaths⟩ := GeneralBorrowGcSurvivingPathFormation.children tree location protections forest depth ready.children root node present live
  have predicted : scan live root (none,tree) = .yield (none,same) := by simp only [scan,component]
  have equal := congrArg (fun result : ForInStep RootState => result.value.2) (actual.symm.trans predicted)
  change after = same at equal
  subst same
  have metadata := GeneralBorrowGcNodeMetadata.children tree root live
  rw [component] at metadata
  refine ⟨after,actual,afterReady,compose original.nodes tree.nodes after.nodes paths localPaths ?_⟩
  intro index value found
  obtain ⟨old,oldFound,_⟩ := metadata index value found
  exact ⟨old,oldFound⟩

theorem fold (original tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : original.nodes.size ≤ 4294967296) (items : List UniIndex)
    (included : items ⊆ original.roots.toList) (live : Array BorTag)
    (ready : Ready original location protections tree) (paths : Valid original.nodes tree.nodes) :
    ∃ after,forIn (m := Id) items (none,tree) (scan live) = (none,after) ∧ Ready original location protections after ∧ Valid original.nodes after.nodes := by
  induction items generalizing tree with
  | nil => exact ⟨tree,rfl,ready,paths⟩
  | cons root rest ih =>
    obtain ⟨middle,actual,middleReady,middlePaths⟩ := step original tree location protections fits root (included (by simp)) live ready paths
    obtain ⟨after,tail,finalReady,finalPaths⟩ := ih middle (by intro item member;exact included (List.mem_cons_of_mem _ member)) middleReady middlePaths
    refine ⟨after,?_,finalReady,finalPaths⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail

/-- FULL actual production GC preserves exact surviving ancestry on arbitrary
finite forests/root arrays, including repeated or empty lists. Original listed
roots are real parentless nodes; all subsequent root/graph data are formed by
the actual earlier traversals. No final path relation or successful GC premise. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (closed : GeneralBorrowGraph.ChildNodes tree) (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList,∃ node,tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (live : Array BorTag) :
    Valid tree.nodes (tree.removeUnreachableTags live).tree.nodes := by
  have ready : Ready tree location protections tree := ⟨⟨depth⟩,⟨forest⟩,closed,rfl,well,rfl,rootNodes⟩
  obtain ⟨after,folded,finalReady,paths⟩ := fold tree tree location protections fits tree.roots.toList
    (by intro item member;exact member) live ready (initial tree.nodes depth)
  unfold BorrowTree.removeUnreachableTags
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  have callback : scan = GeneralBorrowGcForestRootFold.scan live := rfl
  rw [callback,folded]
  dsimp only
  split <;> exact paths

end
end DuplicatePrefix.GeneralBorrowGcSurvivingRootPaths
