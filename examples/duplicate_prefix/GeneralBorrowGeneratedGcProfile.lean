import duplicate_prefix.GeneralBorrowGcResourceFrame
import duplicate_prefix.GeneralBorrowGcPermissionPolicy
import duplicate_prefix.GeneralBorrowGcLiveNode
import duplicate_prefix.GeneralBorrowFullSharedResources
import duplicate_prefix.GeneralBorrowGcAllocatorFull

namespace DuplicatePrefix.GeneralBorrowGeneratedGcProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGcPermissionPolicy DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact Unique root and Frozen shared-leaf policy, including accessed/SIFA. -/
def expected (root query : UniIndex) : LocationState :=
  if query = root then GeneralBorrowWildcardLeaf.unique else GeneralBorrowFreshAnchor.sharedState

/-- The allocation-generated homogeneous profile establishes the GC policy. -/
theorem of_state (input : Input) (location : LocationTree) (good : State input location) :
    Policy (expected input.parent) input.tree := by
  refine ⟨?_,GeneralBorrowFullSharedEntryData.vacant_clean input location good⟩
  intro query node present position valid
  have zero : position = 0 := by
    rw [good.locations] at valid
    change position < 1 at valid
    omega
  subst position
  have known : location.perms.get query = some (expected input.parent query) := by
    by_cases same : query = input.parent
    · subst query
      simpa only [expected,ite_true] using good.profile.rootStored
    · simpa only [expected,ite_false,same] using good.profile.shared query node present same
  simpa only [good.locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using known

/-- Recover a complete generator permission profile on every stored range once
the distinguished root's presence has been established independently. -/
theorem profiles (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node) (good : Policy (expected root) tree) :
    Every (fun location => GeneralBorrowSharedGeneratorProfile.Profile tree location root) tree.locations := by
  intro position valid
  refine ⟨?_,?_,?_⟩
  · simpa only [expected,ite_true] using good.live root node present position valid
  · intro query value found different
    simpa only [expected,ite_false,different] using good.live query value found position valid
  · intro query vacant
    exact good.vacant query vacant position valid

/-- The explicit live-tag list retains the input root and any caller-supplied
additional live tags. It makes no dead-leaf or GC-success assumption. -/
def gc (input : Input) (extraLive : Array BorTag) :=
  input.tree.removeUnreachableTags (#[input.parentNode.tag] ++ extraLive)

/-- Full actual GC preserves exact generator permissions on every resulting
range, root index/tag and allocator coherence. This is data preservation even
on errors, not GC completion or graph/whole-invocation safety. -/
theorem collected (input : Input) (location : LocationTree) (good : State input location)
    (allocator : GeneralBorrowGcAllocator.Invariant input.tree) (extraLive : Array BorTag) :
    GeneralBorrowGcAllocator.Invariant (gc input extraLive).tree ∧
    GeneralBorrowGcLiveNode.Retained input.parent input.parentNode.tag (gc input extraLive).tree ∧
    Every (fun location => GeneralBorrowSharedGeneratorProfile.Profile (gc input extraLive).tree location input.parent)
      (gc input extraLive).tree.locations := by
  have held : (#[input.parentNode.tag] ++ extraLive).contains input.parentNode.tag = true := by simp
  have retained := GeneralBorrowGcLiveNode.preserves input.tree input.parent input.parentNode.tag
    (#[input.parentNode.tag] ++ extraLive) held ⟨input.parentNode,input.parentPresent,rfl⟩
  have policy := GeneralBorrowGcPermissionPolicy.preserves (expected input.parent) input.tree
    (#[input.parentNode.tag] ++ extraLive) (of_state input location good)
  obtain ⟨node,present,tagged⟩ := retained
  exact ⟨GeneralBorrowGcAllocatorFull.preserves input.tree _ allocator,⟨node,present,tagged⟩,
    profiles _ input.parent node present policy⟩

/-- Reserved map/node tags, node headroom and vacant Clean remain available
on the actual GC result, without assuming any successful GC outcome. -/
theorem resources {n : Nat} (input : Input) (location : LocationTree) (reserve : Fin n → BorTag)
    (initial : GeneralBorrowFullSharedResources.Resources input location reserve) (extraLive : Array BorTag) :
    GeneralBorrowGcResourceFrame.Frame reserve input.tree (gc input extraLive).tree ∧
    (∀ step, GeneralBorrowProtector.Fresh (gc input extraLive).tree (reserve step)) ∧
    (gc input extraLive).tree.nodes.size+4 ≤ 4294967295 ∧
    GeneralBorrowGcVacantClean.VacantClean (gc input extraLive).tree := by
  have frame := GeneralBorrowGcResourceFrame.preserves reserve input.tree (#[input.parentNode.tag] ++ extraLive) initial.futureMap
  have allocator := (collected input location initial.state initial.allocator extraLive).1
  have policy := GeneralBorrowGcPermissionPolicy.preserves (expected input.parent) input.tree
    (#[input.parentNode.tag] ++ extraLive) (of_state input location initial.state)
  exact ⟨frame,fun step => GeneralBorrowFullSharedResources.protector_fresh _ allocator.nodeTags _ (frame.fresh step),
    by change (input.tree.removeUnreachableTags _).tree.nodes.size+4 ≤ 4294967295;rw [frame.capacity];exact initial.nodeRoom,policy.vacant⟩

/-- Actual allocation and arbitrary finite full-slice shared generation followed
by actual full GC derive allocator and all-range permission profiles internally.
No initial profile, graph, allocator or operation-success premise is supplied.
GC completion and post-GC forest/call-entry formation remain separate obligations. -/
theorem generate_gc {n : Nat} (capacity : UInt64) (nonzero : capacity ≠ 0)
    (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin n → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) (extraLive : Array BorTag) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ final finalLocation, GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      GeneralBorrowFullSharedResources.Resources final finalLocation reserve ∧
      final.len = capacity ∧
      GeneralBorrowGcResourceFrame.Frame reserve final.tree (gc final extraLive).tree ∧
      (∀ step, GeneralBorrowProtector.Fresh (gc final extraLive).tree (reserve step)) ∧
      (gc final extraLive).tree.nodes.size+4 ≤ 4294967295 ∧
      GeneralBorrowGcVacantClean.VacantClean (gc final extraLive).tree ∧
      GeneralBorrowGcAllocator.Invariant (gc final extraLive).tree ∧
      GeneralBorrowGcLiveNode.Retained final.parent final.parentNode.tag (gc final extraLive).tree ∧
      Every (fun location => GeneralBorrowSharedGeneratorProfile.Profile (gc final extraLive).tree location final.parent)
        (gc final extraLive).tree.locations := by
  obtain ⟨final,location,history,resources,_⟩ := GeneralBorrowFullSharedResources.generate capacity nonzero
    rootTag childTag different tags unique rootUnused childUnused reserve reserved room
  have facts := collected final location resources.state resources.allocator extraLive
  have remaining := GeneralBorrowGeneratedGcProfile.resources final location reserve resources extraLive
  exact ⟨final,location,history,resources,history.length,remaining.1,remaining.2.1,remaining.2.2.1,remaining.2.2.2,facts⟩

end DuplicatePrefix.GeneralBorrowGeneratedGcProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGeneratedGcProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated GC profile dependency {dependency}"
