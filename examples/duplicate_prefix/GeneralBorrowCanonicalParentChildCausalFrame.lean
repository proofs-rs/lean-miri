import duplicate_prefix.GeneralBorrowCanonicalSegmentSourceFrame
import duplicate_prefix.GeneralBorrowCanonicalChildCausalFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalParentChildCausalFrame
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open GeneralBorrowCausalGraphFormation GeneralBorrowCanonicalParentLoopCausalFrame
open GeneralBorrowCanonicalChildCausalFrame GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowTypedTreeUpdateCausalFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- The saved original tree is retained through arbitrary parent accesses;
this is a local proof invariant, not an additional valid-caller definition. -/
theorem snapshot_stable (target : AllocId) (original : BorrowTree) :
    FrameStable (Snapshot target original) := by
  intro id before after packet nodes mapping
  refine ⟨formed_stable id before after packet.1 nodes mapping,?_⟩
  intro same
  obtain ⟨oldNodes,oldMapping⟩ := packet.2 same
  exact ⟨nodes.trans oldNodes,mapping.trans oldMapping⟩

/-- Actual canonical parent accesses followed by child insertion retain causal
graph formation, on both success and error. The tag/runtime come from the
original allocator snapshot. No access, child or retag success is assumed.
This is the exact post-ensure suffix of factoredReborrow, not a claim that all
valid initial states or the entire canonical retag driver are covered. -/
theorem preserves {K U : Type} [DecidableEq K]
    (state : MachineHooks.State K U) (location : RetagPipeline.ResolvedLocation)
    (inside : DedupRangeMap Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (original : BorrowTree) (formed : Formed original) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original global)
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (provenance : location.parentProvenance = .concrete parentTag)
    (tagged : original.indexOfTag parentTag = some parent)
    (present : original.nodeAt parent = some node)
    (room : original.nodes.size+1 ≤ 4294967295)
    (before : AllTrees (Snapshot location.allocId original) state.machine.memory) :
    Holds (fun _ tree => Formed tree)
      ((do
        let _ ← forIn inside.iterAll () (fun segment _ =>
          GeneralBorrowCanonicalReborrowSource.sourceSegment location segment)
        childSuffix location inside policy global.nextPointerTag) state) := by
  have maintained := GeneralBorrowCanonicalSegmentSourceFrame.source_loop_preserves (Snapshot location.allocId original)
    (snapshot_stable location.allocId original) location inside state before
  cases actual : (forIn inside.iterAll () (fun segment _ =>
      GeneralBorrowCanonicalReborrowSource.sourceSegment location segment) : MachineHooks.M K U PUnit) state with
  | error error changed =>
    have after : AllTrees (Snapshot location.allocId original) changed.machine.memory := by
      simpa only [actual,Holds] using maintained
    simp only [bind,EStateM.bind,actual,Holds]
    exact fun row member => (after row member).1
  | ok value changed =>
    have after : AllTrees (Snapshot location.allocId original) changed.machine.memory := by
      simpa only [actual,Holds] using maintained
    simp only [bind,EStateM.bind,actual]
    exact GeneralBorrowCanonicalChildCausalFrame.preserves changed location inside policy original formed global runtime
      parentTag parent node provenance tagged present room after
end DuplicatePrefix.GeneralBorrowCanonicalParentChildCausalFrame
