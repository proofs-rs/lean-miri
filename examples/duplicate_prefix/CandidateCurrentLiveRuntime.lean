import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.DuplicatePrefixCallSpecification

/-! Current live-tree runtime and numeric data from the existing explicit state
and resource candidates. No ordinary-input admission is claimed. -/
namespace DuplicatePrefix.CandidateCurrentLiveRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
set_option autoImplicit false

theorem live (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len) :
    ∀ id allocation, Present (ActualWorld before) id allocation →
      DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder allocation.extra ∧
      allocation.extra.nodes.size+1 ≤ 4294967295 ∧
      allocation.extra.nodes.size < 65536 ∧ allocation.len < 2^64 ∧
      allocation.extra.locations.size.bytes.toNat = allocation.len := by
  intro id allocation present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨oldId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  have nodes := resources.nodeRoom (oldId,entry) member
  have storage := resources.storageRoom (oldId,entry) member
  refine ⟨⟨state.formed _ member,state.coherent _ member,state.possible _ member,
    resources.tagsBelow _ member⟩,state.parentTags _ member,by omega,by omega,by omega,?_⟩
  rw [state.treeLength _ member,state.byteLength _ member]

theorem tag_room (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len) :
    tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have room := resources.tagRoom
  change tracker.global.nextPointerTag.value.toNat < (18446744073709551615 : UInt64).toNat
  change tracker.global.nextPointerTag.value.toNat < 18446744073709551615
  omega

theorem fresh (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) id allocation)
    (index : UniIndex) (node : TreeNode) (nodeAt : allocation.extra.nodes.get index = some node) :
    node.tag ≠ tracker.global.nextPointerTag := by
  have runtime := (live options limits remaining before tracker len state resources id allocation present).1
  apply GeneralBorrowForestTagHighWater.different
  exact GeneralBorrowForestTagHighWater.mapped _ _ _ _ runtime.below index
    (runtime.formed.allocator.nodeTags index node nodeAt)

end DuplicatePrefix.CandidateCurrentLiveRuntime

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentLiveRuntime." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current live runtime dependency {dependency}"
