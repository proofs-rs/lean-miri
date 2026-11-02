import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.StackPopRelease
import duplicate_prefix.S04ReturnReleaseParent
namespace DuplicatePrefix.S05CompletedChildReanchor
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem below_child {completion : Completion} {child parent index : UniIndex}
    (edge : completion.parents[child.toNat]? = some (some parent)) :
    Below completion index child ↔ index = child ∨ Below completion index parent := by
  constructor
  · intro below
    cases below with
    | refl => exact .inl rfl
    | @step predecessor _ found prior =>
      have same : predecessor = parent := Option.some.inj (Option.some.inj (found.symm.trans edge))
      subst predecessor
      exact .inr prior
  · rintro (same | prior)
    · subst index;exact .refl child
    · exact .step edge prior

/-- Reanchor at the actual completion parent after its child protector is
removed. The parent may be a virtual origin of a physical wildcard root. -/
theorem authority (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (before after : ProtectedTags) (child parent : UniIndex) (childNode : TreeNode)
    (edge : completion.parents[child.toNat]? = some (some parent))
    (childAt : tree.nodes.get child = some childNode)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (removed : after.contains childNode.tag = false)
    (owned : Authority tree completion before child location) : Authority tree completion after parent location := by
  intro index node present
  have initial := owned index node present
  constructor
  · intro below
    have prior := initial.1 (.step edge below)
    exact ⟨prior.1,prior.2.1,prior.2.2.1,fun held => prior.2.2.2 (weaken node.tag held)⟩
  · intro outside
    by_cases same : index = child
    · subst index
      have nodeEq : node = childNode := Option.some.inj (present.symm.trans childAt)
      subst node
      exact ⟨(initial.1 (.refl child)).1,by intro h;rw [removed] at h;cases h⟩
    · have prior := initial.2 (fun below => outside (((below_child edge).mp below).resolve_left same))
      exact ⟨prior.1,fun held => prior.2 (weaken node.tag held)⟩

theorem end_call (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (global : GlobalState) (frame : FrameState) (allocation : AllocId) (child parent : UniIndex) (childNode : TreeNode)
    (edge : completion.parents[child.toNat]? = some (some parent))
    (childAt : tree.nodes.get child = some childNode)
    (member : (allocation,childNode.tag) ∈ frame.protectedTags.toList)
    (owned : Authority tree completion global.protectedTags child location) :
    Authority tree completion (global.endCall frame).protectedTags parent location := by
  apply authority tree completion location global.protectedTags (global.endCall frame).protectedTags child parent childNode
    edge childAt (GeneralBorrowRelease.end_call_weakens global frame) _ owned
  rw [StackPopRelease.end_call_contains]
  have tagMember : childNode.tag ∈ frame.protectedTags.toList.map Prod.snd := List.mem_map.mpr ⟨(allocation,childNode.tag),member,rfl⟩
  simp only [tagMember,ite_true]

theorem owned_end_call (tree : BorrowTree) (completion : Completion) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (child parent : UniIndex) (childNode : TreeNode) (lower upper : UInt64)
    (edge : completion.parents[child.toNat]? = some (some parent))
    (childAt : tree.nodes.get child = some childNode)
    (member : (allocation,childNode.tag) ∈ frame.protectedTags.toList)
    (owned : OwnedOn (Authority tree completion global.protectedTags child) lower upper tree.locations) :
    OwnedOn (Authority tree completion (global.endCall frame).protectedTags parent) lower upper tree.locations := by
  intro position valid positive start stop
  exact end_call tree completion _ global frame allocation child parent childNode edge childAt member
    (owned position valid positive start stop)
private theorem fold_member (rows : List (AllocId × BorTag)) (tags : ProtectedTags)
    (entry : BorTag × ProtectorKind)
    (member : entry ∈ (rows.foldl (fun table row => table.remove row.2) tags).entries) : entry ∈ tags.entries := by
  induction rows generalizing tags with
  | nil => exact member
  | cons row rest ih =>
    exact (Array.mem_filter.mp (ih (tags.remove row.2) member)).1

/-- The actual whole-frame bookkeeping preserves runtime after its real
release Plan has completed; no legacy permission packet is needed. -/
theorem runtime_end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (hidden : S04ReturnReleaseParent.HiddenFrame tree frame) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall frame) := by
  have weaken := GeneralBorrowRelease.end_call_weakens global frame
  have same := S04ReturnReleaseParent.exposed_frame tree global frame hidden
  refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
  · intro position valid
    exact GeneralBorrowHiddenProtectorDropRuntime.profile tree _ _ _ weaken (runtime.formed.profile position valid)
  · intro position valid
    exact GeneralBorrowProtectorCacheMap.frame tree _ _ _ (runtime.coherent position valid) same
  · refine ⟨runtime.below.mapping,?_⟩
    intro row member
    apply runtime.below.protectors row
    apply fold_member frame.protectedTags.toList global.protectedTags row
    simpa only [GlobalState.endCall,Array.foldl_toList] using member

end DuplicatePrefix.S05CompletedChildReanchor
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedChildReanchor." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved completed child reanchor dependency {dependency}"
