import duplicate_prefix.CandidateCurrentGrantResources
import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.DuplicatePrefixRuntimeInput

/-! The grant denotation's two scalar realization requirements already follow
from existing runtime representation facts. They add no content-ownership
restriction. This supplies the actual-row field when building the unadopted
Joint candidate; active embedding and ordinary admission remain separate. -/
namespace DuplicatePrefix.CandidateCurrentGrantRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Possible excludes lazy Unique; scalar SIFA consistency separately excludes
protected ReservedIM. Neither conclusion comes from exclusive content rights. -/
theorem realized (state : LocationState) (held : Bool) (possible : state.possible = true)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held) : Realized state held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> simp [Realized,WellFormed,denote]
  | Unique => simpa [Realized,WellFormed,denote,LocationState.possible,Permission.isUnique] using possible
  | ReservedIM =>
    cases held
    · simp [Realized,WellFormed,denote]
    · obtain ⟨strongest,impossible,_⟩ := consistent
      simp [Permission.strongestIdempotentForeignAccess] at impossible
  | Cell | Frozen | Disabled => simp [Realized,WellFormed,denote]

/-- Every actual stored row receives its realization from current runtime
possible/profile data, including rows outside all active content windows. -/
theorem tree_rows (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (segment : Miri.DataStructures.RangeMapSegment LocationTree)
    (member : segment ∈ tree.locations.entries.toList)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    Realized (RawState segment.data index node) (global.protectedTags.contains node.tag) := by
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  exact realized _ _ (runtime.possible position valid index node present)
    ((runtime.formed.profile position valid).present index node present)

theorem actual (world : World) (global : GlobalState)
    (runtime : ∀ id allocation, Present world id allocation →
      DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra global) :
    ActualRealized world global.protectedTags := by
  intro id allocation present segment member index node nodeAt
  exact tree_rows allocation.extra global (runtime id allocation present) segment member index node nodeAt

/-- Direct Joint construction from its existing runtime representation input.
The initial active content embedding is still explicit; no scalar observation,
operation success, or extra Realized/ActualRealized ownership gate is supplied. -/
theorem joint (world : World) (global : GlobalState) (interpretation : Interpretation)
    (shape : PreciseShape world interpretation)
    (contents : CandidateFreezeContentResources.Valid interpretation.content)
    (runtime : ∀ id allocation, Present world id allocation →
      DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra global)
    (active : ∀ byte owner mode,
      interpretation.content byte owner = some ⟨mode,.active⟩ →
      ∃ loan pointer allocation precise,
        interpretation.loans[owner]? = some loan ∧
        interpretation.pointers[loan.pointer]? = some pointer ∧
        pointer.allocation = byte.1 ∧ Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
        (byte.1,precise) ∈ interpretation.precise.toList ∧
        Embeds allocation global.protectedTags precise.completion pointer.grant byte.2 (demandOf mode)) :
    Joint world global.protectedTags interpretation :=
  ⟨shape,contents,actual world global runtime,active⟩

/-- The existing whole-call RuntimeInput.State already supplies both scalar
representation invariants, without tag headroom or per-allocation high-water
resources. This is a consequence of that candidate, not its admission proof. -/
theorem actual_state (before : Before) (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (state : DuplicatePrefixRuntimeInput.State before tracker) :
    ActualRealized (ActualWorld before) tracker.global.protectedTags := by
  intro id allocation live segment member index node nodeAt
  simp only [Present,ActualWorld,Array.toList_map] at live
  obtain ⟨⟨oldId,entry⟩,present,equal⟩ := List.mem_map.mp live
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  exact realized _ _ (state.possible (oldId,entry) present position valid index node nodeAt)
    (((state.formed (oldId,entry) present).profile position valid).present index node nodeAt)

/-- Available contents embed in the actual current world using the existing
State representation input. The candidate's ActualRealized field is derived,
so it creates no extra ordinary-ownership restriction. -/
theorem joint_state (before : Before) (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (interpretation : Interpretation) (state : DuplicatePrefixRuntimeInput.State before tracker)
    (shape : PreciseShape (ActualWorld before) interpretation)
    (contents : CandidateFreezeContentResources.Valid interpretation.content)
    (active : ∀ byte owner mode,
      interpretation.content byte owner = some ⟨mode,.active⟩ →
      ∃ loan pointer allocation precise,
        interpretation.loans[owner]? = some loan ∧
        interpretation.pointers[loan.pointer]? = some pointer ∧
        pointer.allocation = byte.1 ∧ Present (ActualWorld before) byte.1 allocation ∧ byte.2 < allocation.len ∧
        (byte.1,precise) ∈ interpretation.precise.toList ∧
        Embeds allocation tracker.global.protectedTags precise.completion pointer.grant byte.2 (demandOf mode)) :
    Joint (ActualWorld before) tracker.global.protectedTags interpretation :=
  ⟨shape,contents,actual_state before tracker state,active⟩

end DuplicatePrefix.CandidateCurrentGrantRuntime

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentGrantRuntime." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved candidate grant runtime dependency {dependency}"
