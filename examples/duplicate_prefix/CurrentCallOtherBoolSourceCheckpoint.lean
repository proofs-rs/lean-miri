import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallAllocationLicense

/-! An actual latent Bool conversion may advance the counter and root cache.
On a different allocation, transport the unchanged source and its entire fixed
cell bank using selected cache and metadata facts only. -/
namespace DuplicatePrefix.CurrentCallOtherBoolSourceCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem runtime_move {tree : BorrowTree} {old next : GlobalState}
    (facts : DuplicatePrefixBorrowContract.RuntimeFacts tree old)
    (flags : next.protectedTags = old.protectedTags)
    (counter : old.nextPointerTag.value.toNat ≤ next.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree next := by
  refine ⟨?_, ?_, facts.possible, ?_, ?_⟩
  · simpa only [flags] using facts.formed
  · simpa only [flags] using facts.coherent
  · intro row member
    have := facts.below.mapping row member
    omega
  · intro row member
    rw [flags] at member
    have := facts.below.protectors row member
    omega

/-- All arguments after the current source are selected facts derived from
the actual Bool phase. No conversion result, global-state equality, or source
authority under the Bool's completion is required. -/
theorem at_post {before tracker offset len}
    (source : Source before tracker offset len) (ready : CopyReady source)
    (frame : FrameState) (boolId : AllocId)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (post : Before) (next : MachineHooks.BorrowState)
    (present : Present (ActualWorld post) source.role.backing.id source.role.backing.allocation)
    (binding : CandidateCallBindings.WindowBinding post source.role.family.value source.role.backing.id offset len.toNat)
    (rootTag : next.global.rootTag? source.role.backing.id = tracker.global.rootTag? source.role.backing.id)
    (flags : next.global.protectedTags = (GeneralBorrowFnEntryRegistration.registered tracker.global frame boolId room).1.protectedTags)
    (counter : (GeneralBorrowFnEntryRegistration.registered tracker.global frame boolId room).1.nextPointerTag.value.toNat ≤
      next.global.nextPointerTag.value.toNat)
    (extras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == source.role.backing.id) =
      before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == source.role.backing.id)) :
    ∃ current : Source post next offset len,
      CopyReady current ∧ current.role.family = source.role.family ∧
      current.role.backing.id = source.role.backing.id ∧
      current.role.backing.allocation = source.role.backing.allocation ∧
      HEq current.role.backing.cells source.role.backing.cells ∧
      current.tag = source.tag ∧ current.grant = source.grant ∧ current.node = source.node ∧
      (∀ (i : Fin current.role.backing.cells.size) overlap,
        ∃ old : Fin source.role.backing.cells.size, old.val = i.val ∧
        ∃ oldOverlap, (current.role.roles i overlap).grant = (source.role.roles old oldOverlap).grant) := by
  let back : AllocationCover post := {
    id := source.role.backing.id, allocation := source.role.backing.allocation,
    live := present, cells := source.role.backing.cells, disjoint := source.role.backing.disjoint }
  let ctx : Context post := { allocations := #[back], unique := by simp }
  have sourceFlags : ∀ index node, source.role.backing.allocation.extra.nodes.get index = some node →
      next.global.protectedTags.contains node.tag = tracker.global.protectedTags.contains node.tag := by
    intro index node found
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh source.role.backing.allocation.extra
      tracker.global source.runtime index node found
    have different : node.tag ≠ tracker.global.nextPointerTag := by
      intro equal
      rw [equal] at older
      exact UInt64.lt_irrefl _ older
    rw [flags]
    exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector different
  let role : RoleCover post next ctx .mut offset len.toNat := {
    family := source.role.family, backing := back, backingAt := by simp [ctx], id := source.role.id,
    covered := source.role.covered,
    roles := by
      intro i overlap
      let old := source.role.roles i overlap
      have issued := CurrentCallAllocationLicense.spatial old.issued post next source.role.backing.allocation
        present rootTag rfl rfl rfl (fun _ _ hit => hit)
        (fun _ node hit => ⟨node, hit, rfl, rfl, rfl, rfl⟩)
        source.role.backing.cells[i].completion (fun _ _ edge => edge)
      refine ⟨old.grant, old.binding, issued, ?_⟩
      intro byte request cell
      obtain ⟨bound, authority⟩ := old.available byte request cell
      refine ⟨bound, ?_⟩
      intro segment member lower upper index node found
      rw [sourceFlags index node found]
      exact authority segment member lower upper index node found }
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare source.role.backing.allocation.extra
    tracker.global frame boolId room source.runtime).2.2.2.1
  have runtime := runtime_move registeredRuntime flags counter
  let current : Source post next offset len := {
    context := ctx, role := role, runtime := runtime, distinct := source.distinct,
    tag := source.tag, concrete := source.concrete, grant := source.grant, node := source.node,
    nodeAt := source.nodeAt, nodeTag := source.nodeTag, hidden := source.hidden, activity := source.activity,
    binding := binding, positive := source.positive, signedFits := source.signedFits, nodes := source.nodes }
  refine ⟨current, ⟨ready.storage, ?_⟩, rfl, rfl, rfl, HEq.rfl, rfl, rfl, rfl, ?_⟩
  · obtain ⟨sync, selected, outside⟩ := ready.profile
    exact ⟨sync, extras.trans selected, outside⟩
  · intro i overlap
    exact ⟨i, rfl, overlap, rfl⟩

end
end DuplicatePrefix.CurrentCallOtherBoolSourceCheckpoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOtherBoolSourceCheckpoint.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved other-Bool source dependency {name}: {dependency}"
