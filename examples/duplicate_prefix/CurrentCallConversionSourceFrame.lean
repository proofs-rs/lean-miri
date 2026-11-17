import duplicate_prefix.CurrentCallLazySourceResources
import duplicate_prefix.CurrentCallAllocationLicense

/-! The actual converter can allocate relocation roots after the source tag
has been saved. Transport the unchanged constructor resources to its actual
global state; neither the selected tag nor its counter is reallocated here. -/
namespace DuplicatePrefix.CurrentCallConversionSourceFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallLazySourceResources
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem runtime {tree : BorrowTree} {old next : GlobalState}
    (facts : DuplicatePrefixBorrowContract.RuntimeFacts tree old)
    (flags : next.protectedTags = old.protectedTags)
    (counter : old.nextPointerTag.value.toNat ≤ next.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree next := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [flags] using facts.formed
  · simpa only [flags] using facts.coherent
  · exact facts.possible
  · intro row member
    have := facts.below.mapping row member
    omega
  · intro row member
    rw [flags] at member
    have := facts.below.protectors row member
    omega

/-- The source window and runtime refer to the ACTUAL post-conversion tracker.
Only selected-cache preservation, unchanged registered flags and counter growth
are used; the saved source tag need not equal the final counter minus one. -/
theorem at_post (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (attributes : GlobalAllocationAttributes.Attributes source converted)
    (storage : source.len = source.byteSize.bytes.toNat) (rootCached : global.rootTag? id = some root)
    (offset len : UInt64) (room : global.nextPointerTag.value < 18446744073709551615)
    (stage : Stage global frame id root source.byteSize.bytes offset len room)
    (bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat)
    (base : UInt64) (post : Before) (next : MachineHooks.BorrowState)
    (actualRoot : next.global.rootTag? id = some root)
    (flags : next.global.protectedTags = stage.output.global.protectedTags)
    (counter : stage.output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat)
    (present : Present (ActualWorld post) id (converted.mapExtra (fun _ => stage.output.child.tree)))
    (data : Identities) :
    ∃ nextData nextOwner,
    ∃ current : UniformWindow post next nextData nextOwner id offset.toNat len.toNat .mut,
      current.pointer = ⟨id, Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset)), stage.child⟩ ∧
      current.allocation = converted.mapExtra (fun _ => stage.output.child.tree) ∧
      current.precise.completion = S05ConcreteProtectedChildCompletion.extend stage.initialCompletion stage.child allocationRoot ∧
      DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra next.global := by
  let shadow : MachineHooks.BorrowState := {next with global := stage.output.global}
  obtain ⟨nextData, nextOwner, current, pointer, allocation, completion⟩ :=
    CurrentCallLazySourceResources.at_post global frame id root source converted attributes storage rootCached
      offset len room stage bounds base post shadow rfl present data
  have selectedCache : next.global.rootTag? id = shadow.global.rootTag? id := by
    change next.global.rootTag? id = stage.output.global.rootTag? id
    rw [actualRoot, stage.globalEq]
    exact rootCached.symm
  have issued := CurrentCallAllocationLicense.spatial current.issued post next current.allocation current.present selectedCache
    rfl rfl rfl (fun _ _ hit => hit) (fun _ node hit => ⟨node, hit, rfl, rfl, rfl, rfl⟩)
    current.precise.completion (fun _ _ edge => edge)
  let actual : UniformWindow post next nextData nextOwner id offset.toNat len.toNat .mut := {
    loan := current.loan, pointer := current.pointer, allocation := current.allocation, precise := current.precise,
    loanAt := current.loanAt, pointerAt := current.pointerAt, pointerId := current.pointerId,
    present := current.present, preciseAt := current.preciseAt, binding := current.binding,
    issued := issued, parents := current.parents,
    window := by intro byte inside; simpa only [shadow, flags] using current.window byte inside }
  refine ⟨nextData, nextOwner, actual, pointer, allocation, completion, ?_⟩
  change DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra next.global
  rw [allocation]
  exact runtime stage.runtime flags counter

end DuplicatePrefix.CurrentCallConversionSourceFrame
