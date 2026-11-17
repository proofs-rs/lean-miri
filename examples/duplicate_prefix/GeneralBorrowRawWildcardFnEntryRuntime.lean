import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeRuntime
import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime
import duplicate_prefix.GeneralBorrowForestFnEntry
namespace DuplicatePrefix.GeneralBorrowRawWildcardFnEntryRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Literal allocation, Strong registration, wildcard Read and protected root
construction, with each real failure retained. -/
def operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (offset len : UInt64) : Except GlobalStateError GeneralBorrowForestFnEntry.Output := do
  let (advanced,tag) ← global.newPointerTag
  let (registered,callFrame) := advanced.addProtector frame allocation tag .StrongProtector
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  let child := accessed.tree.newChild (Size.ofBytes offset) .wildcard tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  pure ⟨registered,callFrame,tag,accessed,child⟩

/-- Actual wildcard FnEntry runtime initialization from raw current Positive
and coherent runtime. Allocator reuse and arbitrary other-root shapes remain
available. This stage does not yet claim the new child's full Positive. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615) :
    ∃ output, operation tree global frame allocation offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧
      output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots.push child ∧
        (∃ node,output.child.tree.nodeAt child = some node ∧ node.tag = output.tag ∧ node.parent = none ∧ node.isExposed = false) ∧
        GeneralRangeMapOrigins.OwnedOn (fun location => location.perms.get child = some GeneralBorrowFreshChild.inside)
          offset (offset+len) output.child.tree.locations := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime none none none offset len positive
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read
    registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access tree registration.1 registeredRuntime
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed offset len registeredPositive distinct short
    (Nat.le_refl _) (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact nodeRoom
  have bound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have nonzero : len ≠ 0 := by intro zero;have p := positive.positive;rw [zero] at p;contradiction
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by
    rw [contract.capacity];exact positive.bounds
  obtain ⟨childDone,childRuntime,capacity,growth,child,lookup,roots,geometry,stored⟩ :=
    GeneralBorrowWildcardConstructorRuntime.protected_mutable accessed.tree registration.1 afterRuntime
      global.nextPointerTag freshAfter room bound heldTag offset len nonzero bounds
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  refine ⟨output,?_,rfl,rfl,frameEq,contract.completed,childDone,childRuntime,capacity.trans contract.capacity,?_,child,lookup,?_,geometry,stored⟩
  · simp only [operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth
  · rw [contract.roots] at roots
    exact roots
end DuplicatePrefix.GeneralBorrowRawWildcardFnEntryRuntime
