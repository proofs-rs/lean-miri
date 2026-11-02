import duplicate_prefix.GeneralBorrowRawWildcardFnEntryResources
import duplicate_prefix.GeneralBorrowWildcardChildCausalOrder

namespace DuplicatePrefix.S02WildcardSourceOrder
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration GeneralBorrowRawWildcardFnEntryRuntime
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The actual wildcard FnEntry read plus parentless fresh-root construction
preserves parent-tag order; no constructor outcome is a premise. -/
theorem ordered (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (output : GeneralBorrowForestFnEntry.Output)
    (run : operation tree global frame allocation offset len = .ok output) :
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder output.child.tree := by
  obtain ⟨allocated,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime
      none none none offset len positive
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access tree
    registration.1 registeredRuntime (Size.ofBytes offset) (Size.ofBytes len) .Read
    .VisitChildrenOfAccessed offset len registeredPositive distinct short
    (Nat.le_refl _) (Nat.le_refl _)
  have accessedOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder accessed.tree := by
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [contract.nodes]
    exact order
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by
    rw [contract.nodes]
    exact nodeRoom
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by
    rw [contract.tags]
    exact fresh
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ :=
    GeneralBorrowWildcardConstructorSlot.select accessed.tree registration.1 afterRuntime
      global.nextPointerTag freshAfter room (.ReservedFrz false) .None
  have constructorOrder := GeneralBorrowWildcardChildCausalOrder.inserted_order accessed.tree
    (GeneralBorrowStructuralHistoryShared.depth accessed.tree afterRuntime.formed.toState)
    accessedOrder global.nextPointerTag mapping index inserted vacant (Size.ofBytes offset)
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true
  have outputEq : output = ⟨registration.1,registration.2,global.nextPointerTag,accessed,
      accessed.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
        (.ReservedFrz false) true⟩ := by
    unfold operation at run
    rw [allocated] at run
    simp only [Except.bind,Except.pure,bind,pure] at run
    exact (Except.ok.inj run).symm
  rw [outputEq]
  exact constructorOrder

end DuplicatePrefix.S02WildcardSourceOrder

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceOrder.ordered) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard source-order dependency {dependency}"
