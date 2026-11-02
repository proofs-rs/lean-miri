import duplicate_prefix.S02DisjointFnEntryDestination
import duplicate_prefix.GeneralBorrowRawFnEntryArgument

namespace DuplicatePrefix.S02DisjointFnEntryTree
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The destination capability belongs to the literal tree installed by typed
argument passing, independently of the initial borrow tracker's retag mode. -/
theorem positive (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (destination : Positive tree
      (GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom).1.protectedTags
      source selected maximum lower width) :
    Nonempty (Positive (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len)
      (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).protectedTags source selected maximum lower width) := by
  obtain ⟨output,actual,globalEq,_read,_child,positive⟩ := S02DisjointFnEntryDestination.invoke tree tracker.global frame allocation
    runtime input source selected maximum lower width outside destination
  have allocated := (GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
    input.parent input.selected input.maximum input.offset input.len input.positive).1
  let registered := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registered.1.protectedTags .VisitChildrenOfAccessed
  have outputEq : output = ⟨registered.1,registered.2,tracker.global.nextPointerTag,read,
      read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩ := by
    unfold GeneralBorrowForestFnEntry.operation at actual
    rw [allocated] at actual
    simp only [Except.bind,Except.pure] at actual
    exact (Except.ok.inj actual).symm
  have treeEq : output.child.tree = GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len := by
    rw [outputEq]
    rfl
  have globalExact : output.global = TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom := by
    rw [globalEq]
    rfl
  rw [treeEq,globalExact] at positive
  exact positive

end DuplicatePrefix.S02DisjointFnEntryTree

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointFnEntryTree.positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
