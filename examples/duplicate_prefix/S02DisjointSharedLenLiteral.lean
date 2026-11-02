import duplicate_prefix.S02DisjointSharedHelper
import duplicate_prefix.S02DisjointSharedExpression
import duplicate_prefix.GeneralBorrowRawSharedNext
import duplicate_prefix.GeneralBorrowRawSharedToLenLiteralLedger
namespace DuplicatePrefix.S02DisjointSharedLenLiteral
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- An initial disjoint owner survives the actual shared expression, protected length helper, release and endCall. -/
theorem destination (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+2 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (positive : Positive tree tracker.global.protectedTags source selected maximum lower width) :
    Nonempty (Positive (GeneralBorrowRawSharedToLenLiteralLedger.finalTree tree tracker input.parentTag input.offset input.len input.tagRoom)
      tracker.global.protectedTags source selected maximum lower width) := by
  let expression := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
    input.offset input.len .VisitChildrenOfAccessed).tree
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  obtain ⟨exprRuntime,capacity,raw,tag,selectedEq,maximumEq,offsetEq,lenEq⟩ :=
    GeneralBorrowRawSharedNext.next_input tree tracker runtime input (by omega) nodeRoom tagRoom
  obtain ⟨_,_,_,exprPositive⟩ := S02DisjointSharedExpression.literal tree tracker.global runtime input source selected maximum lower width outside positive
  obtain ⟨_,_,_,growth,_,_,_⟩ := GeneralBorrowRawSharedResources.resources tree tracker.global runtime input
  have stepRoom : expression.nodes.size+1 < 65536 := by
    have bound : expression.nodes.size ≤ tree.nodes.size+1 := growth
    omega
  obtain ⟨finalPositive⟩ := S02DisjointSharedHelper.destination expression next allocation exprRuntime raw stepRoom source selected maximum lower width
    (by simpa only [offsetEq,lenEq] using outside) (Classical.choice exprPositive)
  rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq] at finalPositive
  simp only [tag,offsetEq,lenEq] at finalPositive
  exact ⟨finalPositive⟩
end DuplicatePrefix.S02DisjointSharedLenLiteral
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointSharedLenLiteral.destination) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
