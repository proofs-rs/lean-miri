import duplicate_prefix.GeneralBorrowWildcardConstructorSlot
import duplicate_prefix.GeneralBorrowWildcardConstructorExact
import duplicate_prefix.GeneralBorrowTagMap

namespace DuplicatePrefix.S02WildcardReturnConstructorOtherTag
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- A real wildcard root constructor leaves every different tag lookup alone,
for both append and coherent free-slot reuse. -/
theorem preserved (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag query : BorTag) (different : tag ≠ query)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
      (.ReservedFrz false) true).tree.indexOfTag query = tree.indexOfTag query := by
  obtain ⟨mapping,index,inserted,pushed,_vacant,_graph,_lower,_upper⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room
      (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState
    tag fresh room mapping index inserted (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have mapEq : mapping.get query = tree.tagMapping.get query := by
    cases mapping with
    | mk rows pool =>
      simp only [UniKeyMap.get] at *
      rw [pushed]
      exact GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag query different index pool
  rw [actual]
  change mapping.get query = tree.tagMapping.get query
  exact mapEq

end
end DuplicatePrefix.S02WildcardReturnConstructorOtherTag

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnConstructorOtherTag.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard constructor tag-frame dependency {dependency}"
