import duplicate_prefix.S02DisjointMutableConstructor
import duplicate_prefix.GeneralBorrowStructuralHistoryMutable

namespace DuplicatePrefix.S02DisjointMutableRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Runtime coherence supplies allocator geometry, cleanliness and scalar
profiles. No constructor-success or post-constructor capability is assumed. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (old : Positive tree global.protectedTags source selected maximum lower width) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    result.outcome = .ok () ∧ Nonempty (Positive result.tree global.protectedTags source selected maximum lower width) := by
  let depth := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  exact S02DisjointMutableConstructor.construct tree runtime.formed.toState.toGraphState depth parentTag newTag parent parentNode
    tagged present fresh slot offset len nonzero runtime.formed.well bounds (DuplicatePrefixBorrowContract.vacant_clean runtime)
    global.protectedTags source selected maximum lower width outside runtime.formed.profile old

end DuplicatePrefix.S02DisjointMutableRuntime

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointMutableRuntime.construct) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
