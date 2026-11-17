import duplicate_prefix.S04ZeroChildPositive
import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration

namespace DuplicatePrefix.S04ZeroFnEntryObserver
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- Real tag allocation, Strong registration and the first zero-length
protected Default newChild preserve an independent positive observer window.
The actual sparse allocator Input is derived from runtime accounting and vacant
Clean. The empty reference's parent can be the observer or lie in any other
component of the SAME tree; no separation or operation-success field is added.
The zero typed retag has an empty inside map, so it performs no range Read. -/
theorem register_construct (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (short : tree.nodes.size < 65536)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime source selected maximum ownerOffset ownerLen positive
  let registration := registered global frame allocation tagRoom
  have accounting := registeredRuntime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let depth := Classical.choice registeredRuntime.formed.depth
  let input := ConcreteEmptyPoolEntry.factory tree parentTag global.nextPointerTag parent parentNode depth tagged present fresh
    registeredRuntime.formed.allocator.pool registeredRuntime.formed.allocator.accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean registeredRuntime)
  obtain ⟨done,kept⟩ := S04ZeroChildPositive.construct tree registration.1 registeredRuntime parentTag global.nextPointerTag input
    registeredRuntime.formed.fits offset source selected maximum ownerOffset ownerLen registeredPositive
  exact ⟨allocated,held,frameEq,done,kept⟩

end DuplicatePrefix.S04ZeroFnEntryObserver
