import duplicate_prefix.S04ZeroRootObserverPositive
import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration
import duplicate_prefix.S04ZeroWildcardRuntime

namespace DuplicatePrefix.S04ZeroWildcardFnEntryObserver
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Allocate the real fresh tag, register its Strong protector, and construct
an empty wildcard root while preserving the old positive observer window.
The sparse slot is derived from the initial runtime accounting and free pool;
no successful constructor or future permission profile is assumed. -/
theorem register_construct (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (short : tree.nodes.size < 65536)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime source selected maximum ownerOffset ownerLen positive
  have accounting := registeredRuntime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let slot := WildcardHitPoolRoot.factory tree registeredRuntime.formed.allocator.pool accounting fits
  obtain ⟨done,kept⟩ := S04ZeroRootObserverPositive.actual tree slot global.nextPointerTag fresh offset
    registeredRuntime.formed.toGraphState (DuplicatePrefixBorrowContract.vacant_clean registeredRuntime)
    (registered global frame allocation tagRoom).1.protectedTags source selected maximum ownerOffset ownerLen registeredPositive
  exact ⟨allocated,held,frameEq,done,kept⟩

/-- The observer and the complete runtime record hold on the SAME actual
constructor output. This is suitable for the next real retag in the empty call. -/
theorem complete (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (short : tree.nodes.size < 65536)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset : UInt64) (source selected : Option UniIndex) (maximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum ownerOffset ownerLen) :
    let registration := registered global frame allocation tagRoom
    let result := tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    global.newPointerTag = .ok (advanced global tagRoom,global.nextPointerTag) ∧
      registration.1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
      registration.2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
      result.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.tree registration.1.protectedTags source selected maximum ownerOffset ownerLen) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree registration.1 ∧
      result.tree.locations = tree.locations ∧ result.tree.nodes.size ≤ tree.nodes.size+1 := by
  obtain ⟨allocated,held,frameEq,done,kept⟩ := register_construct tree global frame allocation runtime
    short tagRoom offset source selected maximum ownerOffset ownerLen positive
  obtain ⟨_,_,_,registeredRuntime,_,fresh⟩ := GeneralBorrowWildcardFnEntryRegistration.prepare
    tree global frame allocation tagRoom runtime source selected maximum ownerOffset ownerLen positive
  have bound : global.nextPointerTag.value.toNat < (registered global frame allocation tagRoom).1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have isHeld : (registered global frame allocation tagRoom).1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨_,afterRuntime,locations,nodes⟩ := S04ZeroWildcardRuntime.construct tree _ registeredRuntime
    global.nextPointerTag fresh (by omega) bound isHeld offset
  exact ⟨allocated,held,frameEq,done,kept,afterRuntime,locations,nodes⟩

end DuplicatePrefix.S04ZeroWildcardFnEntryObserver
