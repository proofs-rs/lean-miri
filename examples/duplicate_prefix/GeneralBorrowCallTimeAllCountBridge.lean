import duplicate_prefix.GeneralBorrowCallTimeStorageBridge
import duplicate_prefix.GeneralBorrowRawRootAllCount
namespace DuplicatePrefix.GeneralBorrowCallTimeAllCountBridge
open Miri Miri.Input Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Matching the actual concrete argument and initial live/cache rows fixes the
candidate allocation/offset/tracker. These identities are derived from initial
data; no successful resolver or target operation is a premise. -/
theorem identities (s : GeneralBorrowRawRootAllCount.Initial)
    (input : DuplicatePrefixReferenceInput.Positive s.before
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len) :
    input.entry=s.entry ∧ input.offset=s.offset ∧ input.tracker=s.tracker := by
  have id : input.id=s.id := input.binding.1.symm
  have live : s.before.memory.live.find? (fun row => row.1 == s.id) = some (s.id,input.entry) := by
    simpa only [id] using input.live
  have entry : input.entry=s.entry := congrArg Prod.snd (Option.some.inj (live.symm.trans s.present))
  have cache : s.before.user.addresses.baseAddr.find? (fun row => row.allocId == s.id) = some ⟨s.id,input.base⟩ := by
    simpa only [id] using input.cachedBase
  have base : input.base=s.base := congrArg Miri.Memory.AllocAddresses.BaseAddressEntry.address
    (Option.some.inj (cache.symm.trans s.cachedAddress))
  have sum : s.base+s.offset=s.base+input.offset := by
    simpa only [Pointer.new,Size.ofBytes,base] using input.pointerAddress
  have sumNat := congrArg UInt64.toNat sum
  simp only [UInt64.toNat_add] at sumNat
  have offset : input.offset=s.offset := by
    apply UInt64.toNat_inj.mp
    have a := input.offset.toNat_lt
    have b := s.offset.toNat_lt
    omega
  have tracker : input.tracker=s.tracker := Option.some.inj (input.enabled.symm.trans s.enabled)
  exact ⟨entry,offset,tracker⟩

/-- An end-to-end implication from existing S01 reference/resource components
into the checked all-count call. Explicit bytes and +5 headroom premises are
DERIVED. Existing Initial/order/harness/configuration restrictions are retained.
The S01 components are not claimed necessary for every valid caller, and the
+16 candidate resource bound is not presented as weaker than the old +5 bound.
No ordinary-valid-input coverage or complete Target theorem is claimed. -/
theorem invoke (s : GeneralBorrowRawRootAllCount.Initial)
    (input : DuplicatePrefixReferenceInput.Positive s.before
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len)
    (resources : Resources s.options s.limits s.remaining s.before s.tracker s.len)
    (preciseOff : s.options.retag.preciseInteriorMut=false)
    (implicitOff : s.options.retag.implicitWrites=false)
    (budget : Nat) (dispatch : s.limits.callDispatch=budget+1)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation=s.validityFuel+1) (n : UInt64) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset)))) s.len n s.place := by
  obtain ⟨entry,offset,tracker⟩ := identities s input
  have data := GeneralBorrowCallTimeStorageBridge.bytes input resources.storageRoom
  have member : (input.id,input.entry) ∈ s.before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have nodes := resources.nodeRoom (input.id,input.entry) member
  dsimp only at nodes
  have tags := resources.tagRoom
  rw [entry] at nodes
  have nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536 := by omega
  have tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615 := by omega
  rw [entry,offset] at data
  exact GeneralBorrowRawRootAllCount.invoke s preciseOff implicitOff budget dispatch nodeMargin tagMargin data bufferExtras statementFuel n
end
end DuplicatePrefix.GeneralBorrowCallTimeAllCountBridge
