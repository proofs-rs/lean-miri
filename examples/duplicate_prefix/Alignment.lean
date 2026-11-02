import Miri.Memory.Access

/-! Component evidence for `duplicate_prefix`: the MIR uses `u8` elements,
whose required alignment is `Align.ONE`. This proves only the actual memory
alignment check, not safety of the enclosing function or all its accesses. -/

open Miri.ABI Miri.Memory

namespace DuplicatePrefix.Alignment

/-- Every pointer passes Miri's real alignment checker for an access requiring
one-byte alignment. Resolver, allocation lookup, and the machine alignment
hook remain arbitrary: `isPtrMisaligned` returns before consulting them when
required alignment is one byte. -/
theorem u8_checkPtrAlign_all_pointers {Prov ProvExtra : Type}
    [PointerProvenance Prov]
    (pointer : Pointer (Option Prov)) (enforceAlignment : Bool)
    (resolve : PointerResolver Prov ProvExtra)
    (lookup : LiveAllocationLookup)
    (machineAlignmentCheck : AllocId → Align → AllocationKind → Size → Align → Option Misalignment) :
    checkPtrAlign pointer Align.ONE enforceAlignment resolve lookup machineAlignmentCheck = .ok () := by
  unfold checkPtrAlign isPtrMisaligned
  cbv
  cases enforceAlignment <;> rfl

#print axioms u8_checkPtrAlign_all_pointers

end DuplicatePrefix.Alignment
