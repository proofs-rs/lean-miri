import duplicate_prefix.Bounds
import Miri.Interpreter.PointerOffset

/-! Source-backed pointer access lemmas. Resolver/lookup equalities describe
the provenance and live allocation being accessed; the range and signed-size
checks are derived, rather than assumed successful. These are component
contracts, not a claim about execution of the imported MIR. -/

set_option maxRecDepth 4096

namespace DuplicatePrefix.PointerAccess
open Miri.ABI Miri.Memory Miri.Interpreter

theorem dereference_ok {Prov Extra : Type}
    (target : PointerArithmetic) (pointer : Pointer (Option Prov))
    (count : Nat) (message : CheckInAllocMsg)
    (resolve : PointerResolver Prov Extra) (lookup : LiveAllocationLookup)
    (resolved : ResolvedPointer Extra) (info : AllocationInfo)
    (positive : 0 < count) (signedFits : count < 9223372036854775808)
    (resolution : resolve pointer (Int.ofNat count) = .ok resolved)
    (allocation : lookup resolved.allocId = .ok info)
    (live : info.kind ≠ .dead)
    (bounds : resolved.offset.bytes.toNat + count ≤ info.size.bytes.toNat) :
    checkAndDerefPtr target pointer (Int.ofNat count) message resolve lookup =
      .ok (some ⟨resolved, info⟩) := by
  have boundCheck := DuplicatePrefix.checkedBounds_ok target resolved.allocId info.size
    resolved.offset count message signedFits bounds
  simp [checkAndDerefPtr, Nat.ne_of_gt positive]
  split
  · rename_i invalid
    change (decide (-(2 ^ 63 : Int) ≤ (count : Int)) &&
      decide ((count : Int) < (2 ^ 63 : Int))) = false at invalid
    simp at invalid
    omega
  · change resolve pointer (count : Int) = .ok resolved at resolution
    rw [resolution]
    simp [allocation, live]
    change checkedBounds target resolved.allocId info.size resolved.offset (count : Int) message = .ok () at boundCheck
    rw [boundCheck]
    rfl

end DuplicatePrefix.PointerAccess
