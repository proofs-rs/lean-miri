import duplicate_prefix.WildcardImmediateGapAddress
import duplicate_prefix.WildcardEmptyCallTimeCases
import duplicate_prefix.UnknownConcreteEmptyRetag
namespace DuplicatePrefix.WildcardImmediateGapCoverage
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Memory.AllocAddresses
open WildcardImmediateGapAddress
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Recover raw source-precedence metadata constructors from the initial
lookup data produced by the existing exhaustive case classification. This
helper's equation is NOT a final call-safety premise. -/
theorem data_of_lookup {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (info : AllocationInfo) (known : memory.getAllocInfo id = .ok info) :
    SizeData memory id info.size := by
  have transport {size : Size} (data : SizeData memory id size) : SizeData memory id info.size := by
    have same := size_of_data memory id size data
    simp only [known,Except.toOption,Option.map_some] at same
    rw [Option.some.inj same]
    exact data
  cases live : memory.live.find? (fun row => row.1 == id) with
  | some row =>
    have key : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some live
    rcases row with ⟨keyId,entry⟩
    dsimp only at key
    subst keyId
    exact transport (.live entry live)
  | none =>
    cases function : memory.hasFunctionPointer id with
    | true => exact transport (.functionRow live function)
    | false =>
      cases vaList : memory.hasVaListId id with
      | true => exact transport (.vaListRow live function vaList)
      | false =>
        cases global : memory.findGlobal? id with
        | some descriptor => exact transport (.globalRow descriptor live function vaList global)
        | none =>
          cases dead : memory.dead.find? (fun row => row.allocId == id) with
          | some entry => exact transport (.dead entry live function vaList global dead)
          | none =>
            have missing := UnknownConcreteEmptyRetag.missing_info memory id live function vaList global dead
            rw [missing] at known
            cases known

/-- Every immediate-gap case obtained from the existing S01 candidate supplies
raw metadata for the new actual all-count call theorem. No additional family
membership/metadata-success assumption is imposed on Candidate. -/
theorem of_classified {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (gap : WildcardEmptyCallTimeCases.ImmediateGap memory addresses address) :
    RawGeometry memory addresses address := by
  obtain ⟨position,row,info,partition,present,known,outside⟩ := gap
  exact ⟨position,row,info.size,partition,present,data_of_lookup memory row.allocId info known,outside⟩
end DuplicatePrefix.WildcardImmediateGapCoverage
