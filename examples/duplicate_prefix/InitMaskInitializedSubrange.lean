import duplicate_prefix.InitMaskCopy
namespace DuplicatePrefix.InitMaskInitializedSubrange
open Miri.ABI Miri.Memory

/-- Initialized raw bits remain initialized on a contained interval. Endpoints
are start/finish, not start/length; no memory-operation result is assumed. -/
theorem subrange (mask : InitMask) (outerStart outerFinish innerStart innerFinish : Size)
    (start : outerStart.bytes.toNat≤innerStart.bytes.toNat)
    (finish : innerFinish.bytes.toNat≤outerFinish.bytes.toNat)
    (initial : InitMaskCopy.InitializedOn mask outerStart outerFinish) :
    InitMaskCopy.InitializedOn mask innerStart innerFinish := by
  rcases mask with ⟨blocks,length⟩
  cases blocks with
  | Lazy state => exact initial
  | Materialized blocks =>
    intro block inBounds bit bitBound lower upper
    exact initial block inBounds bit bitBound (Nat.le_trans start lower) (Nat.lt_of_lt_of_le upper finish)
end DuplicatePrefix.InitMaskInitializedSubrange
