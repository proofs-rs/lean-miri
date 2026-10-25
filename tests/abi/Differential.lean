import Miri.ABI

open Miri.ABI

private def u128 (value : Nat) : U128 := BitVec.ofNat 128 value

private def checkedValue (result : Except SizeError UInt64) : String :=
  match result with
  | .ok value => toString value
  | .error _ => "error"

private def alignValue (result : Except AlignError UInt64) : String :=
  match result with
  | .ok value => toString value
  | .error _ => "error"

private def sizeOption (result : Option Size) : String :=
  match result with
  | some value => toString value.bytes
  | none => "none"

private def u128Result (result : Except SizeError U128) : String :=
  match result with
  | .ok value => toString value.toNat
  | .error _ => "error"

private def intResult (result : Except SizeError Int) : String :=
  match result with
  | .ok value => toString value
  | .error _ => "error"

private def lines : List String := Id.run do
  let layout16 : TargetDataLayout := ⟨.little, .w16⟩
  let align8 := Align.EIGHT
  let range := WrappingRange.mk (u128 254) (u128 2)
  let full := WrappingRange.mk (u128 128) (u128 127)
  let wrap ← match WrappingRange.smallestRangeContaining [u128 1, u128 254] (Size.ofBytes 1) with
    | .ok (some value) => pure value
    | _ => pure (WrappingRange.mk 0 0)
  let rangeUnsignedWrap :=
    match range.noUnsignedWraparound (Size.ofBytes 1) with
    | .ok .nonWrapping => "true"
    | .ok .wrapping => "false"
    | _ => "error"
  let rangeSignedWrap :=
    match range.noSignedWraparound (Size.ofBytes 1) with
    | .ok .nonWrapping => "true"
    | .ok .wrapping => "false"
    | _ => "error"
  let rangeFull :=
    match WrappingRange.isFullFor full (Size.ofBytes 1) with
    | .ok value => toString value
    | .error _ => "error"
  let smallestText := toString wrap.start.toNat ++ ":" ++ toString wrap.«end».toNat
  return [
    s!"from_bits_9={(Size.fromBits 9).bytes}",
    s!"bits_boundary={checkedValue (Size.bits (Size.ofBytes 2305843009213693951))}",
    s!"bits_overflow={Size.bits (Size.ofBytes 2305843009213693952) != .ok 0}",
    s!"unsigned_max_zero={Size.unsignedIntMax (Size.ofBytes 0) == .error .zeroWidthUnsignedBound}",
    s!"add_overflow={Size.add (Size.ofBytes 18446744073709551615) (Size.ofBytes 1) == .error (.u64Overflow "add" 18446744073709551615 1)}",
    s!"sub_overflow={Size.sub (Size.ofBytes 0) (Size.ofBytes 1) == .error (.negativeSubtraction 0 1)}",
    s!"mul_overflow={Size.mul (Size.ofBytes 18446744073709551615) 2 == .error (.u64Overflow "mul" 18446744073709551615 2)}",
    s!"truncate8={u128Result (Size.truncate (Size.ofBytes 1) (u128 511))}",
    s!"sign8={intResult (Size.signExtend (Size.ofBytes 1) (u128 255))}",
    s!"sign128={intResult (Size.signExtend (Size.ofBytes 16) (u128 (2^127)))}",
    s!"obj16_below={sizeOption (Size.checkedAdd (Size.ofBytes 32767) (Size.ofBytes 0) layout16)}",
    s!"obj16_at={Size.checkedAdd (Size.ofBytes 32767) (Size.ofBytes 1) layout16 == none}",
    s!"mul16_below={sizeOption (Size.checkedMul (Size.ofBytes 32767) 1 layout16)}",
    s!"mul16_at={Size.checkedMul (Size.ofBytes 16384) 2 layout16 == none}",
    s!"align_ceil={alignValue ((Align.fromBits 9).bind Align.bytes)}",
    s!"align_max={alignValue ((Align.fromBytes 536870912).bind Align.bytes)}",
    s!"align_too_large={match Align.fromBytes 1073741824 with | .error (.tooLarge _) => true | _ => false}",
    s!"align_overflow={match Size.alignTo (Size.ofBytes 18446744073709551615) align8 with | .error _ => true | _ => false}",
    s!"zero_factor_restrict={alignValue ((Align.restrictForOffset Align.EIGHT (Size.ofBytes 0)).bytes)}",
    s!"zero_factor_bytes_overflow={match (Align.maxAlignedFactor (Size.ofBytes 0)).bytes with | .error (.shiftOverflow 64) => true | _ => false}",
    s!"range_contains={range.contains (u128 1)}",
    s!"range_full={rangeFull}",
    s!"range_unsigned_wrap={rangeUnsignedWrap}",
    s!"range_signed_wrap={rangeSignedWrap}",
    s!"smallest={smallestText}"
  ]

def main : IO Unit := do
  for line in lines do
    IO.println line
