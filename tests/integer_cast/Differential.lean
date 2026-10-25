import Miri.Interpreter.IntegerCast

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

def integerType (kind : IntegerKind) (bytes : Nat) : IntegerType :=
  { kind := kind, size := Size.ofBytes (UInt64.ofNat bytes) }

def castTargets : List (String × IntegerType) := [
  ("i8", integerType .i8 1), ("u8", integerType .u8 1),
  ("i16", integerType .i16 2), ("u16", integerType .u16 2),
  ("i32", integerType .i32 4), ("u32", integerType .u32 4),
  ("i64", integerType .i64 8), ("u64", integerType .u64 8),
  ("i128", integerType .i128 16), ("u128", integerType .u128 16),
  ("isize", integerType .isize 8), ("usize", integerType .usize 8)
]

structure CastSampleGroup where
  tag : String
  type : IntegerType
  values : List Int

def integerSamples : List CastSampleGroup := [
  ⟨"i8", integerType .i8 1, [-128, -1, 0, 127]⟩,
  ⟨"u8", integerType .u8 1, [0, 1, 127, 128, 255]⟩,
  ⟨"i16", integerType .i16 2, [-(2 ^ 15 : Int), -1, 0, (2 ^ 15 : Int) - 1]⟩,
  ⟨"u16", integerType .u16 2, [0, 1, 2 ^ 15, 2 ^ 16 - 1]⟩,
  ⟨"i32", integerType .i32 4, [-(2 ^ 31 : Int), -1, 0, (2 ^ 31 : Int) - 1]⟩,
  ⟨"u32", integerType .u32 4, [0, 1, 2 ^ 31, 2 ^ 32 - 1]⟩,
  ⟨"i64", integerType .i64 8, [-(2 ^ 63 : Int), -1, 0, (2 ^ 63 : Int) - 1]⟩,
  ⟨"u64", integerType .u64 8, [0, 1, 2 ^ 63, 2 ^ 64 - 1]⟩,
  ⟨"i128", integerType .i128 16,
    [-(2 ^ 127 : Int), -1, 0, (2 ^ 127 : Int) - 1]⟩,
  ⟨"u128", integerType .u128 16,
    [0, 1, 2 ^ 127, (2 ^ 128 : Int) - 1]⟩,
  ⟨"isize", integerType .isize 8,
    [-(2 ^ 63 : Int), -1, 0, (2 ^ 63 : Int) - 1]⟩,
  ⟨"usize", integerType .usize 8,
    [0, 1, 2 ^ 63, (2 ^ 64 : Int) - 1]⟩
]

def sourceScalar (type : IntegerType) (value : Int) : IO ScalarInt := do
  let result := if type.signed then
      ScalarInt.truncateFromInt value type.size
    else
      ScalarInt.truncateFromUInt (BitVec.ofNat 128 value.toNat) type.size
  match result with
  | .ok (scalar, _) => pure scalar
  | .error _ => throw (IO.Error.userError "failed to construct a checked source scalar")

def castResult (source : IntegerCastSource) (scalar : ScalarInt)
    (target : IntegerCastTarget) : IO String := do
  match IntegerCast.cast source scalar target with
  | .ok result => pure result.data.toNat.repr
  | .error _ => throw (IO.Error.userError "valid integer-like cast unexpectedly failed")

def emitCastRow (tag : String) (source : IntegerCastSource) (scalar : ScalarInt) : IO Unit := do
  let results ← castTargets.mapM fun (_, targetType) =>
    castResult source scalar (.integer targetType)
  IO.println s!"C|{tag}|{scalar.data.toNat}|{String.intercalate "|" results}"

def emitIntegerCasts : IO Unit := do
  for group in integerSamples do
    for value in group.values do
      let scalar ← sourceScalar group.type value
      emitCastRow group.tag (.integer group.type) scalar
      if group.tag == "u8" then
        match IntegerCast.cast (.integer group.type) scalar .character with
        | .ok result => IO.println s!"C|u8|{scalar.data.toNat}|char|{result.data.toNat}"
        | .error _ => throw (IO.Error.userError "u8-to-char cast unexpectedly failed")
  for value in [false, true] do
    emitCastRow "bool" .boolean (ScalarInt.ofBool value)
  for value in [Char.ofNat 0, 'A', Char.ofNat 0xe000, Char.ofNat 0x10ffff] do
    emitCastRow "char" .character (ScalarInt.ofChar value)

structure IntrinsicSampleGroup where
  tag : String
  type : IntegerType
  values : List Int

def intrinsicSamples : List IntrinsicSampleGroup := [
  ⟨"u8", integerType .u8 1, [0, 1, 0x80, 0xa5, 0xff]⟩,
  ⟨"u16", integerType .u16 2, [0, 1, 0x8000, 0xa55a, 0xffff]⟩,
  ⟨"u32", integerType .u32 4, [0, 1, 0x80000000, 0xa55aa55a, 0xffffffff]⟩,
  ⟨"u64", integerType .u64 8,
    [0, 1, 0x8000000000000000, 0xa55aa55aa55aa55a, 0xffffffffffffffff]⟩,
  ⟨"u128", integerType .u128 16,
    [0, 1, 2 ^ 127,
      0xa55aa55aa55aa55aa55aa55aa55aa55a,
      2 ^ 128 - 1]⟩,
  ⟨"i8", integerType .i8 1, [0, 1, -128, -91, -1, 127]⟩,
  ⟨"i128", integerType .i128 16,
    [0, 1, -(2 ^ 127 : Int), -1, (2 ^ 127 : Int) - 1]⟩
]

def intrinsicResult (intrinsic : IntegerIntrinsic) (scalar : ScalarInt)
    (input output : IntegerType) : IO String := do
  match IntegerIntrinsic.run intrinsic scalar input output with
  | .ok result =>
      if output.signed then
        match result.toInt output.size with
        | .ok signedValue => pure (BitVec.ofInt 128 signedValue).toNat.repr
        | .error _ => throw (IO.Error.userError "failed to decode signed intrinsic result")
      else
        pure result.data.toNat.repr
  | .error _ => throw (IO.Error.userError s!"valid intrinsic {repr intrinsic} unexpectedly failed")

def arithmeticValue (type : IntegerType) (value : Int) : IO IntegerValue := do
  return ⟨← sourceScalar type value, type⟩

def integerRaw (value : ScalarInt) : String := value.data.toNat.repr

def saturatingRow (tag : String) (type : IntegerType) (left right : Int) : IO Unit := do
  let l ← arithmeticValue type left
  let r ← arithmeticValue type right
  let add ← match IntegerArithmeticIntrinsic.saturatingArith .add l r with
    | .ok value => pure (integerRaw value)
    | .error error => throw (IO.Error.userError s!"saturating add failed: {repr error}")
  let sub ← match IntegerArithmeticIntrinsic.saturatingArith .sub l r with
    | .ok value => pure (integerRaw value)
    | .error error => throw (IO.Error.userError s!"saturating sub failed: {repr error}")
  IO.println s!"S|{tag}|{integerRaw l.scalar}|{integerRaw r.scalar}|{add}|{sub}"

def exactDivisionRow (tag : String) (type : IntegerType) (left right : Int) : IO Unit := do
  let l ← arithmeticValue type left
  let r ← arithmeticValue type right
  match IntegerArithmeticIntrinsic.exactDiv l r with
  | .ok result => IO.println s!"D|{tag}|{integerRaw l.scalar}|{integerRaw r.scalar}|{integerRaw result}"
  | .error error => throw (IO.Error.userError s!"valid exact_div failed: {repr error}")

def emitIntrinsicRow (group : IntrinsicSampleGroup) (value : Int) : IO Unit := do
  let scalar ← sourceScalar group.type value
  let raw := if group.type.signed then (BitVec.ofInt 128 value).toNat else value.toNat
  let countType := integerType .u32 4
  let mut results : List String := []
  results := results ++ [← intrinsicResult .ctpop scalar group.type countType]
  results := results ++ [← intrinsicResult .cttz scalar group.type countType]
  if value == 0 then
    results := results ++ ["-"]
  else
    results := results ++ [← intrinsicResult .cttzNonzero scalar group.type countType]
  results := results ++ [← intrinsicResult .ctlz scalar group.type countType]
  if value == 0 then
    results := results ++ ["-"]
  else
    results := results ++ [← intrinsicResult .ctlzNonzero scalar group.type countType]
  results := results ++ [← intrinsicResult .bswap scalar group.type group.type]
  results := results ++ [← intrinsicResult .bitreverse scalar group.type group.type]
  IO.println s!"N|{group.tag}|{raw}|{String.intercalate "|" results}"

def checkErrors : IO Unit := do
  let u8 := integerType .u8 1
  let u16 := integerType .u16 2
  let zero ← sourceScalar u8 0
  for intrinsic in [IntegerIntrinsic.cttzNonzero, .ctlzNonzero] do
    match IntegerIntrinsic.run intrinsic zero u8 (integerType .u32 4) with
    | .error (.undefinedBehaviorOnZero actual) =>
        if actual != intrinsic then throw (IO.Error.userError "nonzero intrinsic reported the wrong tag")
    | _ => throw (IO.Error.userError "zero input was accepted by a nonzero intrinsic")
  let badBool ← match ScalarInt.truncateFromUInt 2 (Size.ofBytes 1) with
    | .ok (scalar, _) => pure scalar
    | .error _ => throw (IO.Error.userError "failed to make invalid bool scalar")
  match IntegerCast.cast .boolean badBool (.integer u8) with
  | .error (.scalar (.invalidBool _)) => pure ()
  | _ => throw (IO.Error.userError "invalid bool cast was accepted")
  let badChar ← match ScalarInt.truncateFromUInt 0xd800 (Size.ofBytes 4) with
    | .ok (scalar, _) => pure scalar
    | .error _ => throw (IO.Error.userError "failed to make invalid char scalar")
  match IntegerCast.cast .character badChar (.integer u8) with
  | .error (.scalar (.invalidChar _)) => pure ()
  | _ => throw (IO.Error.userError "invalid char cast was accepted")
  let tooWide ← sourceScalar u16 256
  match IntegerCast.cast (.integer u16) tooWide .character with
  | .error (.integerToCharTryFromPanicked 256) => pure ()
  | _ => throw (IO.Error.userError "out-of-range int-to-char cast was accepted")
  let negativeI8 ← sourceScalar (integerType .i8 1) (-1)
  match IntegerCast.cast (.integer (integerType .i8 1)) negativeI8 .character with
  | .error (.integerToCharTryFromPanicked value) =>
      if value != 2 ^ 128 - 1 then
        throw (IO.Error.userError "signed int-to-char panic lost the source u128 intermediate")
  | _ => throw (IO.Error.userError "negative signed int-to-char did not preserve unwrap panic")
  match IntegerIntrinsic.run .bswap zero u8 u16 with
  | .error (.layoutMismatch _ _) => pure ()
  | _ => throw (IO.Error.userError "byte swap accepted unequal layouts")
  match IntegerIntrinsic.run .bitreverse zero u8 u16 with
  | .error (.layoutMismatch _ _) => pure ()
  | _ => throw (IO.Error.userError "bit reverse accepted unequal layouts")
  let i8 := integerType .i8 1
  let i8Min ← arithmeticValue i8 (-128)
  let minusOneI8 ← arithmeticValue i8 (-1)
  match IntegerArithmeticIntrinsic.exactDiv i8Min minusOneI8 with
  | .error (.integerOperation (.undefinedBehavior .remainderOverflow)) => pure ()
  | other => throw (IO.Error.userError s!"exact_div did not preserve MIN / -1 remainder UB: {repr other}")
  let i8Five ← arithmeticValue i8 5
  let i8Two ← arithmeticValue i8 2
  match IntegerArithmeticIntrinsic.exactDiv i8Five i8Two with
  | .error (.exactDivisionHasRemainder _) => pure ()
  | other => throw (IO.Error.userError s!"inexact division was accepted: {repr other}")
  let i8Zero ← arithmeticValue i8 0
  match IntegerArithmeticIntrinsic.exactDiv i8Five i8Zero with
  | .error (.integerOperation (.undefinedBehavior .remainderByZero)) => pure ()
  | other => throw (IO.Error.userError s!"exact_div did not preserve divide-by-zero UB: {repr other}")

def main : IO Unit := do
  checkErrors
  emitIntegerCasts
  saturatingRow "i8" (integerType .i8 1) 127 1
  saturatingRow "i8" (integerType .i8 1) (-128) (-1)
  saturatingRow "u8" (integerType .u8 1) 255 1
  saturatingRow "u8" (integerType .u8 1) 0 1
  saturatingRow "i128" (integerType .i128 16) (2 ^ 127 - 1) 1
  saturatingRow "i128" (integerType .i128 16) (-(2 ^ 127)) (-1)
  saturatingRow "u128" (integerType .u128 16) (2 ^ 128 - 1) 1
  saturatingRow "u128" (integerType .u128 16) 0 1
  exactDivisionRow "i8" (integerType .i8 1) (-6) 2
  exactDivisionRow "u8" (integerType .u8 1) 18 3
  exactDivisionRow "i128" (integerType .i128 16) (-(2 ^ 127)) 1
  exactDivisionRow "u128" (integerType .u128 16) (2 ^ 128 - 1) 3
  for group in intrinsicSamples do
    for value in group.values do
      emitIntrinsicRow group value
