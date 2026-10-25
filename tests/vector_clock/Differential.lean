import Miri.Concurrency.VectorClock

open Miri.Concurrency

private def timestamp (time : Nat) (readType : NaReadType) : VTimestamp :=
  match VTimestamp.encode time readType with
  | .ok value => value
  | .error _ => VTimestamp.ZERO

private def vectorIdx (value : Nat) : VectorIdx :=
  match VectorIdx.ofNat value with
  | .ok index => index
  | .error _ => VectorIdx.ofU32 0 (by decide)

private def fromTimes (times : List Nat) : VClock :=
  VClock.fromTimestamps (times.map fun time => timestamp time .Read)

private def timestampCode (value : VTimestamp) : String :=
  s!"{value.time}{if value.readType == .Retag then "t" else "r"}"

private def clockCode (clock : VClock) : String :=
  "[" ++ String.intercalate "," (clock.asList.map timestampCode) ++ "]"

private def readTypeCode : NaReadType → String
  | .Read => "read"
  | .Retag => "retag"

private def orderingCode : Option Ordering → String
  | none => "N"
  | some .lt => "L"
  | some .eq => "E"
  | some .gt => "G"

private def boolCode (value : Bool) : String := if value then "1" else "0"

private def emitComparison (label : String) (left right : VClock) : IO Unit := do
  IO.println s!"cmp:{label}:{orderingCode (VClock.partialCompare left right)}:{boolCode (VClock.lt left right)}:{boolCode (VClock.le left right)}:{boolCode (VClock.gt left right)}:{boolCode (VClock.ge left right)}:{boolCode (left == right)}"

private def smallClockInputs : Array VClock := Id.run do
  let allTimestamps := [
    timestamp 0 .Read, timestamp 0 .Retag,
    timestamp 1 .Read, timestamp 1 .Retag,
    timestamp 2 .Read, timestamp 2 .Retag]
  let nonzeroTimestamps := [
    timestamp 1 .Read, timestamp 1 .Retag,
    timestamp 2 .Read, timestamp 2 .Retag]
  let mut clocks := #[VClock.default]
  for tail in nonzeroTimestamps do
    clocks := clocks.push (VClock.fromTimestamps [tail])
  for head in allTimestamps do
    for tail in nonzeroTimestamps do
      clocks := clocks.push (VClock.fromTimestamps [head, tail])
  return clocks

def main : IO Unit := do
  let maxRead := timestamp 2147483647 .Read
  let maxRetag := timestamp 2147483647 .Retag
  IO.println s!"timestamp:max-read:{maxRead.packedValue}:{maxRead.time}:{readTypeCode maxRead.readType}"
  IO.println s!"timestamp:max-retag:{maxRetag.packedValue}:{maxRetag.time}:{readTypeCode maxRetag.readType}"
  IO.println s!"timestamp:tie-equal:{boolCode (maxRead == maxRetag)}:{orderingCode (some (VTimestamp.compare maxRead maxRetag))}"
  let changed := maxRead.setReadType .Retag
  IO.println s!"timestamp:set-read-type:{changed.packedValue}:{changed.time}:{readTypeCode changed.readType}"
  IO.println s!"timestamp:overflow:{match VTimestamp.encode 2147483648 .Read with | .ok _ => "0" | .error .timestampOverflow => "1" | .error _ => "other"}"

  let maxIndex := VectorIdx.ofU32 4294967295 (by decide)
  IO.println s!"index:max:{maxIndex.toNat}"
  IO.println s!"index:overflow:{match VectorIdx.ofNat 4294967296 with | .ok _ => "0" | .error .vectorIndexOverflow => "1" | .error _ => "other"}"

  let empty : VClock := .default
  let zeroRetag := timestamp 0 .Retag
  IO.println s!"clock:zero:{clockCode empty}"
  IO.println s!"clock:new-zero-retag:{clockCode (VClock.newWithIndex (vectorIdx 3) zeroRetag)}"
  IO.println s!"clock:new-at:{clockCode (VClock.newWithIndex (vectorIdx 3) (timestamp 2 .Retag))}"
  IO.println s!"clock:trim-trailing-retag:{clockCode (VClock.fromTimestamps [timestamp 2 .Read, zeroRetag, zeroRetag])}"
  IO.println s!"clock:missing-index:{timestampCode (empty.index (vectorIdx 9))}"

  let interiorRetag := VClock.fromTimestamps
    [timestamp 1 .Read, zeroRetag, timestamp 2 .Read]
  let incremented := interiorRetag.incrementIndex (vectorIdx 1)
  IO.println s!"clock:increment-interior:{match incremented with | .ok c => clockCode c | .error _ => "error"}"
  let incrementedTail := interiorRetag.incrementIndex (vectorIdx 4)
  IO.println s!"clock:increment-tail:{match incrementedTail with | .ok c => clockCode c | .error _ => "error"}"
  let overflowClock := VClock.newWithIndex (vectorIdx 0) maxRead
  IO.println s!"clock:increment-overflow:{match overflowClock.incrementIndex (vectorIdx 0) with | .ok _ => "ok" | .error .timestampOverflow => "overflow" | .error _ => "other"}"

  let joinLeft := VClock.fromTimestamps
    [timestamp 1 .Read, timestamp 3 .Read, zeroRetag, timestamp 6 .Read]
  let joinRight := VClock.fromTimestamps
    [timestamp 1 .Retag, timestamp 2 .Retag, timestamp 0 .Read, timestamp 6 .Retag]
  let joined := joinLeft.join joinRight
  IO.println s!"clock:join-ties:{clockCode joined}"
  IO.println s!"clock:join-zero:{clockCode (empty.join joined)}"

  let setLeft := fromTimes [1, 2]
  let setRight := VClock.fromTimestamps
    [timestamp 1 .Retag, timestamp 3 .Retag, timestamp 4 .Read, timestamp 5 .Retag]
  let setExtended := setLeft.setAtIndex setRight (vectorIdx 3)
  IO.println s!"clock:set-extend:{match setExtended with | .ok c => clockCode c | .error _ => "error"}"
  let setZeroTail := setLeft.setAtIndex empty (vectorIdx 8)
  IO.println s!"clock:set-zero-outside:{match setZeroTail with | .ok c => clockCode c | .error _ => "error"}"
  let setInteriorRetag := interiorRetag.setAtIndex
    (VClock.fromTimestamps [timestamp 1 .Read, zeroRetag, timestamp 2 .Read]) (vectorIdx 1)
  IO.println s!"clock:set-interior-retag:{match setInteriorRetag with | .ok c => clockCode c | .error _ => "error"}"
  let decrease := (fromTimes [2]).setAtIndex (fromTimes [1]) (vectorIdx 0)
  IO.println s!"clock:set-decrease:{match decrease with | .ok _ => "ok" | .error .setAtIndexWouldDecrease => "assert" | .error _ => "other"}"
  let applied := interiorRetag.applyReadType (vectorIdx 1) .Retag
  IO.println s!"clock:apply-read-type:{match applied with | .ok c => clockCode c | .error _ => "error"}"
  IO.println s!"clock:apply-read-type-oob:{match empty.applyReadType (vectorIdx 0) .Retag with | .ok _ => "ok" | .error .mutableIndexOutOfBounds => "oob" | .error _ => "other"}"
  IO.println s!"clock:clear:{clockCode (joinLeft.setZeroVector)}"

  emitComparison "equal" (fromTimes [1]) (fromTimes [1])
  emitComparison "less" (fromTimes [1]) (fromTimes [2])
  emitComparison "greater" (fromTimes [2]) (fromTimes [1])
  emitComparison "prefix-less" (fromTimes [1]) (fromTimes [1, 2])
  emitComparison "incomparable-prefix" (fromTimes [2]) (fromTimes [1, 2])
  emitComparison "incomparable-cross" (fromTimes [400]) (fromTimes [0, 1])
  emitComparison "long-equal" (fromTimes (List.range 11))
    (fromTimes (List.range 11 ++ [0, 0, 0]))
  emitComparison "long-less" (fromTimes (List.range 11))
    (fromTimes (List.range 11 ++ [0, 1]))
  emitComparison "long-greater" (fromTimes (List.range 10 ++ [11]))
    (fromTimes (List.range 11 ++ [0, 0, 0]))
  emitComparison "long-incomparable" (fromTimes (List.range 10 ++ [11]))
    (fromTimes (List.range 11 ++ [0, 1]))
  emitComparison "long-less-tail" (fromTimes (List.range 10 ++ [9]))
    (fromTimes (List.range 11 ++ [0, 1]))
  emitComparison "retag-tie" (VClock.fromTimestamps [timestamp 5 .Read])
    (VClock.fromTimestamps [timestamp 5 .Retag])

  let smallClocks := smallClockInputs
  for leftIndex in [:smallClocks.size] do
    for rightIndex in [:smallClocks.size] do
      let left := smallClocks[leftIndex]!
      let right := smallClocks[rightIndex]!
      emitComparison s!"small:{leftIndex}:{rightIndex}" left right
      IO.println s!"join:small:{leftIndex}:{rightIndex}:{clockCode (left.join right)}"
