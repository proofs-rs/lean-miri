import Miri.Memory.InitMask

open Miri.ABI
open Miri.Memory

private def mkSize (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def bytes (size : Size) : Nat := size.bytes.toNat
private def range (start finish : Nat) : AllocRange :=
  allocRange (mkSize start) (mkSize (finish - start))

private def requireOk {α : Type} (label : String) (result : Except InitMaskError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected InitMask error: {error}")

private def emitSnapshot (tag : String) (mask : InitMask) : IO Unit := do
  let modeAndWords := match mask.blocks with
    | .Lazy state => (s!"L{if state then 1 else 0}", "-")
    | .Materialized blocks =>
      let words : List String := blocks.blocks.toList.map fun (word : UInt64) =>
        toString (UInt64.toNat word)
      ("M", String.intercalate "," words)
  let mut bitChars := #[]
  for index in [0:bytes mask.len] do
    let bit ← requireOk s!"snapshot {tag} byte {index}" (mask.get (mkSize index))
    bitChars := bitChars.push (if bit then '1' else '0')
  let bits := String.ofList bitChars.toList
  IO.println s!"S {tag} {bytes mask.len} {modeAndWords.1} {modeAndWords.2} {bits}"

private def emitQuery (tag : String) (mask : InitMask) (start finish : Nat) : IO Unit := do
  let result := mask.isRangeInitialized (range start finish)
  let encoded ← match result with
    | .error error => pure s!"X{error}"
    | .ok (.ok ()) => pure "O"
    | .ok (.error missing) => do
      let missingEnd ← requireOk s!"query {tag} missing range end" missing.endExclusive
      pure s!"E{bytes missing.start}:{bytes missingEnd}"
  IO.println s!"R {tag} {start} {finish} {encoded}"

private def emitChunks (tag : String) (mask : InitMask) (start finish : Nat) : IO Unit := do
  let iter ← requireOk s!"chunks {tag} range" (mask.rangeAsInitChunks (range start finish))
  let chunks ← requireOk s!"chunks {tag} collect" (InitMask.collectChunks iter)
  let mut encodedChunks := #[]
  for chunk in chunks do
    let chunkRange ← requireOk s!"chunks {tag} range endpoint" chunk.range
    let chunkEnd ← requireOk s!"chunks {tag} endpoint" chunkRange.endExclusive
    encodedChunks := encodedChunks.push
      s!"{if chunk.isInit then 1 else 0}:{bytes chunkRange.start}-{bytes chunkEnd}"
  let encoded := String.intercalate "," encodedChunks.toList
  IO.println s!"C {tag} {start} {finish} {encoded}"

private def makePattern (len : Nat) (initial : Bool) (pattern : Nat) : IO InitMask := do
  let mut mask := InitMask.new (mkSize len) initial
  for index in [0:len] do
    let wanted := Nat.testBit pattern index
    if wanted != initial then
      mask ← requireOk "makePattern.setRange"
        (mask.setRange (allocRange (mkSize index) (mkSize 1)) wanted)
  pure mask

private def exhaustiveSmall : IO Unit := do
  let mut tagId := 0
  for len in [0:6] do
    for initial in [false, true] do
      for pattern in [0:2^len] do
        let mask ← makePattern len initial pattern
        let tag := s!"b{tagId}"
        tagId := tagId + 1
        emitSnapshot tag mask
        for start in [0:len + 3] do
          for finish in [start:len + 4] do
            emitQuery tag mask start finish
            if finish ≤ len then emitChunks tag mask start finish
        for start in [0:len + 3] do
          for size in [0:5] do
            for newState in [false, true] do
              let changed ← requireOk "exhaustive.setRange"
                (mask.setRange (allocRange (mkSize start) (mkSize size)) newState)
              let opTag := s!"o{tagId}:{start}:{size}:{if newState then 1 else 0}"
              emitSnapshot opTag changed

private def boundaryCases : IO Unit := do
  let ranges := #[(0, 0), (1, 64), (62, 65), (63, 64), (64, 65),
    (64, 128), (60, 130), (130, 132)]
  let mut id := 0
  for len in [63, 64, 65] do
    for initial in [false, true] do
      for (start, finish) in ranges do
        for newState in [false, true] do
          let mask ← requireOk "boundary.setRange"
            ((InitMask.new (mkSize len) initial).setRange
              (allocRange (mkSize start) (mkSize (finish - start))) newState)
          let tag := s!"x{id}"
          id := id + 1
          emitSnapshot tag mask
          for (qstart, qfinish) in #[(0, 1), (62, 63), (62, 65), (63, 64),
              (63, 65), (64, 65), (64, 66), (0, 65), (65, 66), (129, 132)] do
            emitQuery tag mask qstart qfinish
          for (cstart, cfinish) in #[(0, 0), (0, len), (min 60 len, min 63 len),
              (min 63 len, min 65 len), (min 64 len, min 65 len)] do
            emitChunks tag mask cstart cfinish

private def copyCases : IO Unit := do
  let mut sources : Array (String × InitMask × Nat × Nat) := #[]
  sources := sources.push ("lazy0", InitMask.new (mkSize 4) false, 0, 4)
  sources := sources.push ("lazy1", InitMask.new (mkSize 4) true, 0, 4)
  let mixed ← requireOk "copy mixed first write"
    ((InitMask.new (mkSize 8) true).setRange (allocRange (mkSize 1) (mkSize 2)) false)
  let mixed ← requireOk "copy mixed second write"
    (mixed.setRange (allocRange (mkSize 5) (mkSize 1)) false)
  sources := sources.push ("mixed", mixed, 0, 8)
  let boundary ← requireOk "copy boundary write"
    ((InitMask.new (mkSize 65) true).setRange (allocRange (mkSize 63) (mkSize 2)) false)
  sources := sources.push ("boundary", boundary, 60, 5)

  for (sourceName, source, sourceStart, sourceLen) in sources do
    let defined ← requireOk s!"prepareCopy {sourceName}"
      (source.prepareCopy (allocRange (mkSize sourceStart) (mkSize sourceLen)))
    let runText := String.intercalate "," (defined.ranges.toList.map fun run => toString run.toNat)
    IO.println s!"I {sourceName} {if defined.initial then 1 else 0} {if defined.noBytesInit then 1 else 0} {runText}"
    for destinationInitial in [false, true] do
      for repeatCount in [0:5] do
        let destLen := 3 + sourceLen * max repeatCount 1
        let destination := InitMask.new (mkSize destLen) destinationInitial
        let updated ← requireOk s!"applyCopy {sourceName} {repeatCount}"
          (destination.applyCopy defined (allocRange (mkSize 3) (mkSize sourceLen))
            (UInt64.ofNat repeatCount))
        let tag := s!"p{sourceName}:{if destinationInitial then 1 else 0}:{repeatCount}"
        emitSnapshot tag updated

private def errorClass : InitMaskError → String
  | .sizeError _ => "size-error"
  | .sizeFromNatOverflow _ => "size-overflow"
  | .blockCapacityTooSmall _ _ => "block-capacity-error"
  | .blockIndexOutOfBounds _ _ => "block-index-error"
  | .rangeOutOfBounds _ _ => "range-assertion"
  | .emptyCopyRange => "empty-copy-assertion"
  | .invalidCopyEncoding => "copy-encoding-error"
  | .invalidChunkIterator _ _ => "chunk-iterator-error"
  | .accessOutsideBounds _ _ _ _ => "subrange-assertion"

private def invalidCases : IO Unit := do
  let malformed : InitMask := ⟨.Materialized ⟨#[]⟩, mkSize 2⟩
  let malformedRead := match malformed.get (mkSize 0) with
    | .error err => errorClass err
    | .ok _ => "returned"
  let malformedWrite := match malformed.setRange (range 0 1) true with
    | .error err => errorClass err
    | .ok _ => "returned"
  let oobChunks := match (InitMask.new (mkSize 1) true).rangeAsInitChunks (range 0 2) with
    | .error err => errorClass err
    | .ok _ => "returned"
  let emptyCopy := match (InitMask.new (mkSize 1) false).prepareCopy (range 0 0) with
    | .error err => errorClass err
    | .ok _ => "returned"
  let oobQuery := match
      (InitMask.new (mkSize 1) false).isRangeInitialized (range 0 2) with
    | .error err => errorClass err
    | .ok (.error _) => "range-result"
    | .ok (.ok _) => "initialized"
  let overflowRange := allocRange (mkSize 18446744073709551615) (mkSize 1)
  let sizeOverflow := match (InitMask.new (mkSize 18446744073709551615) true)
      |>.isRangeInitialized overflowRange with
    | .error err => errorClass err
    | .ok _ => "returned"
  IO.println s!"V malformed-get {malformedRead}"
  IO.println s!"V malformed-set {malformedWrite}"
  IO.println s!"V oob-chunks {oobChunks}"
  IO.println s!"V empty-copy {emptyCopy}"
  IO.println s!"V oob-query {oobQuery}"
  IO.println s!"V size-overflow {sizeOverflow}"

def main : IO Unit := do
  exhaustiveSmall
  boundaryCases
  copyCases
  invalidCases
