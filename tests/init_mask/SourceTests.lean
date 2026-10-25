import Miri.Memory.InitMask

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def interval (start finish : Nat) : AllocRange :=
  allocRange (size start) (size (finish - start))

private def must {α : Type} (label : String) (value : Except InitMaskError α) : IO α := do
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"{label}: {error}")

private def ensure (label : String) (condition : Bool) : IO Unit :=
  if condition then pure () else throw (IO.userError s!"failed source test: {label}")

private def succeeded {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

private def failed {ε α : Type} : Except ε α → Bool
  | .ok _ => false
  | .error _ => true

private def bit (mask : InitMask) (index : Nat) : IO Bool :=
  must s!"get({index})" (mask.get (size index))

private def blockCount (mask : InitMask) : Nat := mask.materializedBlockCount

private def chunkCount (mask : InitMask) (start finish : Nat) : IO Nat := do
  let iter ← must "rangeAsInitChunks" (mask.rangeAsInitChunks (interval start finish))
  let chunks ← must "collectChunks" (InitMask.collectChunks iter)
  pure chunks.size

private def allBits (label : String) (mask : InitMask)
    (start finish : Nat) (expected : Bool) : IO Unit := do
  for index in [start:finish] do
    ensure s!"{label} byte {index}" ((← bit mask index) == expected)

private def sourceUninitMask : IO Unit := do
  let mut mask := InitMask.new (size 500) false
  ensure "new uninit get" (!(← bit mask 499))
  mask ← must "set byte 499" (mask.setRange (allocRange (size 499) (size 1)) true)
  ensure "byte 499 set" (← bit mask 499)
  mask ← must "set 100..256" (mask.setRange (interval 100 256) true)
  allBits "prefix remains uninit" mask 0 100 false
  allBits "selected region initialized" mask 100 256 true
  allBits "middle remains uninit" mask 256 499 false

private def sourceMaterializeWithinRange : IO Unit := do
  let mut mask := InitMask.new (size 16) false
  ensure "new lazy mask" (blockCount mask == 0)
  mask ← must "materialize partial range" (mask.setRange (interval 8 16) true)
  ensure "one materialized block" (blockCount mask == 1)
  allBits "prefix false" mask 0 8 false
  allBits "suffix true" mask 8 16 true

private def sourceGrowFullOverwrite : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  allBits "initial full mask" mask 0 16 true
  mask ← must "full overwrite and grow" (mask.setRange (interval 0 32) true)
  allBits "grown full mask" mask 0 32 true
  ensure "full overwrite stays lazy" (blockCount mask == 0)

private def sourceGrowSameStateWithinUnused : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  mask ← must "same-state grow within spare capacity" (mask.setRange (interval 24 32) true)
  allBits "same-state gap" mask 16 24 true
  allBits "same-state grown range" mask 24 32 true
  ensure "one chunk" ((← chunkCount mask 0 32) == 1)
  ensure "same-state grow remains lazy" (blockCount mask == 0)

private def sourceGrowMixedWithinUnused : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  mask ← must "mixed grow within spare capacity" (mask.setRange (interval 24 32) false)
  allBits "mixed gap" mask 16 24 false
  allBits "mixed range" mask 24 32 false
  ensure "prefix chunks" ((← chunkCount mask 0 16) == 1)
  ensure "grown chunks" ((← chunkCount mask 0 32) == 2)
  ensure "one materialized block" (blockCount mask == 1)

private def sourceGrowOverlap : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  mask ← must "overlapping grow" (mask.setRange (interval 8 24) false)
  allBits "overlap write" mask 8 24 false
  ensure "unchanged prefix chunk" ((← chunkCount mask 0 8) == 1)
  ensure "overlap chunks" ((← chunkCount mask 0 24) == 2)
  ensure "one materialized block" (blockCount mask == 1)

private def sourceGrowMixedThenOverwrite : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  let full ← must "query initial range" (mask.isRangeInitialized (interval 0 16))
  ensure "initial range initialized" (succeeded full)
  mask ← must "force materialization" (mask.setRange (interval 8 24) false)
  let mixed ← must "query mixed range" (mask.isRangeInitialized (interval 8 24))
  ensure "mixed range uninitialized" (failed mixed)
  ensure "materialized before overwrite" (blockCount mask == 1)
  mask ← must "full overwrite to lazy" (mask.setRange (interval 0 32) true)
  let overwritten ← must "query overwritten range" (mask.isRangeInitialized (interval 0 32))
  ensure "overwritten range initialized" (succeeded overwritten)
  ensure "one chunk after overwrite" ((← chunkCount mask 0 32) == 1)
  ensure "full overwrite clears blocks" (blockCount mask == 0)

private def sourceGrowSameStateOutsideCapacity : IO Unit := do
  let mut mask := InitMask.new (size 16) true
  mask ← must "same-state grow outside capacity" (mask.setRange (interval 24 640) true)
  ensure "outside-capacity single chunk" ((← chunkCount mask 0 640) == 1)
  ensure "outside-capacity growth remains lazy" (blockCount mask == 0)

private def sourceAllocRange : IO Unit := do
  let outer := allocRange (size 10) (size 8)
  let inner ← must "checked AllocRange subrange" (outer.subrange (allocRange (size 6) (size 2)))
  ensure "subrange start is relative to outer range" (inner.start.bytes == UInt64.ofNat 16)
  ensure "subrange length is preserved" (inner.size.bytes == UInt64.ofNat 2)
  let escaped := outer.subrange (allocRange (size 7) (size 2))
  let escapedRejected := match escaped with
    | .error (.accessOutsideBounds _ _ _ _) => true
    | _ => false
  ensure "escaping AllocRange rejected" escapedRejected
  let backwards := AllocRange.fromEndpoints (size 2) (size 1)
  let backwardsRejected := match backwards with
    | .error (.sizeError (.negativeSubtraction _ _)) => true
    | _ => false
  ensure "descending endpoint construction rejected" backwardsRejected
  let overflow := (allocRange (size 18446744073709551615) (size 1)).end
  let overflowRejected := match overflow with
    | .error (.sizeError (.u64Overflow "add" _ _)) => true
    | _ => false
  ensure "AllocRange end overflow rejected" overflowRejected

private def sourceRejectsMalformedLeanStates : IO Unit := do
  let mask := InitMask.new (size 1) true
  let malformedIter : InitChunkIter := ⟨mask, false, size 0, size 1⟩
  let iterRejected := match malformedIter.next? with
    | .error (.invalidChunkIterator _ _) => true
    | _ => false
  ensure "malformed chunk iterator rejected" iterRejected
  let emptyCopy : InitCopy := ⟨false, #[]⟩
  let copyRejected := match mask.applyCopy emptyCopy (interval 0 1) 1 with
    | .error .invalidCopyEncoding => true
    | _ => false
  ensure "empty copy encoding rejected" copyRejected

def main : IO Unit := do
  sourceUninitMask
  sourceMaterializeWithinRange
  sourceGrowFullOverwrite
  sourceGrowSameStateWithinUnused
  sourceGrowMixedWithinUnused
  sourceGrowOverlap
  sourceGrowMixedThenOverwrite
  sourceGrowSameStateOutsideCapacity
  sourceAllocRange
  sourceRejectsMalformedLeanStates
  IO.println "passed all pinned rustc init-mask helper scenarios"
