import Miri.Concurrency.AtomicAccess

open Miri.ABI Miri.Concurrency Miri.Memory

def size1 : Size := .ofBytes 1
def size4 : Size := .ofBytes 4
def size8 : Size := .ofBytes 8
def size16 : Size := .ofBytes 16
def size3 : Size := .ofBytes 3

def readonlyOps : AtomicAccessOps Nat String String where
  checkPtrAlign := fun _ => .ok ()
  pointerTryGetAllocId := .ok 7
  getAllocMutability := fun _ => .ok .Not

def mutableOps : AtomicAccessOps Nat String String where
  checkPtrAlign := fun _ => .ok ()
  pointerTryGetAllocId := .ok 7
  getAllocMutability := fun _ => .ok .Mut

def misalignedOps : AtomicAccessOps Nat String String where
  checkPtrAlign := fun _ => .error "misaligned"
  pointerTryGetAllocId := .error "allocation lookup must not run first"
  getAllocMutability := fun _ => .error "mutability lookup must not run first"

def noAllocOps : AtomicAccessOps Nat String String where
  checkPtrAlign := fun _ => .ok ()
  pointerTryGetAllocId := .error "no allocation for pointer"
  getAllocMutability := fun _ => .error "expect must fail before mutability lookup"

def atomicAccessCode : Except (AtomicAccessError String String) Unit → String
  | .ok _ => "ok"
  | .error (.alignmentConstructionPanic _) => "panic"
  | .error (.pointerAlignment _) => "alignment"
  | .error (.allocationExpectationPanic _) => "panic"
  | .error (.mutabilityLookup _) => "mutability"
  | .error (.undefinedBehavior _) => "ub"

def sourceOps (mutability : Mutability) (alignment : Except String Unit)
    (allocation : Except String Nat) : AtomicAccessOps Nat String String where
  checkPtrAlign := fun _ => alignment
  pointerTryGetAllocId := allocation
  getAllocMutability := fun _ => .ok mutability

example : atomicAccessCheck size4 size4 (.load .Relaxed) readonlyOps = .ok () := by
  decide

example : prepareAtomicLoad .Relaxed size4 size16 readonlyOps = .ok .Relaxed := by
  decide

-- The source tests large loads before the non-relaxed restriction, so every
-- load larger than pointer size hits this branch even when relaxed.
example : prepareAtomicLoad .Relaxed size16 size4 readonlyOps =
    .error (.accessCheck (.undefinedBehavior .oversizedLoad)) := by
  decide

example : prepareAtomicLoad .Acquire size16 size4 readonlyOps =
    .error (.accessCheck (.undefinedBehavior .oversizedLoad)) := by
  decide

example : prepareAtomicLoad .Acquire size4 size4 readonlyOps =
    .error (.accessCheck (.undefinedBehavior .nonRelaxedLoad)) := by
  decide

example : prepareAtomicStore .Relaxed size4 size4 readonlyOps =
    .error (.accessCheck (.undefinedBehavior .storeOrRmw)) := by
  decide

example : prepareAtomicRmw .AcqRel size4 size4 readonlyOps =
    .error (.accessCheck (.undefinedBehavior .storeOrRmw)) := by
  decide

-- Ordering conversion in machine.rs runs before atomic_access_check.
example : prepareAtomicLoad .Release size4 size4 misalignedOps =
    .error (.invalidOrdering (.invalidRead .Release)) := by
  decide

example : prepareAtomicCompareExchange .Relaxed .AcqRel size4 size4 misalignedOps =
    .error (.invalidOrdering (.invalidRead .AcqRel)) := by
  decide

example : atomicAccessCheck size3 size4 (.load .Relaxed) mutableOps =
    .error (.alignmentConstructionPanic (.notPowerOfTwo 3)) := by
  decide

-- Pointer alignment precedes allocation-id resolution; the callback error is
-- propagated and the subsequent lookup error cannot mask it.
example : atomicAccessCheck size4 size4 (.load .Relaxed) misalignedOps =
    .error (.pointerAlignment "misaligned") := by
  decide

example : atomicAccessCheck size4 size4 (.load .Relaxed) noAllocOps =
    .error (.allocationExpectationPanic "no allocation for pointer") := by
  decide

example : prepareAtomicFence .Relaxed true = .ok none := by
  decide

example : prepareAtomicFence .Relaxed false = .error (.invalidFence .Relaxed) := by
  decide

def main : IO Unit := do
  let readonly := sourceOps .Not (.ok ()) (.ok 1)
  let mutable := sourceOps .Mut (.ok ()) (.ok 1)
  let alignmentFailed := sourceOps .Mut (.error "alignment") (.error "pointer")
  let noAllocation := sourceOps .Mut (.ok ()) (.error "pointer address")
  IO.println s!"atomic:readonly-small-relaxed:{atomicAccessCode (atomicAccessCheck size4 size16 (.load .Relaxed) readonly)}"
  IO.println s!"atomic:readonly-large-relaxed:{atomicAccessCode (atomicAccessCheck size16 size8 (.load .Relaxed) readonly)}"
  IO.println s!"atomic:readonly-small-acquire:{atomicAccessCode (atomicAccessCheck size4 size8 (.load .Acquire) readonly)}"
  IO.println s!"atomic:readonly-store:{atomicAccessCode (atomicAccessCheck size4 size8 .store readonly)}"
  IO.println s!"atomic:readonly-rmw:{atomicAccessCode (atomicAccessCheck size4 size8 .rmw readonly)}"
  IO.println s!"atomic:mutable-large-relaxed:{atomicAccessCode (atomicAccessCheck size16 size8 (.load .Relaxed) mutable)}"
  IO.println s!"atomic:alignment-before-resolution:{atomicAccessCode (atomicAccessCheck size4 size8 (.load .Relaxed) alignmentFailed)}"
  IO.println s!"atomic:allocation-expect:{atomicAccessCode (atomicAccessCheck size4 size8 (.load .Relaxed) noAllocation)}"
  IO.println "atomic-access: source ordering, alignment, read-only, and fence checks pass"
