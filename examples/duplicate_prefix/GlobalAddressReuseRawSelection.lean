import duplicate_prefix.GlobalAddressPhysicalRowHistory
namespace DuplicatePrefix.GlobalAddressReuseRawSelection
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressAlignedBumpFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def range (bucket : Array ReusableAddress) (size : Size) (thread : AddressThreadId) (cross : Bool) : Nat×Nat :=
  (reuse_source ".ReusePool.candidateRange") bucket size thread cross

theorem range_eq (bucket : Array ReusableAddress) (size : Size) (thread : AddressThreadId) (cross : Bool) :
    (reuse_source ".ReusePool.candidateRange") bucket size thread cross=range bucket size thread cross := rfl

/-- Raw bucket/selected-row numeric resources. No prepare/take success is
included. A future sorted/aligned pool-history invariant can form these fields
for all source-selected indices; the older hole invariant alone cannot. -/
structure Input (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool) where
  bucket : Array ReusableAddress
  present : pool.pool[align.pow2]?=some bucket
  selected : Nat
  valid : selected<bucket.size
  lower : (range bucket size thread cross).1≤selected
  upper : selected<(range bucket size thread cross).2
  fits : size.bytes≤bucket[selected].size.bytes
  aligned : bucket[selected].address%(alignment align)=0
  thread : cross=false → bucket[selected].thread=thread

theorem ensure (pool : ReusePool) (index : Nat) (bounded : index<pool.pool.size) :
    source_reuse_ensure pool index=pool := by
  unfold_internal ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [scan,show ¬pool.pool.size≤index from by omega]

theorem checked (align : Align) (valid : align.pow2≤29) :
    (reuse_source ".ReusePool.checkedPoolIndex") align=.ok align.pow2 := by
  have info:=align_metadata align valid
  unfold_internal ".ReusePool.checkedPoolIndex"
  simp only [info.1,info.2.1,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte]

theorem bucket_bound (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) : align.pow2<pool.pool.size := by
  by_cases h : align.pow2<pool.pool.size
  · exact h
  · have bad:=raw.present
    rw [Array.getElem?_eq_none (by omega)] at bad
    cases bad

def output (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) : ReusePool :=
  {pool with pool:=pool.pool.set align.pow2 (raw.bucket.eraseIdx raw.selected raw.valid) (bucket_bound pool size align thread cross raw)}

/-- The actual source prefix reports its source-computed candidate interval
from a present bucket. It neither assumes nor fabricates a successful draw. -/
theorem prepare (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) (valid : align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross=true) :
    pool.prepareTakeAddr true cross size align .other thread=
      ⟨pool,.ok (some (range raw.bucket size thread cross))⟩ := by
  have bounded : align.pow2<pool.pool.size := by
    by_cases valid : align.pow2<pool.pool.size
    · exact valid
    · have bad:=raw.present
      rw [Array.getElem?_eq_none (by omega)] at bad
      cases bad
  have nonempty : (range raw.bucket size thread cross).2≠(range raw.bucket size thread cross).1 := by
    have one:=raw.lower
    have two:=raw.upper
    omega
  unfold ReusePool.prepareTakeAddr
  simp only [show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,checked align valid,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,
    ensure pool align.pow2 bounded]
  unfold_internal ".ReusePool.subpoolAt"
  unfold_internal ".ReusePool.getSubpool?"
  simp only [raw.present,range_eq,show ((range raw.bucket size thread cross).2==(range raw.bucket size thread cross).1)=false from by simpa using nonempty,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Bool.false_eq_true,↓reduceIte]
  rfl

/-- Raw chosen-row size/alignment/thread facts force actual take_addr success,
including the real same-thread/cross-thread clock payload and bucket erase. -/
theorem take (pool : ReusePool) (size : Size) (align : Align) (thread : AddressThreadId) (cross : Bool)
    (raw : Input pool size align thread cross) (valid : align.pow2≤29)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true=true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross=true) :
    pool.takeAddr true cross raw.selected size align .other thread=
      ⟨output pool size align thread cross raw,.ok (some ⟨(raw.bucket[raw.selected]'raw.valid).address,
        if (raw.bucket[raw.selected]'raw.valid).thread==thread then none else some (raw.bucket[raw.selected]'raw.valid).clock⟩)⟩ := by
  have bounded : align.pow2<pool.pool.size := by
    by_cases valid : align.pow2<pool.pool.size
    · exact valid
    · have bad:=raw.present
      rw [Array.getElem?_eq_none (by omega)] at bad
      cases bad
  have nonempty : (range raw.bucket size thread cross).2≠(range raw.bucket size thread cross).1 := by
    have one:=raw.lower;have two:=raw.upper;omega
  have selected : ¬(raw.selected<(range raw.bucket size thread cross).1 ∨ raw.selected≥(range raw.bucket size thread cross).2) := by
    have one:=raw.lower;have two:=raw.upper;omega
  have fits : ¬(raw.bucket[raw.selected]'raw.valid).size.bytes<size.bytes := by
    have one:=UInt64.le_iff_toNat_le.mp raw.fits
    intro smaller
    have two:=UInt64.lt_iff_toNat_lt.mp smaller
    omega
  have threadOk : (!cross && ((raw.bucket[raw.selected]'raw.valid).thread != thread))=false := by
    cases cross
    · simp only [raw.thread rfl,beq_self_eq_true,bne_self_eq_false,Bool.and_false]
    · rfl
  unfold ReusePool.takeAddr
  simp only [show (AddressMemoryKind.other==AddressMemoryKind.stack)=false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,checked align valid,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,
    ensure pool align.pow2 bounded]
  unfold_internal ".ReusePool.subpoolAt"
  unfold_internal ".ReusePool.getSubpool?"
  simp only [raw.present]
  unfold_internal ".ReusePool.updateSubpool"
  simp only [range_eq,show ((range raw.bucket size thread cross).2==(range raw.bucket size thread cross).1)=false from by simpa using nonempty,
    show (raw.selected<(range raw.bucket size thread cross).1 || raw.selected≥(range raw.bucket size thread cross).2)=false from by simpa using selected,
    raw.valid,bounded,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Bool.false_eq_true,↓reduceIte,↓reduceDIte,
    fits,(align_metadata align valid).1,Except.mapError,raw.aligned,bne_self_eq_false,threadOk]
  rfl
end DuplicatePrefix.GlobalAddressReuseRawSelection
