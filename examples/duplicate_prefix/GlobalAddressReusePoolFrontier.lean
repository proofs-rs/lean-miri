import duplicate_prefix.GlobalAddressReuseFreePairwise
namespace DuplicatePrefix.GlobalAddressReusePoolFrontier
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressBumpRangeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def Bounded (generator : AddressGenerator) (entry : ReusableAddress) : Prop :=
  entry.address.toNat+max 1 entry.size.bytes.toNat≤generator.nextBaseAddr.toNat

theorem mono (pool : ReusePool) (before after : AddressGenerator)
    (initial : Contents pool (Bounded before)) (grows : before.nextBaseAddr.toNat≤after.nextBaseAddr.toNat) :
    Contents pool (Bounded after) := by
  intro bucket member entry stored
  have bound:=initial bucket member entry stored
  unfold Bounded at *
  omega

theorem released (generator : AddressGenerator) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (frontier : Frontier entries sizes generator) (id : AllocId) (address : UInt64) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<entries.size) (row : entries[position]?=some ⟨address,id⟩)
    (thread : AddressThreadId) (clock : VClock) : Bounded generator ⟨address,size,thread,clock⟩ := by
  have actual : entries[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  have bound:=frontier entries[position] (Array.getElem_mem valid)
  simpa only [actual,sizeEq,Bounded] using bound

/-- Stored holes formed below the source cursor remain disjoint from the
actual checked fresh aligned allocation; this is the missing fresh-fallback
side of recurrent pool availability. -/
theorem fresh_insert (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (generator : AddressGenerator) (holes : Contents pool (Hole entries sizes)) (bounds : Contents pool (Bounded generator))
    (id : AllocId) (size : Size) (align : Align) (valid : align.pow2≤29) (slack : Fin 16)
    (room : GlobalAddressAlignedBumpFormation.Room generator size align slack)
    (cut : Nat) (bounded : cut≤entries.size) :
    Contents pool (Hole (entries.insertIdx cut ⟨GlobalAddressAlignedBumpFormation.base generator align slack,id⟩ bounded) sizes) := by
  intro bucket member entry stored
  have initial:=holes bucket member entry stored
  have bound:=bounds bucket member entry stored
  have lower:=(GlobalAddressAlignedBumpFormation.base_bounds generator size align valid slack room).1
  refine ⟨initial.1,?_⟩
  intro row present
  rcases Array.mem_insertIdx.mp present with same | old
  · subst row
    apply Or.inr
    change entry.address.toNat+max 1 entry.size.bytes.toNat≤(GlobalAddressAlignedBumpFormation.base generator align slack).toNat
    unfold Bounded at bound
    omega
  · exact initial.2 row old

theorem take (pool : ReusePool) (generator : AddressGenerator) (initial : Contents pool (Bounded generator))
    (reuse cross : Bool) (selection : Nat) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) :
    Contents (pool.takeAddr reuse cross selection size align kind thread).state (Bounded generator) ∧
    ∀ used,(pool.takeAddr reuse cross selection size align kind thread).outcome=.ok (some used) →
      used.address.toNat+max 1 size.bytes.toNat≤generator.nextBaseAddr.toNat := by
  have facts:=GlobalAddressReuseTakeContents.take pool (Bounded generator) initial reuse cross selection size align kind thread
  refine ⟨facts.1,?_⟩
  intro used actual
  obtain ⟨entry,bound,same,fits⟩:=facts.2 used actual
  have fitsNat:=UInt64.le_iff_toNat_le.mp fits
  rw [same]
  unfold Bounded at bound
  omega
end DuplicatePrefix.GlobalAddressReusePoolFrontier
