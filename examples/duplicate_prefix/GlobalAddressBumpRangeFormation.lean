import duplicate_prefix.GlobalAddressRangeFormation
namespace DuplicatePrefix.GlobalAddressBumpRangeFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressRangeFormation WildcardEmptyFamilyFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def length (size : Size) : UInt64 := if size.bytes < 1 then 1 else size.bytes

def base (generator : AddressGenerator) (slack : Fin 16) : UInt64 := generator.nextBaseAddr + UInt64.ofNat slack.val

def next (generator : AddressGenerator) (size : Size) (slack : Fin 16) : AddressGenerator :=
  {generator with nextBaseAddr := base generator slack + length size}

/-- Raw arithmetic headroom, rather than a generator-success premise. This
unit uses actual one-byte alignment, legal Fin16 slack and max(size,1) bump. -/
def Room (generator : AddressGenerator) (size : Size) (slack : Fin 16) : Prop :=
  generator.nextBaseAddr.toNat + slack.val + (length size).toNat < 2^64 ∧
  generator.nextBaseAddr.toNat + slack.val + (length size).toNat ≤ generator.endAddr.toNat

theorem length_nat (size : Size) : (length size).toNat = max 1 size.bytes.toNat := by
  unfold length
  split
  · rename_i small
    have low := UInt64.lt_iff_toNat_lt.mp small
    change size.bytes.toNat < 1 at low
    change 1 = max 1 size.bytes.toNat
    omega
  · rename_i large
    have low : ¬size.bytes.toNat < 1 := by
      rw [UInt64.lt_iff_toNat_lt] at large
      exact large
    omega

theorem base_nat (generator : AddressGenerator) (size : Size) (slack : Fin 16) (room : Room generator size slack) :
    (base generator slack).toNat = generator.nextBaseAddr.toNat + slack.val := by
  have slackNat : (UInt64.ofNat slack.val).toNat = slack.val := by rw [UInt64.toNat_ofNat'];omega
  unfold base
  rw [UInt64.toNat_add,slackNat,Nat.mod_eq_of_lt]
  have positive := length_nat size
  have bounded := room.1
  omega

theorem next_nat (generator : AddressGenerator) (size : Size) (slack : Fin 16) (room : Room generator size slack) :
    (next generator size slack).nextBaseAddr.toNat = generator.nextBaseAddr.toNat+slack.val+max 1 size.bytes.toNat := by
  change (base generator slack + length size).toNat = _
  rw [UInt64.toNat_add,base_nat generator size slack room,Nat.mod_eq_of_lt]
  · rw [length_nat]
  · exact room.1

/-- Actual checked source generation completes and advances the cursor by at
least one even for zero size; no chosen address/nonoverlap premise is supplied. -/
theorem generated (generator : AddressGenerator) (size : Size) (slack : Fin 16) (room : Room generator size slack) :
    generator.generate size Align.ONE slack = ⟨next generator size slack,.ok (base generator slack)⟩ := by
  have baseValue := base_nat generator size slack room
  have nextValue := next_nat generator size slack room
  have first : ¬base generator slack < generator.nextBaseAddr := by
    rw [UInt64.lt_iff_toNat_lt,baseValue]
    omega
  have second : ¬(base generator slack + length size) < base generator slack := by
    rw [UInt64.lt_iff_toNat_lt,baseValue]
    change ¬(next generator size slack).nextBaseAddr.toNat < _
    rw [nextValue]
    omega
  have third : ¬(base generator slack + length size) > generator.endAddr := by
    change ¬generator.endAddr.toNat < (next generator size slack).nextBaseAddr.toNat
    rw [nextValue]
    have limit := room.2
    rw [length_nat] at limit
    omega
  unfold AddressGenerator.generate
  simp only [show Align.bytes Align.ONE = .ok 1 from rfl,show Align.fromBytes 1 = .ok Align.ONE from rfl,
    bne_self_eq_false,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  change (if base generator slack < generator.nextBaseAddr then _ else _) = _
  simp only [first,↓reduceIte]
  simp only [AddressGenerator.alignAddr,beq_iff_eq,show (1:UInt64)≠0 from by decide,↓reduceIte,UInt64.mod_one,eq_self_iff_true]
  simp only [Except.bind,bind,pure,Except.pure]
  change (if base generator slack + length size < base generator slack then _ else _) = _
  simp only [second,↓reduceIte]
  change (if base generator slack + length size > generator.endAddr then _ else _) = _
  rw [if_neg third]
  rfl

/-- The stronger cursor frontier is formed by each source bump. It supplies
both range separation and distinct addresses for zero-sized allocations. -/
def Frontier (entries : Array InverseAddressEntry) (sizes : AllocId → Size) (generator : AddressGenerator) : Prop :=
  ∀ row ∈ entries, row.address.toNat + max 1 (sizes row.allocId).bytes.toNat ≤ generator.nextBaseAddr.toNat

theorem placement (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (generator : AddressGenerator) (initial : Frontier entries sizes generator)
    (id : AllocId) (size : Size) (sizeEq : sizes id = size) (slack : Fin 16) (room : Room generator size slack) :
    WildcardInteriorHitAddress.Cut entries (base generator slack) entries.size ∧
    Placement entries sizes id (base generator slack) entries.size := by
  have value := base_nat generator size slack room
  refine ⟨⟨Nat.le_refl _,?_,by intro index valid outside;omega⟩,?_,by intro index valid outside;omega⟩
  · intro index valid before
    have prior := initial entries[index] (Array.getElem_mem valid)
    apply UInt64.lt_iff_toNat_lt.mpr
    omega
  · intro index valid before
    have prior := initial entries[index] (Array.getElem_mem valid)
    omega

end DuplicatePrefix.GlobalAddressBumpRangeFormation
