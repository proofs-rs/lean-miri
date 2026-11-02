import duplicate_prefix.GlobalAddressRangeAllocationStage
namespace DuplicatePrefix.GlobalAddressAlignedBumpFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressBumpRangeFormation (length length_nat Frontier)
open GlobalAddressRangeFormation (Placement)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def alignment (align : Align) : UInt64 := UInt64.shiftLeft 1 (UInt64.ofNat align.pow2)

/-- Every source-supported exponent, rather than a supplied successful align
query, yields nonzero bytes and round-trips through actual ABI normalization. -/
theorem align_metadata (align : Align) (valid : align.pow2 ≤ 29) :
    Align.bytes align = .ok (alignment align) ∧ Align.fromBytes (alignment align) = .ok align ∧ alignment align ≠ 0 := by
  cases align with
  | mk power =>
    change power ≤ 29 at valid
    have possibilities : power = 0 ∨ power = 1 ∨ power = 2 ∨ power = 3 ∨ power = 4 ∨ power = 5 ∨ power = 6 ∨ power = 7 ∨ power = 8 ∨ power = 9 ∨ power = 10 ∨ power = 11 ∨ power = 12 ∨ power = 13 ∨ power = 14 ∨ power = 15 ∨ power = 16 ∨ power = 17 ∨ power = 18 ∨ power = 19 ∨ power = 20 ∨ power = 21 ∨ power = 22 ∨ power = 23 ∨ power = 24 ∨ power = 25 ∨ power = 26 ∨ power = 27 ∨ power = 28 ∨ power = 29 := by omega
    rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

def slackBase (generator : AddressGenerator) (slack : Fin 16) : UInt64 := generator.nextBaseAddr + UInt64.ofNat slack.val

def base (generator : AddressGenerator) (align : Align) (slack : Fin 16) : UInt64 :=
  let value := slackBase generator slack
  let bytes := alignment align
  if value % bytes = 0 then value else value + bytes - value % bytes

def next (generator : AddressGenerator) (size : Size) (align : Align) (slack : Fin 16) : AddressGenerator :=
  {generator with nextBaseAddr := base generator align slack + length size}

/-- Checked headroom includes the source's whole-alignment addition before
remainder subtraction, legal slack and max(size,1) zero-size uniqueness bump. -/
def Room (generator : AddressGenerator) (size : Size) (align : Align) (slack : Fin 16) : Prop :=
  generator.nextBaseAddr.toNat + slack.val + (alignment align).toNat + (length size).toNat < 2^64 ∧
  generator.nextBaseAddr.toNat + slack.val + (alignment align).toNat + (length size).toNat ≤ generator.endAddr.toNat

theorem slack_nat (generator : AddressGenerator) (size : Size) (align : Align) (slack : Fin 16) (room : Room generator size align slack) :
    (slackBase generator slack).toNat = generator.nextBaseAddr.toNat+slack.val := by
  have small : (UInt64.ofNat slack.val).toNat=slack.val := by rw [UInt64.toNat_ofNat'];omega
  unfold slackBase
  rw [UInt64.toNat_add,small,Nat.mod_eq_of_lt]
  have bounded:=room.1
  omega

theorem add_nat (generator : AddressGenerator) (size : Size) (align : Align) (slack : Fin 16) (room : Room generator size align slack) :
    (slackBase generator slack + alignment align).toNat = generator.nextBaseAddr.toNat+slack.val+(alignment align).toNat := by
  rw [UInt64.toNat_add,slack_nat generator size align slack room,Nat.mod_eq_of_lt]
  have bounded:=room.1
  omega

theorem base_bounds (generator : AddressGenerator) (size : Size) (align : Align) (valid : align.pow2≤29)
    (slack : Fin 16) (room : Room generator size align slack) :
    generator.nextBaseAddr.toNat+slack.val ≤ (base generator align slack).toNat ∧
    (base generator align slack).toNat ≤ generator.nextBaseAddr.toNat+slack.val+(alignment align).toNat := by
  have positive : 0 < (alignment align).toNat := by
    have nonzero:=(align_metadata align valid).2.2
    have bound:=UInt64.toNat_lt (alignment align)
    have nz : (alignment align).toNat ≠ 0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    omega
  have remainder : ((slackBase generator slack) % alignment align).toNat < (alignment align).toNat := by
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ positive
  unfold base
  dsimp only
  split
  · rw [slack_nat generator size align slack room]
    exact ⟨Nat.le_refl _,by omega⟩
  · have subtract : (slackBase generator slack % alignment align) ≤ slackBase generator slack + alignment align := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [add_nat generator size align slack room]
      omega
    rw [UInt64.toNat_sub_of_le _ _ subtract,add_nat generator size align slack room]
    constructor <;> omega

theorem aligned (generator : AddressGenerator) (size : Size) (align : Align) (valid : align.pow2≤29)
    (slack : Fin 16) (room : Room generator size align slack) :
    AddressGenerator.alignAddr (slackBase generator slack) (alignment align) = .ok (base generator align slack) := by
  have nonzero := (align_metadata align valid).2.2
  have nonoverflow : ¬slackBase generator slack + alignment align < slackBase generator slack := by
    rw [UInt64.lt_iff_toNat_lt,add_nat generator size align slack room,slack_nat generator size align slack room]
    omega
  unfold AddressGenerator.alignAddr base
  by_cases zero : slackBase generator slack % alignment align = 0
  · simp [nonzero,zero,beq_iff_eq,bind,Except.bind,pure,Except.pure]
  · simp [nonzero,zero,nonoverflow,beq_iff_eq,bind,Except.bind,pure,Except.pure]

theorem next_nat (generator : AddressGenerator) (size : Size) (align : Align) (valid : align.pow2≤29)
    (slack : Fin 16) (room : Room generator size align slack) :
    (next generator size align slack).nextBaseAddr.toNat = (base generator align slack).toNat+max 1 size.bytes.toNat := by
  change (base generator align slack + length size).toNat = _
  rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
  · rw [length_nat]
  · have upper := (base_bounds generator size align valid slack room).2
    have bound:=room.1
    omega

theorem generated (generator : AddressGenerator) (size : Size) (align : Align) (valid : align.pow2≤29)
    (slack : Fin 16) (room : Room generator size align slack) :
    generator.generate size align slack = ⟨next generator size align slack,.ok (base generator align slack)⟩ := by
  obtain ⟨bytes,normal,positive⟩ := align_metadata align valid
  have one : ¬slackBase generator slack < generator.nextBaseAddr := by
    rw [UInt64.lt_iff_toNat_lt,slack_nat generator size align slack room]
    omega
  have two : ¬base generator align slack + length size < base generator align slack := by
    rw [UInt64.lt_iff_toNat_lt]
    change ¬(next generator size align slack).nextBaseAddr.toNat < _
    rw [next_nat generator size align valid slack room]
    omega
  have three : ¬base generator align slack + length size > generator.endAddr := by
    change ¬generator.endAddr.toNat < (next generator size align slack).nextBaseAddr.toNat
    rw [next_nat generator size align valid slack room]
    have upper:=(base_bounds generator size align valid slack room).2
    have bound:=room.2
    rw [length_nat] at bound
    omega
  unfold AddressGenerator.generate
  simp only [bytes,normal,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  change (if slackBase generator slack < generator.nextBaseAddr then _ else _) = _
  simp only [one,↓reduceIte]
  have normalized := aligned generator size align valid slack room
  unfold slackBase at normalized
  rw [normalized]
  change (if base generator align slack + length size < base generator align slack then _ else _) = _
  simp only [two,↓reduceIte]
  change (if base generator align slack + length size > generator.endAddr then _ else _) = _
  rw [if_neg three]
  rfl

theorem placement (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (generator : AddressGenerator) (initial : Frontier entries sizes generator)
    (id : AllocId) (size : Size) (align : Align) (valid : align.pow2≤29) (slack : Fin 16) (room : Room generator size align slack) :
    WildcardInteriorHitAddress.Cut entries (base generator align slack) entries.size ∧
    Placement entries sizes id (base generator align slack) entries.size := by
  have lower:=(base_bounds generator size align valid slack room).1
  refine ⟨⟨Nat.le_refl _,?_,by intro index valid outside;omega⟩,?_,by intro index valid outside;omega⟩
  · intro index valid before
    have prior:=initial entries[index] (Array.getElem_mem valid)
    apply UInt64.lt_iff_toNat_lt.mpr
    omega
  · intro index valid before
    have prior:=initial entries[index] (Array.getElem_mem valid)
    omega
end DuplicatePrefix.GlobalAddressAlignedBumpFormation
