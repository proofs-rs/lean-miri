import duplicate_prefix.GlobalRelocationConversion
namespace DuplicatePrefix.GlobalRelocationWordDecode
open Miri.ABI Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def bytes (b : Fin 8 → UInt8) : Array UInt8 := #[b 0,b 1,b 2,b 3,b 4,b 5,b 6,b 7]
def little (b : Fin 8 → UInt8) : Nat :=
  (b 0).toNat + (b 1).toNat*256 + (b 2).toNat*65536 + (b 3).toNat*16777216 +
  (b 4).toNat*4294967296 + (b 5).toNat*1099511627776 +
  (b 6).toNat*281474976710656 + (b 7).toNat*72057594037927936

def big (b : Fin 8 → UInt8) : Nat :=
  (b 7).toNat + (b 6).toNat*256 + (b 5).toNat*65536 + (b 4).toNat*16777216 +
  (b 3).toNat*4294967296 + (b 2).toNat*1099511627776 +
  (b 1).toNat*281474976710656 + (b 0).toNat*72057594037927936

def value (layout : TargetDataLayout) (b : Fin 8 → UInt8) : UInt64 :=
  UInt64.ofNat (if layout.endian == .little then little b else big b)

theorem bounded (b : Fin 8 → UInt8) : little b < 18446744073709551616 := by
  have h0 := UInt8.toNat_lt (b 0);have h1 := UInt8.toNat_lt (b 1)
  have h2 := UInt8.toNat_lt (b 2);have h3 := UInt8.toNat_lt (b 3)
  have h4 := UInt8.toNat_lt (b 4);have h5 := UInt8.toNat_lt (b 5)
  have h6 := UInt8.toNat_lt (b 6);have h7 := UInt8.toNat_lt (b 7)
  unfold little
  omega

theorem big_bounded (b : Fin 8 → UInt8) : big b < 18446744073709551616 := by
  have h0 := UInt8.toNat_lt (b 0);have h1 := UInt8.toNat_lt (b 1)
  have h2 := UInt8.toNat_lt (b 2);have h3 := UInt8.toNat_lt (b 3)
  have h4 := UInt8.toNat_lt (b 4);have h5 := UInt8.toNat_lt (b 5)
  have h6 := UInt8.toNat_lt (b 6);have h7 := UInt8.toNat_lt (b 7)
  unfold big
  omega

/-- The pinned endian reader succeeds on all eight bytes, without a callback
success premise or restriction to zero/nonzero sample words. -/
theorem read (layout : TargetDataLayout) (b : Fin 8 → UInt8) :
    relocation_read layout (bytes b) = .ok (BitVec.ofNat 128 (value layout b).toNat) := by
  unfold_global_data ".Miri.Memory.readTargetUInt"
  have forward := bounded b
  have backward := big_bounded b
  simp [little,big] at forward backward
  cases endian : layout.endian <;>
    simp [bytes,value,little,big,endian,
      bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,List.range'_succ,List.forIn_cons,List.forIn_nil,
      Nat.mul_comm,Nat.add_assoc] <;> congr 1 <;> omega
end DuplicatePrefix.GlobalRelocationWordDecode
