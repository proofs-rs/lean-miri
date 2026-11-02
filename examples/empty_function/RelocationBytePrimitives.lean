import Miri.Memory.Allocation
import Lean
namespace EmptyFunction.RelocationBytePrimitives
open Miri Miri.ABI Miri.Memory
open Lean Elab Tactic
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def sourceName (suffix : String) : TermElabM Name := do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  let [name] := names | throwError "expected original byte conversion helper {suffix}"
  return name
elab "byte_source " suffix:str : term => return ← Lean.Meta.mkConstWithFreshMVarLevels (←sourceName suffix.getString)
elab "unfold_byte_source " suffix:str : tactic => do
  let name ← sourceName suffix.getString
  evalTactic (← `(tactic| unfold $(mkIdent name)))

abbrev sourceRead := byte_source ".Miri.Memory.readTargetUInt"
abbrev sourceEncode := byte_source ".Miri.Memory.targetUIntBytes"

def snapshot {Prov Extra : Type} (allocation : Allocation Prov Extra) : Array UInt8 :=
  (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len).toOption.getD #[]

theorem snapshot_size {Prov Extra : Type} (source : Allocation Prov Extra) : (snapshot source).size = source.len := by
  cases source
  simp [snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,pure,Except.pure,Except.toOption]

theorem target_word_exists (layout : TargetDataLayout) (bits : U128) :
    ∃ encoded, sourceEncode layout (Size.ofBytes 8) bits = .ok encoded ∧ encoded.size = 8 := by
  unfold sourceEncode
  unfold_byte_source ".Miri.Memory.targetUIntBytes"
  simp [Size.ofBytes,UInt64.toNat_ofNat,bind,Except.bind,pure,Except.pure,Id.run,
    List.range'_succ,List.forIn_cons,List.forIn_nil]

def patch (raw encoded : Array UInt8) (position : Nat) : Array UInt8 :=
  raw.extract 0 position ++ encoded ++ raw.extract (position+8) raw.size

theorem size (raw encoded : Array UInt8) (position : Nat)
    (bounds : position+8≤raw.size) (width : encoded.size=8) :
    (patch raw encoded position).size=raw.size := by
  simp only [patch,Array.size_append,Array.size_extract,Nat.min_self,Nat.sub_zero]
  rw [Nat.min_eq_left (by omega : position≤raw.size),width]
  omega

/-- A completed first relocation does not alter a later disjoint source window. -/
theorem later_window (raw encoded : Array UInt8) (first second : Nat)
    (separate : first+8≤second) (bounds : second+8≤raw.size) (width : encoded.size=8) :
    (patch raw encoded first).extract second (second+8) = raw.extract second (second+8) := by
  have patchSize := size raw encoded first (by omega) width
  have prefixSize : (raw.extract 0 first).size=first := by
    simp only [Array.size_extract,Nat.sub_zero,Nat.min_eq_left (by omega : first≤raw.size)]
  apply Array.ext
  · simp only [Array.size_extract,patchSize]
  · intro i validLeft validRight
    have upper : i<8 := by
      simpa only [Array.size_extract,Nat.min_eq_left bounds,Nat.add_sub_cancel_left] using validRight
    simp only [Array.getElem_extract]
    simp only [patch,Array.getElem_append]
    simp only [Array.size_append,prefixSize,width]
    split
    · omega
    · simp only [Array.getElem_extract]
      congr 1
      omega


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
    sourceRead layout (bytes b) = .ok (BitVec.ofNat 128 (value layout b).toNat) := by
  unfold sourceRead
  unfold_byte_source ".Miri.Memory.readTargetUInt"
  have forward := bounded b
  have backward := big_bounded b
  simp [little,big] at forward backward
  cases endian : layout.endian <;>
    simp [bytes,value,little,big,endian,
      bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,List.range'_succ,List.forIn_cons,List.forIn_nil,
      Nat.mul_comm,Nat.add_assoc] <;> congr 1 <;> omega


private theorem array_eight (raw : Array UInt8) (size : raw.size = 8) :
    raw = bytes (fun i => raw[i.val]?.getD 0) := by
  apply Array.ext
  · simpa [bytes] using size
  · intro i validLeft validRight
    have bound : i < 8 := by omega
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [bytes]
    all_goals exact (congrArg (fun value : Option UInt8 => value.getD 0) (Array.getElem?_eq_getElem validLeft)).symm

/-- The offset supplied to a root callback is the actual initial source word,
including all eight arbitrary bytes and either source endianness. -/
def word (layout : TargetDataLayout) (raw : Array UInt8) (position : Nat) : UInt64 :=
  value layout (fun i => (raw.extract position (position+8))[i.val]?.getD 0)

theorem read_window (layout : TargetDataLayout) (raw : Array UInt8) (position : Nat)
    (bounds : position+8 ≤ raw.size) :
    sourceRead layout (raw.extract position (position+8)) =
      .ok (BitVec.ofNat 128 (word layout raw position).toNat) := by
  let window := raw.extract position (position+8)
  have size : window.size = 8 := by
    simp only [window,Array.size_extract,Nat.min_eq_left bounds]
    omega
  have shape := array_eight window size
  calc
    sourceRead layout window = sourceRead layout (bytes (fun i => window[i.val]?.getD 0)) := congrArg _ shape
    _ = _ := read layout _

end EmptyFunction.RelocationBytePrimitives
