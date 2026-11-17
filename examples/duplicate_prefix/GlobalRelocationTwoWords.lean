import duplicate_prefix.GlobalRelocationSplice
namespace DuplicatePrefix.GlobalRelocationTwoWords
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Row where
  position : Size
  provenance : CtfeProvenance
  base : UInt64
  root : BorTag
  word : Fin 8 → UInt8

def Known {K : Type} (memory : MemoryState Provenance BorrowTree K) (tracker : MachineHooks.BorrowState)
    (addresses : Array AllocAddresses.BaseAddressEntry) (row : Row) : Prop :=
  GlobalRelocationWindowConversion.KnownTarget memory row.provenance ∧
    tracker.global.rootTag? row.provenance.allocId = some row.root ∧
    addresses.find? (fun entry => entry.allocId == row.provenance.allocId) = some ⟨row.provenance.allocId,row.base⟩

private theorem convert {Error State : Type}
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (before : State) (rows : Fin 2 → Row)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (width : layout.pointerWidth = .w64)
    (windows : ∀ i, (AllocationCopy.snapshot source).extract (rows i).position.bytes.toNat
      ((rows i).position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes (rows i).word)
    (separate : (rows 0).position.bytes.toNat+8 ≤ (rows 1).position.bytes.toNat)
    (bounds : (rows 1).position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size)
    (relocations : source.provenanceMap.ptrs = #[((rows 0).position,(rows 0).provenance),((rows 1).position,(rows 1).provenance)])
    (noFragments : source.provenanceMap.byteFragments = none)
    (resolved : ∀ i, pointer (Pointer.new (rows i).provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout (rows i).word))) before =
      .ok (Pointer.new (Provenance.concrete (rows i).provenance.allocId (rows i).root)
        (Size.ofBytes ((rows i).base+GlobalRelocationWordDecode.value layout (rows i).word))) before) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = #[((rows 0).position,Provenance.concrete (rows 0).provenance.allocId (rows 0).root),
        ((rows 1).position,Provenance.concrete (rows 1).provenance.allocId (rows 1).root)] ∧
      converted.provenanceMap.byteFragments = none := by
  obtain ⟨encoded0,encoding0,size0⟩ := PhysicalScalarReturn.target_word_exists layout
    (BitVec.ofNat 128 ((rows 0).base+GlobalRelocationWordDecode.value layout (rows 0).word).toNat)
  obtain ⟨encoded1,encoding1,size1⟩ := PhysicalScalarReturn.target_word_exists layout
    (BitVec.ofNat 128 ((rows 1).base+GlobalRelocationWordDecode.value layout (rows 1).word).toNat)
  have ordered : (rows 0).position.bytes < (rows 1).position.bytes := by
    change (rows 0).position.bytes.toNat < (rows 1).position.bytes.toNat
    omega
  have provenanceResult : ∃ result : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs #[((rows 0).position,Provenance.concrete (rows 0).provenance.allocId (rows 0).root),
        ((rows 1).position,Provenance.concrete (rows 1).provenance.allocId (rows 1).root)] = .ok result ∧
      result.ptrs = #[((rows 0).position,Provenance.concrete (rows 0).provenance.allocId (rows 0).root),
        ((rows 1).position,Provenance.concrete (rows 1).provenance.allocId (rows 1).root)] ∧ result.byteFragments = none := by
    simp only [ProvenanceMap.fromPresortedPtrs]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    simp [ordered]
  obtain ⟨resultProvenance,provenanceResult,provenancePtrs,provenanceFragments⟩ := provenanceResult
  have window0 := windows 0
  have window1 := windows 1
  have resolved0 := resolved 0
  have resolved1 := resolved 1
  cases source
  rename_i raw size map mask align mutability extra native
  cases map
  rename_i ptrs fragments
  change ptrs = _ at relocations
  change fragments = none at noFragments
  subst ptrs
  subst fragments
  simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size,pure,Pure.pure,Except.pure,Except.toOption] at bounds window0 window1
  have firstSize := GlobalRelocationSplice.size raw encoded0 (rows 0).position.bytes.toNat (by omega) size0
  have later := (GlobalRelocationSplice.later_window raw encoded0 (rows 0).position.bytes.toNat
    (rows 1).position.bytes.toNat separate bounds size0).trans window1
  have patchedSize := GlobalRelocationSplice.size (GlobalRelocationSplice.patch raw encoded0 (rows 0).position.bytes.toNat)
    encoded1 (rows 1).position.bytes.toNat (by rw [firstSize];exact bounds) size1
  rw [firstSize] at patchedSize
  simp only [GlobalRelocationSplice.patch,Array.append_assoc] at firstSize later patchedSize
  simp only [firstSize] at patchedSize
  have offset0 := UInt64.toNat_lt (GlobalRelocationWordDecode.value layout (rows 0).word)
  have offset1 := UInt64.toNat_lt (GlobalRelocationWordDecode.value layout (rows 1).word)
  have offset1280 : (GlobalRelocationWordDecode.value layout (rows 0).word).toNat < 340282366920938463463374607431768211456 := by omega
  have offset1281 : (GlobalRelocationWordDecode.value layout (rows 1).word).toNat < 340282366920938463463374607431768211456 := by omega
  simp only [Allocation.adjustFromTcx,AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size]
  unfold_global_data ".Miri.Memory.pointerSize"
  unfold_global_data ".Miri.Memory.maxU64Nat"
  simp only [Size.ofBytes,UInt64.toNat_add] at encoding0 encoding1
  simp only [Pointer.new,Size.ofBytes] at resolved0 resolved1
  simp [-Array.extract_append,-Array.extract_extract,width,Size.fromBits,PointerWidth.bits,Except.toOption,Pointer.new,window0,later,
    GlobalRelocationWordDecode.read,resolved0,resolved1,encoding0,encoding1,provenanceResult,Size.ofBytes,
    firstSize,Array.append_assoc,
    show ¬((rows 0).position.bytes.toNat+8>raw.size) from by omega,
    show ¬((rows 1).position.bytes.toNat+8>raw.size) from by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt offset1280,Nat.mod_eq_of_lt offset1281,
    show ¬((GlobalRelocationWordDecode.value layout (rows 0).word).toNat>18446744073709551615) from by omega,
    show ¬((GlobalRelocationWordDecode.value layout (rows 1).word).toNat>18446744073709551615) from by omega,
    bind,Bind.bind,pure,Pure.pure,Except.pure,Id.run,List.forIn_cons,List.forIn_nil]
  refine ⟨⟨rfl,?_,rfl,rfl,rfl,rfl⟩,provenancePtrs,provenanceFragments⟩
  change _=raw.size
  exact patchedSize

/-- Two real relocations, with all reader and root callback outcomes derived
from initial byte windows, compiler declarations and root/address caches. -/
theorem two {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState) (rows : Fin 2 → Row)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (known : ∀ i, Known before.memory tracker before.user.addresses.baseAddr (rows i))
    (enabled : before.borrowTracker = some tracker)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (windows : ∀ i, (AllocationCopy.snapshot source).extract (rows i).position.bytes.toNat
      ((rows i).position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes (rows i).word)
    (separate : (rows 0).position.bytes.toNat+8 ≤ (rows 1).position.bytes.toNat)
    (bounds : (rows 1).position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size)
    (relocations : source.provenanceMap.ptrs = #[((rows 0).position,(rows 0).provenance),((rows 1).position,(rows 1).provenance)])
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer choices hooks externStatic) before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = #[((rows 0).position,Provenance.concrete (rows 0).provenance.allocId (rows 0).root),
        ((rows 1).position,Provenance.concrete (rows 1).provenance.allocId (rows 1).root)] ∧
      converted.provenanceMap.byteFragments = none := by
  apply convert (PointerSource.globalRootPointer choices hooks externStatic) before rows source layout width windows separate bounds relocations noFragments
  intro i
  obtain ⟨target,rootCached,addressCached⟩ := known i
  rcases target with ⟨allocation,descriptor⟩ | ⟨definition,size,align,mutability,descriptor⟩
  · exact GlobalRelocationRootPointer.cached choices hooks externStatic before tracker (rows i).provenance
      (GlobalRelocationWordDecode.value layout (rows i).word) (rows i).base (rows i).root allocation descriptor enabled rootCached addressCached arithmetic
  · exact GlobalStaticRelocationConversion.cached_root choices hooks externStatic before tracker (rows i).provenance
      (GlobalRelocationWordDecode.value layout (rows i).word) (rows i).base (rows i).root definition size align mutability descriptor enabled rootCached addressCached arithmetic
end DuplicatePrefix.GlobalRelocationTwoWords
