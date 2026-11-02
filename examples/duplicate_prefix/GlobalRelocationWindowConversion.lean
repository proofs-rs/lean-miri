import duplicate_prefix.GlobalStaticRelocationConversion
namespace DuplicatePrefix.GlobalRelocationWindowConversion
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The byte window is initial source representation data. The callback equation
is an internal composition boundary, derived below from actual cached pointers. -/
private theorem convert {Error State : Type}
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (before : State) (provenance : CtfeProvenance) (base : UInt64) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout) (position : Size)
    (width : layout.pointerWidth = .w64)
    (window : (AllocationCopy.snapshot source).extract position.bytes.toNat (position.bytes.toNat+8) = #[0,0,0,0,0,0,0,0])
    (bounds : position.bytes.toNat+8≤(AllocationCopy.snapshot source).size)
    (relocation : source.provenanceMap.ptrs = #[(position,provenance)])
    (noFragments : source.provenanceMap.byteFragments = none)
    (resolved : pointer (Pointer.new provenance Size.ZERO) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) before) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = #[(position,Provenance.concrete provenance.allocId root)] ∧
      converted.provenanceMap.byteFragments = none := by
  obtain ⟨encoded,encoding,encodedSize⟩ := PhysicalScalarReturn.target_word_exists layout (BitVec.ofNat 128 base.toNat)
  have provenanceResult : ∃ result : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs #[(position,Provenance.concrete provenance.allocId root)] = .ok result ∧
      result.ptrs = #[(position,Provenance.concrete provenance.allocId root)] ∧ result.byteFragments = none := by
    simp only [ProvenanceMap.fromPresortedPtrs]
    unfold_global_data ".Miri.Memory.ProvenanceMap.sortedKeys"
    simp
  obtain ⟨resultProvenance,provenanceResult,provenancePtrs,provenanceFragments⟩ := provenanceResult
  cases source
  rename_i raw size map mask align mutability extra native
  cases map
  rename_i ptrs fragments
  change ptrs = _ at relocation
  change fragments = none at noFragments
  subst ptrs
  subst fragments
  simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size,pure,Pure.pure,Except.pure,Except.toOption] at bounds window
  have patchedSize : (raw.extract 0 position.bytes.toNat ++ encoded ++ raw.extract (position.bytes.toNat+8) raw.size).size=raw.size := by
    simp only [Array.size_append,Array.size_extract,Nat.min_self,Nat.sub_zero]
    rw [Nat.min_eq_left (by omega : position.bytes.toNat≤raw.size)]
    rw [encodedSize]
    omega
  simp only [Allocation.adjustFromTcx,AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size]
  unfold_global_data ".Miri.Memory.pointerSize"
  simp only [Size.ofBytes] at encoding
  simp only [Pointer.new,Size.ZERO,Size.ofBytes] at resolved
  simp [width,Size.fromBits,PointerWidth.bits,Except.toOption,Pointer.new,window,
    GlobalRelocationConversion.zero_word,resolved,encoding,provenanceResult,Size.ofBytes,
    show ¬(position.bytes.toNat+8>raw.size) from by omega,
    bind,Bind.bind,pure,Pure.pure,Except.pure,Id.run,List.forIn_cons,List.forIn_nil]
  exact ⟨⟨rfl,(by simpa only [Allocation.len,Array.append_assoc] using patchedSize),rfl,rfl,rfl,rfl⟩,provenancePtrs,provenanceFragments⟩
/-- Compiler declaration data for the relocation target; no initializer runs. -/
def KnownTarget {K : Type} (memory : MemoryState Provenance BorrowTree K) (provenance : CtfeProvenance) : Prop :=
  (∃ target : Allocation CtfeProvenance Unit, memory.findGlobal? provenance.allocId = some
    ⟨provenance.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩) ∨
  ∃ (definition : Nat) (size : Size) (align : Align) (mutability : Mutability),
    memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.static,size,align,mutability,some (.static definition true false false)⟩

/-- Real relocation of a zero-valued eight-byte window at any in-bounds position.
All surrounding bytes are preserved by the actual conversion algorithm. -/
theorem singleton {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (base : UInt64) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout) (position : Size)
    (target : KnownTarget before.memory provenance)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (window : (AllocationCopy.snapshot source).extract position.bytes.toNat (position.bytes.toNat+8) = #[0,0,0,0,0,0,0,0])
    (bounds : position.bytes.toNat+8≤(AllocationCopy.snapshot source).size)
    (relocation : source.provenanceMap.ptrs = #[(position,provenance)])
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer choices hooks externStatic) before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      converted.provenanceMap.ptrs = #[(position,Provenance.concrete provenance.allocId root)] ∧
      converted.provenanceMap.byteFragments = none := by
  have resolved : PointerSource.globalRootPointer choices hooks externStatic (Pointer.new provenance Size.ZERO) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) before := by
    rcases target with ⟨allocation,descriptor⟩ | ⟨definition,size,align,mutability,descriptor⟩
    · simpa only [Size.ZERO,Size.ofBytes,UInt64.add_zero] using
        GlobalRelocationRootPointer.cached choices hooks externStatic before tracker provenance 0 base root
          allocation descriptor enabled rootCached addressCached arithmetic
    · simpa only [Size.ZERO,Size.ofBytes,UInt64.add_zero] using
        GlobalStaticRelocationConversion.cached_root choices hooks externStatic before tracker provenance 0 base root
          definition size align mutability descriptor enabled rootCached addressCached arithmetic
  exact convert (PointerSource.globalRootPointer choices hooks externStatic) before provenance base root source layout
    position width window bounds relocation noFragments resolved

end DuplicatePrefix.GlobalRelocationWindowConversion
