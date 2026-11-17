import duplicate_prefix.GlobalRelocationConversion

/-! A relocation to a declared, non-TLS, non-extern static resolves through the
real globalRootPointer callback without evaluating its initializer. The target
root and address are explicit pre-existing caches. The source image is eight
zero bytes with a single offset-zero relocation, with arbitrary mutability and
initialization mask. This unit proves conversion, not a whole invocation. -/
namespace DuplicatePrefix.GlobalStaticRelocationConversion
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem cached_root {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (offset base : UInt64) (root : BorTag)
    (definition : Nat) (size : Size) (align : Align) (mutability : Mutability)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.static,size,align,mutability,some (.static definition true false false)⟩)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩) :
    PointerSource.globalRootPointer choices hooks externStatic (Pointer.new provenance (Size.ofBytes offset)) before =
      .ok (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes (base+offset))) before := by
  have rootEq := GlobalState.rootPointerTag_existing tracker.global provenance.allocId root rootCached
  have unchanged : {before with borrowTracker := some tracker} = before := by rw [←enabled]
  simp only [PointerSource.globalRootPointer,Pointer.new,descriptor,enabled,rootEq,
    MachineAddress.addrFromAllocId,get,getThe,MonadStateOf.get,EStateM.get,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,unchanged,addressCached,
    width, Bool.false_eq_true, ite_false]
  have wrapping := DuplicatePrefix.PointerArithmetic.wrapping_offset_u64
    (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)) (Size.ofBytes offset)
  change (Pointer.new (Provenance.concrete provenance.allocId root) (Size.ofBytes base)).wrappingOffset
    (Size.ofBytes offset) ⟨Size.ofBytes 8⟩ = _ at wrapping
  simp only [Pointer.new] at wrapping
  rw [wrapping]
  rfl

theorem singleton_zero {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (base : UInt64) (root : BorTag)
    (definition : Nat) (targetSize : Size) (targetAlign : Align) (targetMutability : Mutability)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.static,targetSize,targetAlign,targetMutability,some (.static definition true false false)⟩)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (rawBytes : AllocationCopy.snapshot source = #[0,0,0,0,0,0,0,0])
    (relocation : source.provenanceMap.ptrs = #[(Size.ZERO,provenance)])
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit, ∃ encoded : Array UInt8,
      Allocation.adjustFromTcx source layout
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
        (PointerSource.globalRootPointer choices hooks externStatic) before = .ok converted before ∧
      GlobalAllocationAttributes.Attributes source converted ∧
      target_bytes layout (Size.ofBytes 8) (BitVec.ofNat 128 base.toNat) = .ok encoded ∧
      encoded.size = 8 ∧ AllocationCopy.snapshot converted = encoded ∧
      converted.provenanceMap.ptrs = #[(Size.ZERO,Provenance.concrete provenance.allocId root)] ∧
      converted.provenanceMap.byteFragments = none := by
  have pointer := cached_root choices hooks externStatic before tracker provenance 0 base root
    definition targetSize targetAlign targetMutability descriptor enabled rootCached addressCached arithmetic
  simp only [UInt64.add_zero] at pointer
  obtain ⟨encoded,encoding,encodedSize⟩ := PhysicalScalarReturn.target_word_exists layout (BitVec.ofNat 128 base.toNat)
  have provenanceResult : ∃ result : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs #[(Size.ZERO,Provenance.concrete provenance.allocId root)] = .ok result ∧
      result.ptrs = #[(Size.ZERO,Provenance.concrete provenance.allocId root)] ∧ result.byteFragments = none := by
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
  have rawEq : raw = #[0,0,0,0,0,0,0,0] := by
    simpa [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
      pure,Pure.pure,Except.pure,Except.toOption] using rawBytes
  subst raw
  simp only [Allocation.adjustFromTcx,AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size]
  unfold_global_data ".Miri.Memory.pointerSize"
  simp only [Pointer.new,Size.ofBytes] at pointer
  simp only [Size.ofBytes] at encoding
  simp only [Size.ZERO] at provenanceResult provenancePtrs
  simp [width,Size.fromBits,PointerWidth.bits,Except.toOption,Pointer.new,GlobalRelocationConversion.zero_word,pointer,encoding,provenanceResult,encodedSize,Size.ZERO,Size.ofBytes,
    bind,Bind.bind,pure,Pure.pure,Except.pure,Id.run,List.forIn_cons,List.forIn_nil]
  refine ⟨?_,provenancePtrs,provenanceFragments⟩
  constructor <;> first | rfl | exact encodedSize

end DuplicatePrefix.GlobalStaticRelocationConversion
