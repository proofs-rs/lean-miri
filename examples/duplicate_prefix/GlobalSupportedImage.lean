import duplicate_prefix.GlobalDataOnlyActualBytes
import duplicate_prefix.GlobalRelocationFiniteConversion

/-! Structural image support for lazy compiler memory, including arbitrary
finite ordered nonoverlapping relocation lists. Each arbitrary eight-byte word
is decoded with the actual target endian; cached memory or non-TLS/non-extern
static targets use actual wrapping pointer arithmetic. Byte fragments and
static source initializer evaluation remain outside this boundary. Clients
require only representation-independent allocation attributes. -/
namespace DuplicatePrefix.GlobalSupportedImage
open Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def Supported {K : Type} (source : Allocation CtfeProvenance Unit) (runtime : RuntimeTargetDataLayout)
    (memory : MemoryState Provenance BorrowTree K) (rootTags : Array (AllocId × BorTag))
    (addresses : Array AllocAddresses.BaseAddressEntry) : Prop :=
  source.provenanceMap = ProvenanceMap.new ∨
  (∃ (provenance : CtfeProvenance) (target : Allocation CtfeProvenance Unit) (base : UInt64) (root : BorTag),
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    AllocationCopy.snapshot source = #[0,0,0,0,0,0,0,0] ∧
    source.provenanceMap.ptrs = #[(Size.ZERO,provenance)] ∧ source.provenanceMap.byteFragments = none ∧
    memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,target.byteSize,target.align,target.mutability,some (.memory target)⟩ ∧
    (rootTags.find? (fun row => row.1 == provenance.allocId)).map Prod.snd = some root ∧
    addresses.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
  (∃ (provenance : CtfeProvenance) (definition : Nat) (targetSize : Size) (targetAlign : Align)
    (targetMutability : Mutability) (base : UInt64) (root : BorTag),
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    AllocationCopy.snapshot source = #[0,0,0,0,0,0,0,0] ∧
    source.provenanceMap.ptrs = #[(Size.ZERO,provenance)] ∧ source.provenanceMap.byteFragments = none ∧
    memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.static,targetSize,targetAlign,targetMutability,some (.static definition true false false)⟩ ∧
    (rootTags.find? (fun row => row.1 == provenance.allocId)).map Prod.snd = some root ∧
    addresses.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
  (∃ (provenance : CtfeProvenance) (position : Size) (base : UInt64) (root : BorTag),
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    (AllocationCopy.snapshot source).extract position.bytes.toNat (position.bytes.toNat+8) = #[0,0,0,0,0,0,0,0] ∧
    position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size ∧
    source.provenanceMap.ptrs = #[(position,provenance)] ∧ source.provenanceMap.byteFragments = none ∧
    GlobalRelocationWindowConversion.KnownTarget memory provenance ∧
    (rootTags.find? (fun row => row.1 == provenance.allocId)).map Prod.snd = some root ∧
    addresses.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
  (∃ (provenance : CtfeProvenance) (position : Size) (word : Fin 8 → UInt8) (base : UInt64) (root : BorTag),
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    (AllocationCopy.snapshot source).extract position.bytes.toNat (position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes word ∧
    position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size ∧
    source.provenanceMap.ptrs = #[(position,provenance)] ∧ source.provenanceMap.byteFragments = none ∧
    GlobalRelocationWindowConversion.KnownTarget memory provenance ∧
    (rootTags.find? (fun row => row.1 == provenance.allocId)).map Prod.snd = some root ∧
    addresses.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
  (∃ rows : Fin 2 → GlobalRelocationTwoWords.Row,
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    (∀ i, (AllocationCopy.snapshot source).extract (rows i).position.bytes.toNat
      ((rows i).position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes (rows i).word) ∧
    (rows 0).position.bytes.toNat+8 ≤ (rows 1).position.bytes.toNat ∧
    (rows 1).position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size ∧
    source.provenanceMap.ptrs = #[((rows 0).position,(rows 0).provenance),((rows 1).position,(rows 1).provenance)] ∧
    source.provenanceMap.byteFragments = none ∧
    (∀ i, GlobalRelocationWindowConversion.KnownTarget memory (rows i).provenance ∧
      (rootTags.find? (fun row => row.1 == (rows i).provenance.allocId)).map Prod.snd = some (rows i).root ∧
      addresses.find? (fun row => row.allocId == (rows i).provenance.allocId) = some ⟨(rows i).provenance.allocId,(rows i).base⟩)) ∨
  ∃ rows : List GlobalRelocationFiniteLoop.Row,
    runtime.base.pointerWidth = .w64 ∧ runtime.pointerSize = Size.ofBytes 8 ∧
    rows.Pairwise GlobalRelocationFiniteLoop.Separate ∧
    (∀ row ∈ rows, (AllocationCopy.snapshot source).extract row.position.bytes.toNat
      (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word) ∧
    (∀ row ∈ rows, row.position.bytes.toNat+8 ≤ (AllocationCopy.snapshot source).size) ∧
    source.provenanceMap.ptrs = (rows.map GlobalRelocationFiniteLoop.input).toArray ∧
    source.provenanceMap.byteFragments = none ∧
    (∀ row ∈ rows, GlobalRelocationWindowConversion.KnownTarget memory row.provenance ∧
      (rootTags.find? (fun entry => entry.1 == row.provenance.allocId)).map Prod.snd = some row.root ∧
      addresses.find? (fun entry => entry.allocId == row.provenance.allocId) = some ⟨row.provenance.allocId,row.base⟩)

theorem adjust_exists {Os R P H D O Aff B Host C : Type}
    (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalPointerSource.User Os R P H D O Aff B Host) P)
    (sourceLeaves : EvalPointerSource.Leaves Os R P H D O Aff B Host C)
    (choice : C)
    (before : EvalPointerSource.Machine Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (managed : (sourceLeaves.nativeLibraryPaths before.user.payload.payload.user.host).isEmpty = true)
    (supported : Supported source compiler.runtime.target before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? id = some root) (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == id)) = false) :
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      GlobalAllocationMachine.adjust compiler.runtime.target.base extras
        (GlobalDataOnlyActualBytes.leaves compiler image sourceLeaves
          (EvalPointerSource.address compiler image sourceLeaves choice)
          (EvalPointerSource.make compiler image extras sourceLeaves choice).rootPointer) id source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))
          (MemoryExtras.putAllocation extras before id ⟨none,#[]⟩) := by
  let pointers := EvalPointerSource.make compiler image extras sourceLeaves choice
  let address := EvalPointerSource.address compiler image sourceLeaves choice
  have conversion : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      Allocation.adjustFromTcx source compiler.runtime.target.base
        (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointers.rootPointer before = .ok converted before := by
    rcases supported with empty | ⟨provenance,target,base,targetRoot,width,pointerSize,raw,relocation,noFragments,descriptor,cachedRoot,cachedAddress⟩ | ⟨provenance,definition,targetSize,targetAlign,targetMutability,base,targetRoot,width,pointerSize,raw,relocation,noFragments,descriptor,cachedRoot,cachedAddress⟩ | ⟨provenance,position,base,targetRoot,width,pointerSize,window,bounds,relocation,noFragments,target,cachedRoot,cachedAddress⟩ | ⟨provenance,position,word,base,targetRoot,width,pointerSize,window,bounds,relocation,noFragments,target,cachedRoot,cachedAddress⟩ | ⟨rows,width,pointerSize,windows,separate,bounds,relocations,noFragments,known⟩ | ⟨rows,width,pointerSize,separate,windows,bounds,relocations,noFragments,known⟩
    · obtain ⟨converted,convertedEq,facts⟩ := GlobalDataOnlyConversion.adjust_exists source compiler.runtime.target.base
        pointers.rootPointer before empty
      exact ⟨converted,⟨facts.size,facts.storage,facts.mask,facts.align,facts.mutability,facts.native⟩,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,encoded,convertedEq,facts,_,_,_,_,_⟩ := GlobalRelocationConversion.singleton_zero
        EvalPointerSource.tape address externStatic before tracker provenance base targetRoot target source
        compiler.runtime.target.base descriptor enabled cachedRoot cachedAddress arithmetic width raw relocation noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,encoded,convertedEq,facts,_,_,_,_,_⟩ := GlobalStaticRelocationConversion.singleton_zero
        EvalPointerSource.tape address externStatic before tracker provenance base targetRoot definition targetSize targetAlign targetMutability source
        compiler.runtime.target.base descriptor enabled cachedRoot cachedAddress arithmetic width raw relocation noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,convertedEq,facts,_,_⟩ := GlobalRelocationWindowConversion.singleton
        EvalPointerSource.tape address externStatic before tracker provenance base targetRoot source
        compiler.runtime.target.base position target enabled cachedRoot cachedAddress arithmetic width window bounds relocation noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,convertedEq,facts,_,_⟩ := GlobalRelocationWordConversion.singleton
        EvalPointerSource.tape address externStatic before tracker provenance base targetRoot source
        compiler.runtime.target.base position word target enabled cachedRoot cachedAddress arithmetic width window bounds relocation noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,convertedEq,facts,_,_⟩ := GlobalRelocationTwoWords.two
        EvalPointerSource.tape address externStatic before tracker rows source compiler.runtime.target.base
        known enabled arithmetic width windows separate bounds relocations noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
    · have rootSource : ∃ externStatic : Miri.MIR.DefId → EvalPointerSource.M Os R P H D O Aff B Host (Pointer Provenance),
          pointers.rootPointer = PointerSource.globalRootPointer EvalPointerSource.tape address externStatic := by
        exact ⟨_,rfl⟩
      obtain ⟨externStatic,rootSource⟩ := rootSource
      have arithmetic : address.arithmetic = ⟨Size.ofBytes 8⟩ := by
        simpa only [address,EvalPointerSource.address,PointerSource.addressHooks] using
          congrArg (fun size => (⟨size⟩ : Miri.Memory.PointerArithmetic)) pointerSize
      obtain ⟨converted,convertedEq,facts,_,_⟩ := GlobalRelocationFiniteConversion.convert
        EvalPointerSource.tape address externStatic before tracker source compiler.runtime.target.base rows
        known enabled arithmetic width separate windows bounds relocations noFragments
      rw [←rootSource] at convertedEq
      exact ⟨converted,facts,convertedEq⟩
  obtain ⟨converted,facts,conversion⟩ := conversion
  refine ⟨converted,facts,?_⟩
  dsimp only [pointers] at conversion
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len = .ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
      pure,Pure.pure,Except.pure,Except.toOption]
  have init := GlobalDataOnlyExtra.init_extra extras before tracker id root source.byteSize source.align
    enabled rootCached race noExtras
  simp only [GlobalAllocationMachine.adjust,GlobalDataOnlyActualBytes.leaves,EvalPointerSource.bytes,managed,
    inspect,conversion,facts.size,facts.align,GlobalAllocationMachine.init,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,ite_true]
  simp only [pure,Pure.pure] at init
  rw [init]
end DuplicatePrefix.GlobalSupportedImage

open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GlobalSupportedImage.adjust_exists) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved supported compiler image dependency {dependency}"
