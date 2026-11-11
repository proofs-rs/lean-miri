import empty_function.ProjectedOldWrite
import empty_function.ProjectedImage
namespace EmptyFunction.ProjectedScalarWrite
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

 theorem scalar_facts (target : TargetDataLayout) (value : Memory.Scalar Provenance)
    (width : target.pointerWidth = .w64) (raw : InputDraft.RawCanonicalScalar target value) :
    ∃ converted, value.toBitsOrPtrInternal value.size = .ok converted ∧
      value.size.bytes ≠ 0 ∧ value.size.bytes.toNat ≤ 16 ∧
      (match converted with | .bits _ => True | .pointer _ => value.size = Size.fromBits target.pointerWidth.bits) := by
  cases raw with
  | integer payload encoding nonzero limited truncated =>
    subst value
    refine ⟨.bits payload.toBitsUnchecked,?_,?_,?_,True.intro⟩
    · with_unfolding_all
        simp [Scalar.toBitsOrPtrInternal,Scalar.fromScalarInt,Memory.Scalar.size,ScalarInt.size,ScalarInt.toBits,
          ScalarInt.toBitsUnchecked,Except.mapError,pure,Pure.pure,Except.pure,bind,Bind.bind,Except.bind]
    · exact nonzero
    · exact limited
  | pointer pointer encoding =>
    subst value
    refine ⟨.pointer pointer,?_,?_,?_,rfl⟩
    · with_unfolding_all
        simp [Scalar.toBitsOrPtrInternal,Scalar.fromPointer,Memory.Scalar.size,ScalarInt.size,pure,Pure.pure,Except.pure]
    · change (Size.fromBits target.pointerWidth.bits).bytes ≠ 0
      rw [width]
      decide
    · change (Size.fromBits target.pointerWidth.bits).bytes.toNat ≤ 16
      rw [width]
      decide

theorem scalar_created (runtime : RuntimeTargetDataLayout) (layout : LocalLayout)
    (bytes : Allocation Provenance Unit) (tree : BorrowTree) (value : Memory.Scalar Provenance)
    (target : runtime.base.pointerWidth = .w64) (raw : InputDraft.RawCanonicalScalar runtime.base value)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok bytes)
    (size : bytes.byteSize = layout.layout.size) (storage : bytes.len = layout.layout.size.bytes.toNat)
    (mutable : bytes.mutability = .Mut) (bound : value.size.bytes.toNat ≤ layout.layout.size.bytes.toNat) :
    ∃ after, Allocation.writeScalar runtime.base (allocRange Size.ZERO value.size) value (bytes.withExtra tree) = .ok () after ∧
      after.byteSize = layout.layout.size ∧ after.len = bytes.len ∧ after.mutability = .Mut ∧
      after.align = bytes.align ∧ after.extra = tree ∧ after.nativeBuffer = bytes.nativeBuffer ∧
      ∃ expected, Preservation.expectedImage runtime.base layout (.scalar value) = some expected ∧
        Preservation.StorageImage expected after := by
  obtain ⟨converted,conversion,nonzero,width,pointerWidth⟩ := scalar_facts runtime.base value target raw
  have shape := Allocation.tryNew_uninit_shape layout.layout.size layout.layout.align.abi bytes created
  have maskLength : (bytes.withExtra tree).initializationMask.len = (bytes.withExtra tree).byteSize := by
    change bytes.initializationMask.len = bytes.byteSize
    rw [shape.2,size]
    rfl
  have maskValid : InitMask.WriteProof.WellFormed (bytes.withExtra tree).initializationMask := by
    change InitMask.WriteProof.WellFormed bytes.initializationMask
    rw [shape.2]
    trivial
  obtain ⟨after,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,_,_,_⟩ :=
    Allocation.writeScalar_fresh_zero runtime.base (bytes.withExtra tree) value converted
      (by change bytes.len = bytes.byteSize.bytes.toNat; rw [size]; exact storage)
      mutable maskLength maskValid shape.1 nonzero width (by change value.size.bytes.toNat ≤ bytes.byteSize.bytes.toNat; rw [size]; exact bound)
      target (by cases converted <;> simpa only [] using pointerWidth) conversion
  have erased : (bytes.withExtra tree).mapExtra (fun _ => ()) = bytes := by cases bytes; rfl
  have pureWrite := Allocation.writeScalar_mapExtra runtime.base (allocRange Size.ZERO value.size) value
    (bytes.withExtra tree) (fun _ => ())
  rw [erased,written] at pureWrite
  have parentPositive : layout.layout.size.bytes ≠ 0 := by
    intro zero
    have valueZero : value.size.bytes.toNat = 0 := by simpa [zero] using Nat.le_zero.mp (by simpa [zero] using bound)
    exact nonzero (UInt64.toNat_inj.mp valueZero)
  have pointerPositive : (Size.fromBits runtime.base.pointerWidth.bits).bytes ≠ 0 := by rw [target]; decide
  obtain ⟨_,initialized,fromBytes,uninitialized⟩ := Allocation.tryNew_uninit_image layout.layout.size layout.layout.align.abi
    (Size.fromBits runtime.base.pointerWidth.bits) bytes pointerPositive created
  simp only [parentPositive,↓reduceIte] at uninitialized
  have image : Preservation.expectedImage runtime.base layout (.scalar value) = some (after.mapExtra (fun _ => ())) := by
    unfold Preservation.expectedImage
    rw [fromBytes]
    simp only [Except.toOption,bind,Bind.bind,Option.bind,pure,Pure.pure]
    rw [uninitialized]
    change (match Allocation.writeScalar runtime.base (allocRange Size.ZERO value.size) value bytes with
      | .ok _ final => some final | .error _ _ => none) = _
    rw [pureWrite]
  refine ⟨after,written,sizeEq.trans size,lenEq,mutEq.trans mutable,alignEq,extraEq,nativeEq,
    after.mapExtra (fun _ => ()),image,ProjectedImage.storageImage_of_erased _ _ rfl⟩

theorem pair_created (runtime : RuntimeTargetDataLayout) (layout : LocalLayout)
    (bytes : Allocation Provenance Unit) (tree : BorrowTree) (first second : Memory.Scalar Provenance)
    (abiA abiB : Miri.ABI.Scalar) (offset : Size)
    (backend : layout.layout.backendRepr = .ScalarPair (a := abiA) (b := abiB) (bOffset := offset))
    (target : runtime.base.pointerWidth = .w64)
    (rawA : InputDraft.RawCanonicalScalar runtime.base first) (rawB : InputDraft.RawCanonicalScalar runtime.base second)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok bytes)
    (size : bytes.byteSize = layout.layout.size) (storage : bytes.len = layout.layout.size.bytes.toNat)
    (mutable : bytes.mutability = .Mut) (firstEnd : first.size.bytes ≤ offset.bytes)
    (bound : offset.bytes.toNat+second.size.bytes.toNat ≤ layout.layout.size.bytes.toNat) :
    ∃ middle after,
      Allocation.writeScalar runtime.base (allocRange Size.ZERO first.size) first (bytes.withExtra tree) = .ok () middle ∧
      Allocation.writeScalar runtime.base (allocRange offset second.size) second middle = .ok () after ∧
      after.byteSize = layout.layout.size ∧ after.len = bytes.len ∧ after.mutability = .Mut ∧
      after.align = bytes.align ∧ after.extra = tree ∧ after.nativeBuffer = bytes.nativeBuffer ∧
      ∃ expected, Preservation.expectedImage runtime.base layout (.scalarPair first second) = some expected ∧
        Preservation.StorageImage expected after := by
  obtain ⟨convertedA,conversionA,nonzeroA,widthA,pointerA⟩ := scalar_facts runtime.base first target rawA
  obtain ⟨convertedB,conversionB,nonzeroB,widthB,pointerB⟩ := scalar_facts runtime.base second target rawB
  have shape := Allocation.tryNew_uninit_shape layout.layout.size layout.layout.align.abi bytes created
  have maskLength : (bytes.withExtra tree).initializationMask.len = (bytes.withExtra tree).byteSize := by
    change bytes.initializationMask.len = bytes.byteSize
    rw [shape.2,size]; rfl
  have maskValid : InitMask.WriteProof.WellFormed (bytes.withExtra tree).initializationMask := by
    change InitMask.WriteProof.WellFormed bytes.initializationMask
    rw [shape.2]; trivial
  have firstNat : first.size.bytes.toNat ≤ offset.bytes.toNat := UInt64.le_iff_toNat_le.mp firstEnd
  obtain ⟨middle,writtenA,sizeA,lenA,mutA,alignA,extraA,nativeA,maskA,validA,provenanceA⟩ :=
    Allocation.writeScalar_fresh_zero runtime.base (bytes.withExtra tree) first convertedA
      (by change bytes.len = bytes.byteSize.bytes.toNat; rw [size]; exact storage)
      mutable maskLength maskValid shape.1 nonzeroA widthA
      (by change first.size.bytes.toNat ≤ bytes.byteSize.bytes.toNat; rw [size]; omega)
      target (by cases convertedA <;> simpa only [] using pointerA) conversionA
  have middleStorage : middle.len = middle.byteSize.bytes.toNat := by
    rw [lenA,sizeA]
    change bytes.len = bytes.byteSize.bytes.toNat
    rw [size]; exact storage
  have middleMask : middle.initializationMask.len = middle.byteSize := by rw [maskA,maskLength,sizeA]
  obtain ⟨after,writtenB,sizeB,lenB,mutB,alignB,extraB,nativeB,_,_⟩ :=
    Allocation.writeScalar_separated runtime.base middle offset second convertedB middleStorage (mutA.trans mutable)
      middleMask validA
      (by rcases provenanceA with empty | ⟨firstPointer,old,present⟩
          · exact Or.inl empty
          · refine Or.inr ⟨old,present,?_⟩
            rw [←firstPointer]
            exact firstNat)
      nonzeroB widthB (by rw [sizeA]; change _ ≤ bytes.byteSize.bytes.toNat; rw [size]; exact bound)
      target (by cases convertedB <;> simpa only [] using pointerB) conversionB
  have erased : (bytes.withExtra tree).mapExtra (fun _ => ()) = bytes := by cases bytes; rfl
  have pureA := Allocation.writeScalar_mapExtra runtime.base (allocRange Size.ZERO first.size) first (bytes.withExtra tree) (fun _ => ())
  rw [erased,writtenA] at pureA
  have pureB := Allocation.writeScalar_mapExtra runtime.base (allocRange offset second.size) second middle (fun _ => ())
  rw [writtenB] at pureB
  have parentPositive : layout.layout.size.bytes ≠ 0 := by
    intro zero
    have secondZero : second.size.bytes.toNat = 0 := by have b := bound; simp only [zero,UInt64.toNat_zero] at b; omega
    exact nonzeroB (UInt64.toNat_inj.mp secondZero)
  have pointerPositive : (Size.fromBits runtime.base.pointerWidth.bits).bytes ≠ 0 := by rw [target]; decide
  obtain ⟨_,initialized,fromBytes,uninitialized⟩ := Allocation.tryNew_uninit_image layout.layout.size layout.layout.align.abi
    (Size.fromBits runtime.base.pointerWidth.bits) bytes pointerPositive created
  simp only [parentPositive,↓reduceIte] at uninitialized
  have image : Preservation.expectedImage runtime.base layout (.scalarPair first second) = some (after.mapExtra (fun _ => ())) := by
    unfold Preservation.expectedImage
    rw [fromBytes]
    simp only [Except.toOption,bind,Bind.bind,Option.bind,pure,Pure.pure]
    rw [uninitialized]
    simp only [backend]
    change ((match Allocation.writeScalar runtime.base (allocRange Size.ZERO first.size) first bytes with
      | .ok _ stored => some stored | .error _ _ => none).bind fun stored =>
        match Allocation.writeScalar runtime.base (allocRange offset second.size) second stored with
        | .ok _ final => some final | .error _ _ => none) = _
    rw [pureA]
    simp only [Option.bind_some]
    rw [pureB]
  exact ⟨middle,after,writtenA,writtenB,sizeB.trans (sizeA.trans size),lenB.trans lenA,
    mutB.trans (mutA.trans mutable),alignB.trans alignA,extraB.trans extraA,nativeB.trans nativeA,
    after.mapExtra (fun _ => ()),image,ProjectedImage.storageImage_of_erased _ _ rfl⟩

private theorem filter_absent (older : Array (AllocId × InputDraft.Entry)) (id : AllocId)
    (fresh : older.find? (fun row => row.1 == id) = none) :
    older.filter (fun row => row.1 != id) = older := by
  apply Array.filter_eq_self.mpr
  intro row member
  have missing := Array.find?_eq_none.mp fresh row member
  simpa only [bne_iff_ne,beq_iff_eq] using missing

 theorem write_scalar (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (id : AllocId) (tag : BorTag) (base : UInt64) (layout : LocalLayout)
    (abi : Miri.ABI.Scalar) (bytes : Allocation Provenance Unit) (value : Memory.Scalar Provenance)
    (older : Array (AllocId × InputDraft.Entry))
    (backendLayout : layout.layout.backendRepr = .Scalar abi)
    (encoding : InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abi.primitive value)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok bytes)
    (size : bytes.byteSize = layout.layout.size) (storage : bytes.len = layout.layout.size.bytes.toNat)
    (mutable : bytes.mutability = .Mut) (valueBound : value.size.bytes ≤ layout.layout.size.bytes)
    (sized : layout.layout.isSized = true) (signed : layout.layout.size.bytes.toNat < 2^63)
    (liveShape : state.machine.memory.live = older.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag layout.layout.size)⟩))
    (fresh : older.find? (fun row => row.1 == id) = none)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noClocks : state.machine.dataRace = none)
    (extra : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id,{weakMemory := none})) :
    ∃ after,
      PlaceMachine.writeMemory {s.cfg.access with ghostMode := false} (fun _ => true) (.scalar value)
        ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ state =
        .ok () {state with machine := {state.machine with memory := {state.machine.memory with live := older.push (id,⟨.stack,after⟩)}}} ∧
      after.byteSize = layout.layout.size ∧ after.len = bytes.len ∧ after.mutability = .Mut ∧
      after.align = bytes.align ∧ after.extra = BorrowTree.new tag layout.layout.size ∧ after.nativeBuffer = bytes.nativeBuffer ∧
      ∃ expected, Preservation.expectedImage s.prepared.compiler.runtime.target.base layout (.scalar value) = some expected ∧
        Preservation.StorageImage expected after := by
  rcases encoding with ⟨raw,primitiveSize,primitive,sizeValue,category⟩
  obtain ⟨after,written,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,image⟩ := scalar_created
    s.prepared.compiler.runtime.target layout bytes (BorrowTree.new tag layout.layout.size) value metadata.target raw
    created size storage mutable (UInt64.le_iff_toNat_le.mp valueBound)
  have positiveValue : value.size.bytes ≠ 0 := (scalar_facts _ _ metadata.target raw).choose_spec.2.1
  have positive : layout.layout.size.bytes ≠ 0 := by
    intro zero
    have valueZero : value.size.bytes.toNat = 0 := by have b := UInt64.le_iff_toNat_le.mp valueBound; simp only [zero,UInt64.toNat_zero] at b; omega
    exact positiveValue (UInt64.toNat_inj.mp valueZero)
  let entry : InputDraft.Entry := ⟨.stack,bytes.withExtra (BorrowTree.new tag layout.layout.size)⟩
  have live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    rw [liveShape]
    simp [Array.find?_push,fresh,entry]
  have filtered := filter_absent older id fresh
  have last : (state.machine.memory.live.filter (fun row => row.1 != id)).push (id,entry) = state.machine.memory.live := by
    rw [liveShape]
    simp [Array.filter_push,filtered,entry]
  have accessed := ProjectedOldWrite.get_place s metadata capacity state.machine id tag layout base entry live rfl
    size mutable sized positive signed cached last backend noClocks extra
  let memory := {state.machine.memory with live := older.push (id,⟨.stack,after⟩)}
  have committed : state.machine.memory.setLiveAllocation id after = .ok memory := by
    rw [MemoryState.setLiveAllocation_of_find state.machine.memory id entry after live]
    simp [memory,liveShape,Array.filter_push,filtered,entry]
  have width : Primitive.size abi.primitive s.cfg.access.runtime = .ok value.size := by
    rw [(MetadataBinding.fields s metadata capacity).runtime,sizeValue]
    exact primitive
  have operand := writeImmediate_scalar_of_access state.machine.memory memory
    (⟨state.machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
    (⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,localMemoryLayout layout⟩ : MemoryOperandPlace Provenance)
    s.cfg.access.runtime s.cfg.access.globalKind s.cfg.access.globalHooks (PlaceMachine.accessHooks s.cfg.access) s.cfg.access.dynamicLayout
    (fun _ => true) value abi id (bytes.withExtra (BorrowTree.new tag layout.layout.size)) after backendLayout width category
    valueBound accessed (by rw [(MetadataBinding.fields s metadata capacity).runtime]; exact written) committed
  have result := PlaceMachine.writeMemory_of_result {s.cfg.access with ghostMode := false} (fun _ => true) (.scalar value)
    (⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ : MPlaceTy Provenance)
    state memory _ (MetadataBinding.fields s metadata capacity).retainTouched operand
  exact ⟨after,result,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,image⟩

theorem write_pair (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (id : AllocId) (tag : BorTag) (base : UInt64) (layout : LocalLayout)
    (abiA abiB : Miri.ABI.Scalar) (offset : Size) (bytes : Allocation Provenance Unit)
    (first second : Memory.Scalar Provenance) (older : Array (AllocId × InputDraft.Entry))
    (backendLayout : layout.layout.backendRepr = .ScalarPair (a := abiA) (b := abiB) (bOffset := offset))
    (encodingA : InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abiA.primitive first)
    (encodingB : InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abiB.primitive second)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok bytes)
    (size : bytes.byteSize = layout.layout.size) (storage : bytes.len = layout.layout.size.bytes.toNat)
    (mutable : bytes.mutability = .Mut) (offsetPositive : offset.bytes ≠ 0) (firstEnd : first.size.bytes ≤ offset.bytes)
    (bound : offset.bytes.toNat+second.size.bytes.toNat ≤ layout.layout.size.bytes.toNat)
    (sized : layout.layout.isSized = true) (signed : layout.layout.size.bytes.toNat < 2^63)
    (liveShape : state.machine.memory.live = older.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag layout.layout.size)⟩))
    (fresh : older.find? (fun row => row.1 == id) = none)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noClocks : state.machine.dataRace = none)
    (extra : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id,{weakMemory := none})) :
    ∃ after,
      PlaceMachine.writeMemory {s.cfg.access with ghostMode := false} (fun _ => true) (.scalarPair first second)
        ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ state =
        .ok () {state with machine := {state.machine with memory := {state.machine.memory with live := older.push (id,⟨.stack,after⟩)}}} ∧
      after.byteSize = layout.layout.size ∧ after.len = bytes.len ∧ after.mutability = .Mut ∧
      after.align = bytes.align ∧ after.extra = BorrowTree.new tag layout.layout.size ∧ after.nativeBuffer = bytes.nativeBuffer ∧
      ∃ expected, Preservation.expectedImage s.prepared.compiler.runtime.target.base layout (.scalarPair first second) = some expected ∧
        Preservation.StorageImage expected after := by
  rcases encodingA with ⟨rawA,primitiveSizeA,primitiveA,sizeValueA,categoryA⟩
  rcases encodingB with ⟨rawB,primitiveSizeB,primitiveB,sizeValueB,categoryB⟩
  obtain ⟨middle,after,writtenA,writtenB,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,image⟩ := pair_created
    s.prepared.compiler.runtime.target layout bytes (BorrowTree.new tag layout.layout.size) first second abiA abiB offset
    backendLayout metadata.target rawA rawB created size storage mutable firstEnd bound
  have positiveValue : second.size.bytes ≠ 0 := (scalar_facts _ _ metadata.target rawB).choose_spec.2.1
  have positive : layout.layout.size.bytes ≠ 0 := by
    intro zero
    have secondZero : second.size.bytes.toNat = 0 := by have b := bound; simp only [zero,UInt64.toNat_zero] at b; omega
    exact positiveValue (UInt64.toNat_inj.mp secondZero)
  let entry : InputDraft.Entry := ⟨.stack,bytes.withExtra (BorrowTree.new tag layout.layout.size)⟩
  have live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    rw [liveShape]; simp [Array.find?_push,fresh,entry]
  have filtered := filter_absent older id fresh
  have last : (state.machine.memory.live.filter (fun row => row.1 != id)).push (id,entry) = state.machine.memory.live := by
    rw [liveShape]; simp [Array.filter_push,filtered,entry]
  have accessed := ProjectedOldWrite.get_place s metadata capacity state.machine id tag layout base entry live rfl
    size mutable sized positive signed cached last backend noClocks extra
  let middleMemory := {state.machine.memory with live := older.push (id,⟨.stack,middle⟩)}
  let memory := {state.machine.memory with live := older.push (id,⟨.stack,after⟩)}
  have cacheA : state.machine.memory.setLiveAllocation id middle = .ok middleMemory := by
    rw [MemoryState.setLiveAllocation_of_find state.machine.memory id entry middle live]
    simp [middleMemory,liveShape,Array.filter_push,filtered,entry]
  have liveMiddle : middleMemory.live.find? (fun row => row.1 == id) = some (id,⟨.stack,middle⟩) := by
    simp [middleMemory,Array.find?_push,fresh]
  have cacheB : middleMemory.setLiveAllocation id after = .ok memory := by
    rw [MemoryState.setLiveAllocation_of_find middleMemory id ⟨.stack,middle⟩ after liveMiddle]
    simp [middleMemory,memory,Array.filter_push,filtered]
  have widthA : Primitive.size abiA.primitive s.cfg.access.runtime = .ok first.size := by
    rw [(MetadataBinding.fields s metadata capacity).runtime,sizeValueA]; exact primitiveA
  have widthB : Primitive.size abiB.primitive s.cfg.access.runtime = .ok second.size := by
    rw [(MetadataBinding.fields s metadata capacity).runtime,sizeValueB]; exact primitiveB
  have operand := writeImmediate_pair_of_access state.machine.memory middleMemory memory
    (⟨state.machine,none⟩ : PlaceMachine.AccessState MiriMemoryKind RootUser)
    (⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,localMemoryLayout layout⟩ : MemoryOperandPlace Provenance)
    s.cfg.access.runtime s.cfg.access.globalKind s.cfg.access.globalHooks (PlaceMachine.accessHooks s.cfg.access) s.cfg.access.dynamicLayout
    first second abiA abiB offset id (bytes.withExtra (BorrowTree.new tag layout.layout.size)) middle after backendLayout
    widthA widthB categoryA categoryB offsetPositive firstEnd bound accessed
    (by rw [(MetadataBinding.fields s metadata capacity).runtime]; exact writtenA) cacheA
    (by rw [(MetadataBinding.fields s metadata capacity).runtime]; exact writtenB) cacheB
  have result := PlaceMachine.writeMemory_of_result {s.cfg.access with ghostMode := false} (fun _ => true) (.scalarPair first second)
    (⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ : MPlaceTy Provenance)
    state memory _ (MetadataBinding.fields s metadata capacity).retainTouched operand
  exact ⟨after,result,sizeEq,lenEq,mutEq,alignEq,extraEq,nativeEq,image⟩

end EmptyFunction.ProjectedScalarWrite
