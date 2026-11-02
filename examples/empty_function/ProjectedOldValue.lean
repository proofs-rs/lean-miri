import empty_function.ProjectedScalarWrite
namespace EmptyFunction.ProjectedOldValue
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Actual source old-value writer for initialized enclosing immediates. Its
inputs describe the freshly created stack backing and the old scalar/pair
encoding; the actual memory write and storage image are conclusions. -/
theorem write (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (state : State) (id : AllocId) (tag : BorTag) (base : UInt64) (layout : LocalLayout)
    (bytes : Allocation Provenance Unit) (value : Immediate Provenance) (initialized : value ≠ .uninit)
    (older : Array (AllocId × InputDraft.Entry))
    (encoding : InputDraft.ImmediateEncoding s.prepared.compiler.runtime.target layout value)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok bytes)
    (size : bytes.byteSize = layout.layout.size) (mutable : bytes.mutability = .Mut)
    (sized : layout.layout.isSized = true) (signed : layout.layout.size.bytes.toNat < 2^63)
    (liveShape : state.machine.memory.live = older.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag layout.layout.size)⟩))
    (fresh : older.find? (fun row => row.1 == id) = none)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noClocks : state.machine.dataRace = none)
    (extra : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow) :
    ∃ after,
      (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler).writeMemoryNoValidate () value
        ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ state =
        .ok () {state with machine := {state.machine with memory := {state.machine.memory with live := older.push (id,⟨.stack,after⟩)}}} ∧
      after.byteSize = layout.layout.size ∧ after.len = bytes.len ∧ after.mutability = .Mut ∧ after.align = bytes.align ∧
      after.extra = BorrowTree.new tag layout.layout.size ∧ after.nativeBuffer = bytes.nativeBuffer ∧
      ∃ expected, Preservation.expectedImage s.prepared.compiler.runtime.target.base layout value = some expected ∧
        Preservation.StorageImage expected after := by
  have storage := (Allocation.tryNew_uninit_image layout.layout.size layout.layout.align.abi (Size.ofBytes 1) bytes (by decide) created).1
  have scopedEq : (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler).writeMemoryNoValidate () value
      ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ state =
      PlaceMachine.writeMemory {s.cfg.access with ghostMode := false} (fun _ => true) value
        ⟨⟨Pointer.new (some (.concrete id tag)) (Size.ofBytes base),.none,none⟩,layout⟩ state := by
    simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      ValidityMachine.scopedAccess,ValidityMachine.validationInProgress,ValidityMachine.enforceValidity,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,ghost,shallow]
    rfl
  simp only [scopedEq]
  cases value with
  | uninit => exact False.elim (initialized rfl)
  | scalar value =>
    have shape : ∃ abi, layout.layout.backendRepr = .Scalar abi ∧
        InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abi.primitive value ∧
        value.size.bytes ≤ layout.layout.size.bytes := by
      cases representation : layout.layout.backendRepr <;> simp_all [InputDraft.ImmediateEncoding]
    obtain ⟨abi,representation,encoded,bound⟩ := shape
    exact ProjectedScalarWrite.write_scalar s metadata capacity state id tag base layout abi bytes value older
      representation encoded created size storage mutable bound sized signed liveShape fresh cached backend noClocks extra
  | scalarPair first second =>
    have shape : ∃ abiA abiB offset, layout.layout.backendRepr = .ScalarPair (a := abiA) (b := abiB) (bOffset := offset) ∧
        InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abiA.primitive first ∧
        InputDraft.ScalarEncoding s.prepared.compiler.runtime.target abiB.primitive second ∧
        offset.bytes ≠ 0 ∧ first.size.bytes ≤ offset.bytes ∧
        offset.bytes.toNat + second.size.bytes.toNat ≤ layout.layout.size.bytes.toNat := by
      cases representation : layout.layout.backendRepr <;> simp_all [InputDraft.ImmediateEncoding]
      rename_i abiA abiB offset
      exact ⟨abiA,abiB,offset,⟨rfl,rfl,rfl⟩,encoding⟩
    obtain ⟨abiA,abiB,offset,representation,encodedA,encodedB,offsetPositive,firstEnd,bound⟩ := shape
    exact ProjectedScalarWrite.write_pair s metadata capacity state id tag base layout abiA abiB offset bytes first second older
      representation encodedA encodedB created size storage mutable offsetPositive firstEnd bound sized signed liveShape fresh cached backend noClocks extra
end EmptyFunction.ProjectedOldValue
