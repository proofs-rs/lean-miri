import empty_function.Preservation
namespace EmptyFunction.ProjectedImage
open Miri Miri.Memory Miri.Interpreter Miri.ABI
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {P E E' : Type}

def mapResult (f : E → E') (result : EStateM.Result AllocError (Allocation P E) Unit) :
    EStateM.Result AllocError (Allocation P E') Unit :=
  match result with
  | .ok value state => .ok value (state.mapExtra f)
  | .error error state => .error error (state.mapExtra f)

theorem storageImage_of_erased (actual : Allocation Provenance TreeBorrows.BorrowTree)
    (expected : Allocation Provenance Unit)
    (same : actual.mapExtra (fun _ => ()) = expected) :
    EmptyFunction.Preservation.StorageImage expected actual := by
  subst expected
  unfold EmptyFunction.Preservation.StorageImage
  refine ⟨rfl,rfl,?_⟩
  intro byte bound
  exact ⟨rfl,fun _ => rfl⟩

abbrev writeScalar_mapExtra := @Allocation.writeScalar_mapExtra
abbrev writeUninit_mapExtra := @Allocation.writeUninit_mapExtra

/-- Internal mutation edge: both equations are produced by the actual/pure
write derivations, never additional initial-state fields. -/
theorem scalar_image_of_erased (target : TargetDataLayout) (range : AllocRange)
    (value : Scalar Provenance) (before after : Allocation Provenance TreeBorrows.BorrowTree)
    (expected next : Allocation Provenance Unit)
    (erased : before.mapExtra (fun _ => ()) = expected)
    (actualWrite : Allocation.writeScalar target range value before = .ok () after)
    (pureWrite : Allocation.writeScalar target range value expected = .ok () next) :
    after.mapExtra (fun _ => ()) = next ∧ EmptyFunction.Preservation.StorageImage next after := by
  have same := Allocation.writeScalar_mapExtra target range value before (fun _ => ())
  rw [erased,actualWrite,pureWrite] at same
  have erasedAfter : after.mapExtra (fun _ => ()) = next := (EStateM.Result.ok.inj same).2.symm
  exact ⟨erasedAfter,storageImage_of_erased after next erasedAfter⟩

theorem uninit_image_of_erased (range : AllocRange) (pointerSize : Size)
    (before after : Allocation Provenance TreeBorrows.BorrowTree)
    (expected next : Allocation Provenance Unit)
    (erased : before.mapExtra (fun _ => ()) = expected)
    (actualWrite : Allocation.writeUninit range pointerSize before = .ok () after)
    (pureWrite : Allocation.writeUninit range pointerSize expected = .ok () next) :
    after.mapExtra (fun _ => ()) = next ∧ EmptyFunction.Preservation.StorageImage next after := by
  have same := Allocation.writeUninit_mapExtra range pointerSize before (fun _ => ())
  rw [erased,actualWrite,pureWrite] at same
  have erasedAfter : after.mapExtra (fun _ => ()) = next := (EStateM.Result.ok.inj same).2.symm
  exact ⟨erasedAfter,storageImage_of_erased after next erasedAfter⟩

theorem create_uninit (size : Size) (align : Align)
    (alignment : EmptyFunction.InputDraft.AlignmentRepresentation align) :
    ∃ allocation : Allocation Provenance Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut := by
  obtain ⟨bytes,representation,normalized⟩ := alignment
  exact Allocation.tryNew_replicate size align bytes representation normalized

theorem create_uninit_full (size : Size) (align : Align)
    (alignment : EmptyFunction.InputDraft.AlignmentRepresentation align) :
    ∃ allocation : Allocation Provenance Unit,
      Allocation.tryNew size align .Uninit (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation ∧
      allocation.byteSize = size ∧ allocation.len = size.bytes.toNat ∧
      allocation.nativeBuffer = none ∧ allocation.mutability = .Mut ∧ allocation.align = align := by
  obtain ⟨bytes,representation,normalized⟩ := alignment
  exact Allocation.tryNew_replicate_full size align bytes representation normalized

theorem tryNew_uninit_image (target : TargetDataLayout) (layout : LocalLayout)
    (allocation : Allocation Provenance Unit) (tree : TreeBorrows.BorrowTree)
    (positive : (Size.fromBits target.pointerWidth.bits).bytes ≠ 0)
    (created : Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      (fun size _ => some (Array.replicate size.bytes.toNat 0)) = .ok allocation) :
    ∃ expected, EmptyFunction.Preservation.expectedImage target layout .uninit = some expected ∧
      EmptyFunction.Preservation.StorageImage expected (allocation.withExtra tree) := by
  obtain ⟨length,initialized,bytes,written⟩ := Allocation.tryNew_uninit_image
    layout.layout.size layout.layout.align.abi (Size.fromBits target.pointerWidth.bits)
    allocation positive created
  let expected := match Allocation.writeUninit (allocRange Size.ZERO layout.layout.size)
      (Size.fromBits target.pointerWidth.bits) initialized with
    | .ok _ after => after
    | .error _ after => after
  refine ⟨expected,?_,?_⟩
  · unfold EmptyFunction.Preservation.expectedImage
    rw [bytes]
    simp only [Except.toOption,bind,Bind.bind,Option.bind,pure,Pure.pure]
    dsimp only [expected]
    rw [written]
  · dsimp only [expected]
    rw [written]
    by_cases zero : layout.layout.size.bytes = 0
    · simp only [zero,↓reduceIte]
      unfold EmptyFunction.Preservation.StorageImage
      refine ⟨rfl,rfl,?_⟩
      intro byte bound
      have empty : allocation.len = 0 := by simpa [zero] using length
      change byte < allocation.len at bound
      rw [empty] at bound
      omega
    · simp only [zero,↓reduceIte]
      exact storageImage_of_erased _ allocation rfl

end EmptyFunction.ProjectedImage
