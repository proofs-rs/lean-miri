import duplicate_prefix.GlobalRelocationActualStep
namespace DuplicatePrefix.GlobalRelocationFiniteLoop
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev Row := GlobalRelocationTwoWords.Row

def input (row : Row) : Size × CtfeProvenance := (row.position,row.provenance)
def output (row : Row) : Size × Provenance := (row.position,.concrete row.provenance.allocId row.root)
def Separate (a b : Row) : Prop := a.position.bytes.toNat+8≤b.position.bytes.toNat

noncomputable def action {Error State : Type} (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance)) (before : State) :=
  GlobalRelocationActualStep.step source layout (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before

private theorem one {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (before : State) (row : Row) (bytes : Array UInt8) (provenance : Array (Size × Provenance))
    (width : layout.pointerWidth = .w64)
    (window : bytes.extract row.position.bytes.toNat (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word)
    (bounds : row.position.bytes.toNat+8≤bytes.size)
    (resolved : pointer (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) before =
      .ok (Pointer.new (Provenance.concrete row.provenance.allocId row.root)
        (Size.ofBytes (row.base+GlobalRelocationWordDecode.value layout row.word))) before) :
    ∃ encoded : Array UInt8, encoded.size=8 ∧
      action source layout pointer before (input row) (none,bytes,before,provenance) =
        ForInStep.yield (none,GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat,before,provenance.push (output row)) := by
  obtain ⟨encoded,encoding,size⟩ := PhysicalScalarReturn.target_word_exists layout
    (BitVec.ofNat 128 (row.base+GlobalRelocationWordDecode.value layout row.word).toNat)
  refine ⟨encoded,size,?_⟩
  unfold action GlobalRelocationActualStep.step
  unfold_global_data ".Miri.Memory.pointerSize"
  unfold_global_data ".Miri.Memory.maxU64Nat"
  have offsetBound := UInt64.toNat_lt (GlobalRelocationWordDecode.value layout row.word)
  have offset128 : (GlobalRelocationWordDecode.value layout row.word).toNat < 340282366920938463463374607431768211456 := by omega
  simp only [Size.ofBytes,UInt64.toNat_add] at encoding
  simp only [Pointer.new,Size.ofBytes] at resolved
  simp [-Array.extract_append,-Array.extract_extract,input,output,width,Size.fromBits,PointerWidth.bits,Pointer.new,
    window,GlobalRelocationWordDecode.read,resolved,encoding,Size.ofBytes,
    show ¬(row.position.bytes.toNat+8>bytes.size) from by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt offset128,
    show ¬((GlobalRelocationWordDecode.value layout row.word).toNat>18446744073709551615) from by omega,
    GlobalRelocationSplice.patch,Array.append_assoc,
    bind,Bind.bind,pure,Pure.pure]

private theorem fold {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance)) (before : State)
    (width : layout.pointerWidth = .w64) (rows : List Row)
    (separate : rows.Pairwise Separate)
    (resolved : ∀ row ∈ rows,
      pointer (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) before =
        .ok (Pointer.new (Provenance.concrete row.provenance.allocId row.root)
          (Size.ofBytes (row.base+GlobalRelocationWordDecode.value layout row.word))) before)
    (bytes : Array UInt8) (provenance : Array (Size × Provenance))
    (windows : ∀ row ∈ rows, bytes.extract row.position.bytes.toNat (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word)
    (bounds : ∀ row ∈ rows, row.position.bytes.toNat+8≤bytes.size) :
    ∃ finalBytes, finalBytes.size=bytes.size ∧
      forIn (rows.map input) (none,bytes,before,provenance) (action source layout pointer before) =
        (none,finalBytes,before,provenance ++ (rows.map output).toArray) := by
  induction rows generalizing bytes provenance with
  | nil => exact ⟨bytes,rfl,by simp [pure,Pure.pure]⟩
  | cons row rest ih =>
    obtain ⟨encoded,encodedSize,step⟩ := one source layout pointer before row bytes provenance width
      (windows row (by simp)) (bounds row (by simp)) (resolved row (by simp))
    have patchedSize := GlobalRelocationSplice.size bytes encoded row.position.bytes.toNat (bounds row (by simp)) encodedSize
    have windowsRest : ∀ next ∈ rest,
        (GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat).extract next.position.bytes.toNat
          (next.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes next.word := by
      intro next member
      exact (GlobalRelocationSplice.later_window bytes encoded row.position.bytes.toNat next.position.bytes.toNat
        ((List.pairwise_cons.mp separate).1 next member) (bounds next (by simp [member])) encodedSize).trans
        (windows next (by simp [member]))
    obtain ⟨finalBytes,finalSize,loop⟩ := ih (List.pairwise_cons.mp separate).2
      (fun next member => resolved next (by simp [member]))
      (GlobalRelocationSplice.patch bytes encoded row.position.bytes.toNat) (provenance.push (output row)) windowsRest
      (fun next member => by rw [patchedSize];exact bounds next (by simp [member]))
    refine ⟨finalBytes,finalSize.trans patchedSize,?_⟩
    simp only [List.map_cons,List.forIn_cons,step,bind,Bind.bind] at ⊢
    rw [loop]
    rw [List.toArray_cons,Array.push_eq_append,Array.append_assoc]

/-- The actual pinned relocation loop succeeds for any finite ordered disjoint
list. Every reader and pointer callback result follows from initial source
bytes, compiler declarations and existing root/address caches. -/
theorem run {K U : Type} (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout) (rows : List Row)
    (known : ∀ row ∈ rows, GlobalRelocationTwoWords.Known before.memory tracker before.user.addresses.baseAddr row)
    (enabled : before.borrowTracker = some tracker)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (separate : rows.Pairwise Separate)
    (windows : ∀ row ∈ rows, (AllocationCopy.snapshot source).extract row.position.bytes.toNat
      (row.position.bytes.toNat+8) = GlobalRelocationWordDecode.bytes row.word)
    (bounds : ∀ row ∈ rows, row.position.bytes.toNat+8≤(AllocationCopy.snapshot source).size) :
    ∃ finalBytes, finalBytes.size=(AllocationCopy.snapshot source).size ∧
      forIn (rows.map input) (none,AllocationCopy.snapshot source,before,#[])
        (action source layout (PointerSource.globalRootPointer choices hooks externStatic) before) =
          (none,finalBytes,before,(rows.map output).toArray) := by
  have resolved (row : Row) (member : row ∈ rows) :
      PointerSource.globalRootPointer choices hooks externStatic
        (Pointer.new row.provenance (Size.ofBytes (GlobalRelocationWordDecode.value layout row.word))) before =
        .ok (Pointer.new (Provenance.concrete row.provenance.allocId row.root)
          (Size.ofBytes (row.base+GlobalRelocationWordDecode.value layout row.word))) before := by
    obtain ⟨target,rootCached,addressCached⟩ := known row member
    rcases target with ⟨allocation,descriptor⟩ | ⟨definition,size,align,mutability,descriptor⟩
    · exact GlobalRelocationRootPointer.cached choices hooks externStatic before tracker row.provenance
        (GlobalRelocationWordDecode.value layout row.word) row.base row.root allocation descriptor enabled rootCached addressCached arithmetic
    · exact GlobalStaticRelocationConversion.cached_root choices hooks externStatic before tracker row.provenance
        (GlobalRelocationWordDecode.value layout row.word) row.base row.root definition size align mutability descriptor enabled rootCached addressCached arithmetic
  obtain ⟨finalBytes,size,loop⟩ := fold source layout (PointerSource.globalRootPointer choices hooks externStatic)
    before width rows separate resolved (AllocationCopy.snapshot source) #[] windows bounds
  exact ⟨finalBytes,size,by simpa using loop⟩
end DuplicatePrefix.GlobalRelocationFiniteLoop
