import empty_function.RelocationByteActual
namespace EmptyFunction.RelocationByteFold
open Miri Miri.ABI Miri.Memory
open RelocationBytePrimitives
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
abbrev Row := Size × CtfeProvenance

def Separate (left right : Row) : Prop := left.1.bytes.toNat+8 ≤ right.1.bytes.toNat

noncomputable def action {Error State : Type} (source : Allocation CtfeProvenance Unit)
    (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance)) (initial : State) :=
  RelocationByteActual.step source layout (fun _ _ state => .ok (snapshot source) state) pointer initial

private theorem one {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial state after : State) (row : Row) (raw current : Array UInt8)
    (provenance : Array (Size × Provenance)) (adjusted : Pointer Provenance)
    (width : layout.pointerWidth = .w64)
    (window : current.extract row.1.bytes.toNat (row.1.bytes.toNat+8) =
      raw.extract row.1.bytes.toNat (row.1.bytes.toNat+8))
    (bounds : row.1.bytes.toNat+8 ≤ current.size)
    (sourceBounds : row.1.bytes.toNat+8 ≤ raw.size)
    (resolved : pointer (Pointer.new row.2 (Size.ofBytes (word layout raw row.1.bytes.toNat))) state =
      .ok adjusted after) :
    ∃ encoded : Array UInt8, encoded.size=8 ∧
      action source layout pointer initial row (none,current,state,provenance) =
        ForInStep.yield (none,patch current encoded row.1.bytes.toNat,after,
          provenance.push (row.1,adjusted.provenance)) := by
  obtain ⟨encoded,encoding,size⟩ := target_word_exists layout (BitVec.ofNat 128 adjusted.offset.bytes.toNat)
  refine ⟨encoded,size,?_⟩
  unfold action RelocationByteActual.step
  unfold_byte_source ".Miri.Memory.pointerSize"
  unfold_byte_source ".Miri.Memory.maxU64Nat"
  have offsetBound := UInt64.toNat_lt (word layout raw row.1.bytes.toNat)
  have offset128 : (word layout raw row.1.bytes.toNat).toNat < 340282366920938463463374607431768211456 := by omega
  simp only [sourceEncode,Size.ofBytes] at encoding
  simp only [Pointer.new,Size.ofBytes] at resolved
  simp [-Array.extract_append,-Array.extract_extract,width,Size.fromBits,PointerWidth.bits,Pointer.new,
    window,read_window layout raw row.1.bytes.toNat sourceBounds,resolved,encoding,Size.ofBytes,
    show ¬(row.1.bytes.toNat+8>current.size) from by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt offset128,
    show ¬((word layout raw row.1.bytes.toNat).toNat>18446744073709551615) from by omega,
    patch,Array.append_assoc,bind,Bind.bind,pure,Pure.pure]

/-- Induction over the actual source loop. The callback contract is internal:
the machine proof instantiates it with actual root/address results at each
updated state, while this lemma accounts for all byte and provenance work. -/
private theorem loop {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial : State) (raw : Array UInt8) (width : layout.pointerWidth = .w64)
    (invariant : Nat → State → Prop) (rows : List Row)
    (separate : rows.Pairwise Separate)
    (bounds : ∀ row ∈ rows, row.1.bytes.toNat+8 ≤ raw.size)
    (index : Nat) (state : State) (validState : invariant index state)
    (callback : ∀ j (valid : j < rows.length) current, invariant (index+j) current →
      ∃ adjusted next, pointer (Pointer.new rows[j].2 (Size.ofBytes (word layout raw rows[j].1.bytes.toNat))) current =
        .ok adjusted next ∧ invariant (index+j+1) next)
    (current : Array UInt8) (provenance : Array (Size × Provenance))
    (currentSize : current.size = raw.size)
    (windows : ∀ row ∈ rows, current.extract row.1.bytes.toNat (row.1.bytes.toNat+8) =
      raw.extract row.1.bytes.toNat (row.1.bytes.toNat+8)) :
    ∃ finalBytes finalState finalProvenance, finalBytes.size = raw.size ∧
      forIn rows (none,current,state,provenance) (action source layout pointer initial) =
        (none,finalBytes,finalState,finalProvenance) ∧
      invariant (index+rows.length) finalState ∧
      finalProvenance.toList.map Prod.fst = provenance.toList.map Prod.fst ++ rows.map Prod.fst := by
  induction rows generalizing index state current provenance with
  | nil => exact ⟨current,state,provenance,currentSize,by simp [pure,Pure.pure],by simpa using validState,by simp⟩
  | cons row rest ih =>
    obtain ⟨adjusted,next,resolved,nextState⟩ := callback 0 (by simp) state (by simpa using validState)
    obtain ⟨encoded,encodedSize,step⟩ := one source layout pointer initial state next row raw current provenance
      adjusted width (windows row (by simp)) (by rw [currentSize];exact bounds row (by simp))
      (bounds row (by simp)) resolved
    have patchedSize := (RelocationBytePrimitives.size current encoded row.1.bytes.toNat
      (by rw [currentSize];exact bounds row (by simp)) encodedSize).trans currentSize
    have tailWindows : ∀ later ∈ rest, (patch current encoded row.1.bytes.toNat).extract later.1.bytes.toNat
        (later.1.bytes.toNat+8) = raw.extract later.1.bytes.toNat (later.1.bytes.toNat+8) := by
      intro later member
      exact (later_window current encoded row.1.bytes.toNat later.1.bytes.toNat
        ((List.pairwise_cons.mp separate).1 later member)
        (by rw [currentSize];exact bounds later (by simp [member])) encodedSize).trans
        (windows later (by simp [member]))
    have tailCallback : ∀ j (valid : j < rest.length) current, invariant (index+1+j) current →
        ∃ adjusted next, pointer (Pointer.new rest[j].2 (Size.ofBytes (word layout raw rest[j].1.bytes.toNat))) current =
          .ok adjusted next ∧ invariant (index+1+j+1) next := by
      intro j valid current good
      have result := callback (j+1) (by simp;omega) current (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using good)
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
    obtain ⟨finalBytes,finalState,finalProvenance,finalSize,fold,finalInvariant,keys⟩ := ih
      (List.pairwise_cons.mp separate).2 (fun later member => bounds later (by simp [member]))
      (index+1) next (by simpa using nextState) tailCallback
      (patch current encoded row.1.bytes.toNat) (provenance.push (row.1,adjusted.provenance)) patchedSize tailWindows
    refine ⟨finalBytes,finalState,finalProvenance,finalSize,?_,?_,?_⟩
    · simp only [List.forIn_cons,step,bind,Bind.bind]
      exact fold
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalInvariant
    · simpa only [Array.toList_push,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using keys

structure Attributes (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) : Prop where
  size : converted.byteSize = source.byteSize
  storage : converted.len = source.len
  mask : converted.initializationMask = source.initializationMask
  align : converted.align = source.align
  mutability : converted.mutability = source.mutability
  native : converted.nativeBuffer = none

private theorem sorted (rows : List (Size × Provenance))
    (ordered : rows.Pairwise (fun left right => left.1.bytes < right.1.bytes)) :
    (byte_source ".Miri.Memory.ProvenanceMap.sortedKeys") rows = true := by
  induction rows with
  | nil =>
    unfold_byte_source ".Miri.Memory.ProvenanceMap.sortedKeys"
    rfl
  | cons row rest ih =>
    cases rest with
    | nil =>
      unfold_byte_source ".Miri.Memory.ProvenanceMap.sortedKeys"
      rfl
    | cons next tail =>
      have increasing := (List.pairwise_cons.mp ordered).1 next (by simp)
      have orderedTail := ih (List.pairwise_cons.mp ordered).2
      unfold_byte_source ".Miri.Memory.ProvenanceMap.sortedKeys"
      simpa only [increasing,decide_true,Bool.true_and] using orderedTail

private theorem finish {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (initial state : State) (bytes : Array UInt8) (provenance : Array (Size × Provenance))
    (ordered : provenance.toList.Pairwise (fun left right => left.1.bytes < right.1.bytes))
    (size : bytes.size = source.len) :
    ∃ converted : Allocation Provenance Unit,
      RelocationByteActual.finish source layout (fun _ _ current => .ok (snapshot source) current) pointer initial
        (none,bytes,state,provenance) = .ok converted state ∧
      Attributes source converted ∧ converted.provenanceMap.ptrs = provenance ∧
      converted.provenanceMap.byteFragments = none := by
  have constructed : ∃ result : ProvenanceMap Provenance,
      ProvenanceMap.fromPresortedPtrs provenance = .ok result ∧ result.ptrs = provenance ∧ result.byteFragments = none := by
    simp only [ProvenanceMap.fromPresortedPtrs,sorted provenance.toList ordered,ite_true]
    exact ⟨_,rfl,rfl,rfl⟩
  obtain ⟨result,constructed,ptrs,fragments⟩ := constructed
  unfold RelocationByteActual.finish
  cases source
  rename_i raw allocationSize sourceProvenance mask align mutability extra native
  change bytes.size = raw.size at size
  simp [constructed,pure,Pure.pure,bind,Bind.bind]
  refine ⟨_,rfl,?_,ptrs,fragments⟩
  exact ⟨rfl,size,rfl,rfl,rfl,rfl⟩

/-- Arbitrary finite source relocations through the unchanged conversion
algorithm. The sequential callback contract is instantiated by the machine
proof; it is not an input-validity condition. Reader, encoder, slice bounds,
remaining windows, provenance ordering and allocation attributes are discharged
here for every eight-byte source word and both endiannesses. -/
theorem convert {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (invariant : Nat → State → Prop) (initial : State)
    (width : layout.pointerWidth = .w64)
    (separate : source.provenanceMap.ptrs.toList.Pairwise Separate)
    (bounds : ∀ row ∈ source.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ source.len)
    (noFragments : source.provenanceMap.byteFragments = none)
    (initialInvariant : invariant 0 initial)
    (callback : ∀ index (valid : index < source.provenanceMap.ptrs.size) state,
      invariant index state → ∃ adjusted next,
        pointer (Pointer.new source.provenanceMap.ptrs[index].2
          (Size.ofBytes (word layout (snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat))) state =
          .ok adjusted next ∧ invariant (index+1) next) :
    ∃ converted final,
      Allocation.adjustFromTcx source layout (fun _ _ state => .ok (snapshot source) state) pointer initial =
        .ok converted final ∧
      invariant source.provenanceMap.ptrs.size final ∧ Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none := by
  obtain ⟨bytes,final,provenance,size,fold,finalInvariant,keys⟩ := loop source layout pointer initial (snapshot source)
    width invariant source.provenanceMap.ptrs.toList separate
    (fun row member => by rw [snapshot_size];exact bounds row (by simpa using member)) 0 initial initialInvariant
    (by simpa only [Nat.zero_add,Array.length_toList,Array.getElem_toList] using callback)
    (snapshot source) #[] rfl (fun _ _ => rfl)
  have outputOrdered : provenance.toList.Pairwise (fun left right => left.1.bytes < right.1.bytes) := by
    have inputKeys : (source.provenanceMap.ptrs.toList.map Prod.fst).Pairwise (fun left right => left.bytes < right.bytes) := by
      apply separate.map Prod.fst
      intro left right separated
      change left.1.bytes.toNat < right.1.bytes.toNat
      unfold Separate at separated
      omega
    have outputKeys : (provenance.toList.map Prod.fst).Pairwise (fun left right => left.bytes < right.bytes) := by
      rw [keys]
      simpa using inputKeys
    exact (List.pairwise_map (f := Prod.fst) (R := fun left right : Size => left.bytes < right.bytes)).mp outputKeys
  obtain ⟨converted,finished,attributes,ptrs,fragments⟩ := finish source layout pointer initial final bytes provenance
    outputOrdered (size.trans (snapshot_size source))
  refine ⟨converted,final,?_,?_,attributes,?_,fragments⟩
  · rw [RelocationByteActual.adjust_eq_loop source layout pointer initial noFragments,←Array.forIn_toList]
    change (forIn source.provenanceMap.ptrs.toList (none,snapshot source,initial,#[])
      (action source layout pointer initial) >>= _) = _
    rw [fold]
    exact finished
  · simpa only [Nat.zero_add,Array.length_toList] using finalInvariant
  · rw [ptrs]
    simpa using keys
end EmptyFunction.RelocationByteFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if ["EmptyFunction.RelocationBytePrimitives.","EmptyFunction.RelocationByteSourceExtraction.",
        "EmptyFunction.RelocationByteActual.","EmptyFunction.RelocationByteFold."].any (fun label =>
          (name.toString.splitOn label).length != 1) then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation byte fold axiom {dependency} in {name}"
