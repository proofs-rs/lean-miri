import empty_function.RelocationByteFold
import Miri.Interpreter.RunLoop
namespace EmptyFunction.AddressPartialByteFold
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open EmptyFunction.RelocationBytePrimitives EmptyFunction.RelocationByteFold
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
abbrev Row := Size × CtfeProvenance

private theorem one_error {State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM StepError State (Pointer Provenance))
    (initial state after : State) (row : Row) (raw current : Array UInt8)
    (provenance : Array (Size × Provenance)) (error : StepError)
    (width : layout.pointerWidth = .w64)
    (window : current.extract row.1.bytes.toNat (row.1.bytes.toNat+8) =
      raw.extract row.1.bytes.toNat (row.1.bytes.toNat+8))
    (bounds : row.1.bytes.toNat+8 ≤ current.size)
    (sourceBounds : row.1.bytes.toNat+8 ≤ raw.size)
    (resolved : pointer (Pointer.new row.2 (Size.ofBytes (word layout raw row.1.bytes.toNat))) state = .error error after) :
    action source layout pointer initial row (none,current,state,provenance) =
      ForInStep.done (some (.error (.pointerAdjustment error) after),current,state,provenance) := by
  unfold action RelocationByteActual.step
  unfold_byte_source ".Miri.Memory.pointerSize"
  unfold_byte_source ".Miri.Memory.maxU64Nat"
  have offsetBound := UInt64.toNat_lt (word layout raw row.1.bytes.toNat)
  have offset128 : (word layout raw row.1.bytes.toNat).toNat < 340282366920938463463374607431768211456 := by omega
  simp only [Pointer.new,Size.ofBytes] at resolved
  simp [-Array.extract_append,-Array.extract_extract,width,Size.fromBits,PointerWidth.bits,Pointer.new,
    window,read_window layout raw row.1.bytes.toNat sourceBounds,resolved,Size.ofBytes,
    show ¬(row.1.bytes.toNat+8>current.size) from by omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt offset128,
    show ¬((word layout raw row.1.bytes.toNat).toNat>18446744073709551615) from by omega,
    bind,Bind.bind,pure,Pure.pure]


private theorem loop {State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM StepError State (Pointer Provenance))
    (initial : State) (raw : Array UInt8) (width : layout.pointerWidth = .w64)
    (invariant : Nat → State → Prop) (rows : List Row)
    (separate : rows.Pairwise Separate)
    (bounds : ∀ row ∈ rows, row.1.bytes.toNat+8 ≤ raw.size)
    (index : Nat) (state : State) (validState : invariant index state)
    (callback : ∀ j (valid : j < rows.length) current, invariant (index+j) current →
      (∃ adjusted next, pointer (Pointer.new rows[j].2 (Size.ofBytes (word layout raw rows[j].1.bytes.toNat))) current =
        .ok adjusted next ∧ invariant (index+j+1) next) ∨
      (∃ error failed, pointer (Pointer.new rows[j].2 (Size.ofBytes (word layout raw rows[j].1.bytes.toNat))) current =
        .error error failed ∧ RunLoop.reportsUB error = false))
    (current : Array UInt8) (provenance : Array (Size × Provenance))
    (currentSize : current.size = raw.size)
    (windows : ∀ row ∈ rows, current.extract row.1.bytes.toNat (row.1.bytes.toNat+8) =
      raw.extract row.1.bytes.toNat (row.1.bytes.toNat+8)) :
    (∃ finalBytes finalState finalProvenance, finalBytes.size = raw.size ∧
      forIn rows (none,current,state,provenance) (action source layout pointer initial) =
        (none,finalBytes,finalState,finalProvenance) ∧
      invariant (index+rows.length) finalState ∧
      finalProvenance.toList.map Prod.fst = provenance.toList.map Prod.fst ++ rows.map Prod.fst) ∨
    (∃ error failed finalBytes pendingState finalProvenance,
      forIn rows (none,current,state,provenance) (action source layout pointer initial) =
        (some (.error (.pointerAdjustment error) failed),finalBytes,pendingState,finalProvenance) ∧
      RunLoop.reportsUB error = false) := by
  induction rows generalizing index state current provenance with
  | nil => exact .inl ⟨current,state,provenance,currentSize,by simp [pure,Pure.pure],by simpa using validState,by simp⟩
  | cons row rest ih =>
    rcases callback 0 (by simp) state (by simpa using validState) with good | stopped
    · obtain ⟨adjusted,next,resolved,nextState⟩ := good
      obtain ⟨encoded,encodedSize,step⟩ := (byte_source ".RelocationByteFold.one") source layout pointer initial state next row raw current provenance
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
          (∃ adjusted next, pointer (Pointer.new rest[j].2 (Size.ofBytes (word layout raw rest[j].1.bytes.toNat))) current =
            .ok adjusted next ∧ invariant (index+1+j+1) next) ∨
          (∃ error failed, pointer (Pointer.new rest[j].2 (Size.ofBytes (word layout raw rest[j].1.bytes.toNat))) current =
            .error error failed ∧ RunLoop.reportsUB error = false) := by
        intro j valid current good
        have result := callback (j+1) (by simp;omega) current (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using good)
        simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
      rcases ih (List.pairwise_cons.mp separate).2 (fun later member => bounds later (by simp [member]))
        (index+1) next (by simpa using nextState) tailCallback
        (patch current encoded row.1.bytes.toNat) (provenance.push (row.1,adjusted.provenance)) patchedSize tailWindows with finished | stopped
      · obtain ⟨finalBytes,finalState,finalProvenance,finalSize,fold,finalInvariant,keys⟩ := finished
        refine .inl ⟨finalBytes,finalState,finalProvenance,finalSize,?_,?_,?_⟩
        · simpa only [List.forIn_cons,step,bind,Bind.bind] using fold
        · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalInvariant
        · simpa only [Array.toList_push,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using keys
      · obtain ⟨error,failed,finalBytes,pendingState,finalProvenance,fold,nonUB⟩ := stopped
        refine .inr ⟨error,failed,finalBytes,pendingState,finalProvenance,?_,nonUB⟩
        simpa only [List.forIn_cons,step,bind,Bind.bind] using fold
    · obtain ⟨error,failed,resolved,nonUB⟩ := stopped
      have step := one_error source layout pointer initial state failed row raw current provenance error
        width (windows row (by simp)) (by rw [currentSize];exact bounds row (by simp))
        (bounds row (by simp)) resolved
      refine .inr ⟨error,failed,current,state,provenance,?_,nonUB⟩
      simp only [List.forIn_cons,step,bind,Bind.bind,pure,Pure.pure]


/-- The actual finite conversion either preserves its sequential invariant or
returns the actual failed callback state with a non-UB error. This internal
contract does not assume that a choice or an allocation succeeds. -/
theorem convert {State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM StepError State (Pointer Provenance))
    (invariant : Nat → State → Prop) (initial : State)
    (width : layout.pointerWidth = .w64)
    (separate : source.provenanceMap.ptrs.toList.Pairwise Separate)
    (bounds : ∀ row ∈ source.provenanceMap.ptrs, row.1.bytes.toNat+8 ≤ source.len)
    (noFragments : source.provenanceMap.byteFragments = none)
    (initialInvariant : invariant 0 initial)
    (callback : ∀ index (valid : index < source.provenanceMap.ptrs.size) state,
      invariant index state →
      (∃ adjusted next,
        pointer (Pointer.new source.provenanceMap.ptrs[index].2
          (Size.ofBytes (word layout (snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat))) state =
          .ok adjusted next ∧ invariant (index+1) next) ∨
      (∃ error failed,
        pointer (Pointer.new source.provenanceMap.ptrs[index].2
          (Size.ofBytes (word layout (snapshot source) source.provenanceMap.ptrs[index].1.bytes.toNat))) state =
          .error error failed ∧ RunLoop.reportsUB error = false)) :
    (∃ converted final,
      Allocation.adjustFromTcx source layout (fun _ _ state => .ok (snapshot source) state) pointer initial =
        .ok converted final ∧
      invariant source.provenanceMap.ptrs.size final ∧ Attributes source converted ∧
      converted.provenanceMap.ptrs.toList.map Prod.fst = source.provenanceMap.ptrs.toList.map Prod.fst ∧
      converted.provenanceMap.byteFragments = none) ∨
    (∃ error failed,
      Allocation.adjustFromTcx source layout (fun _ _ state => .ok (snapshot source) state) pointer initial =
        .error (.pointerAdjustment error) failed ∧ RunLoop.reportsUB error = false) := by
  rcases loop source layout pointer initial (snapshot source)
    width invariant source.provenanceMap.ptrs.toList separate
    (fun row member => by rw [snapshot_size];exact bounds row (by simpa using member)) 0 initial initialInvariant
    (by simpa only [Nat.zero_add,Array.length_toList,Array.getElem_toList] using callback)
    (snapshot source) #[] rfl (fun _ _ => rfl) with finished | stopped
  · obtain ⟨bytes,final,provenance,size,fold,finalInvariant,keys⟩ := finished
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
    obtain ⟨converted,finished,attributes,ptrs,fragments⟩ := (byte_source ".RelocationByteFold.finish") source layout pointer initial final bytes provenance
      outputOrdered (size.trans (snapshot_size source))
    refine .inl ⟨converted,final,?_,?_,attributes,?_,fragments⟩
    · rw [RelocationByteActual.adjust_eq_loop source layout pointer initial noFragments,←Array.forIn_toList]
      change (forIn source.provenanceMap.ptrs.toList (none,snapshot source,initial,#[])
        (action source layout pointer initial) >>= _) = _
      rw [fold]
      exact finished
    · simpa only [Nat.zero_add,Array.length_toList] using finalInvariant
    · rw [ptrs]
      simpa using keys
  · obtain ⟨error,failed,bytes,pendingState,provenance,fold,nonUB⟩ := stopped
    refine .inr ⟨error,failed,?_,nonUB⟩
    rw [RelocationByteActual.adjust_eq_loop source layout pointer initial noFragments,←Array.forIn_toList]
    change (forIn source.provenanceMap.ptrs.toList (none,snapshot source,initial,#[])
      (action source layout pointer initial) >>= _) = _
    rw [fold]
    rfl
end EmptyFunction.AddressPartialByteFold
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressPartialByteFold.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved partial byte fold axiom {dependency} in {name}"
