import Miri.Interpreter.Projection
open Miri Miri.ABI Miri.Memory Miri.Interpreter

private def outcome {α : Type} : Except ProjectionError α → Option ProjectionError
  | .ok _ => none
  | .error e => some e

private def layout (count : UInt64) (stride : UInt64 := 4) : TyAndLayout MIR.TyId :=
  ⟨0, ⟨.Array (Size.ofBytes stride) count, .Single 0, .Memory (sized := true),
    none, false, ⟨.ONE⟩, Size.ofBytes 16, none, .ONE, false, 0⟩⟩

private def cx : ProjectionCx AllocId where
  target := ⟨.little, .w64⟩
  maxSizeOfVal := Size.ofBytes 9223372036854775807
  isSliceOrStr := fun _ => .ok false
  field := fun _ _ => .error (.obligation "field")
  variant := fun _ _ => .error (.obligation "variant")
  dynamicAlign := fun _ _ => .error (.obligation "dynamic")
  packedAlign := fun _ => .error (.obligation "packed")
  immediateOffset := fun _ _ _ _ => .error (.obligation "immediate")
  memoryOffset := fun _ _ _ _ => .error (.obligation "memory")
  subsliceLayout := fun _ _ => .error (.obligation "subslice")
  layoutOf := fun _ => .error (.obligation "layout")
  deref := fun _ => .error (.obligation "deref")
  localIndex := fun _ => .error (.obligation "local")

private def base (count : UInt64) (stride : UInt64 := 4) : OpTy AllocId :=
  ⟨.immediate .uninit, layout count stride⟩

-- Bounds failure precedes stride overflow and the missing field query.
example : outcome (projectIndex cx (base 2 18446744073709551615) 2) =
    some (.bounds 2 2) := by decide
example : outcome (projectIndex cx (base 3 18446744073709551615) 2) =
    some .pointerArithOverflow := by decide
example : outcome (projectIndex cx (base 3) 1) = some (.obligation "field") := by decide
-- Minimum length check precedes the invalid from-end offset invariant.
example : outcome (projectConstantIndex cx (base 2) 0 3 true) =
    some (.bounds 3 2) := by decide
example : outcome (projectConstantIndex cx (base 3) 0 3 true) =
    some (.invariant "invalid from-end constant index") := by decide
example : outcome (projectSubslice cx (base 3) 2 2 true) =
    some (.bounds 3 4) := by decide
example : outcome (projectSubslice cx (base 3) 2 1 false) =
    some (.invariant "subslice length underflow") := by decide
example : outcome (projectDowncast cx (base 3) 99) = some (.obligation "variant") := by decide
-- Explicit ABI obligation is preserved even for Uninit.
example : outcome (projectionImmediateOffset (fun _ _ => .error (.obligation "ABI"))
    (Immediate.uninit : Immediate AllocId) (layout 3) .ZERO (layout 3)) =
    some (.obligation "ABI") := by decide

private def iterator : ProjectionArrayIterator AllocId :=
  ⟨base 3, 0, 3, Size.ofBytes 4, layout 1⟩

-- Failed projection still consumes the iterator index.
example : (match (ProjectionArrayIterator.next cx).run iterator with
    | .error (.obligation "immediate") state => state.nextIndex == 1
    | _ => false) = true := by decide

-- Same saturation boundary exercised by source_helpers.rs.
example : outcome (projectSubslice cx (base 18446744073709551615)
    18446744073709551615 1 true) =
    some (.bounds 18446744073709551615 18446744073709551615) := by decide

-- compute_size_in_bytes uses the inclusive max_size_of_val, rather than
-- rustc_abi Size.checkedMul's exclusive obj_size_bound.
example : outcome (projectIndex { cx with maxSizeOfVal := Size.ofBytes 8 }
    (base 3 4) 2) = some (.obligation "field") := by decide
example : outcome (projectIndex { cx with maxSizeOfVal := Size.ofBytes 7 }
    (base 3 4) 2) = some .pointerArithOverflow := by decide
example : (Size.ofBytes 4).checkedMul 2 (⟨.little, .w16⟩ : TargetDataLayout) =
    some (Size.ofBytes 8) := by decide
example : outcome (projectIndex { cx with
    target := ⟨.little, .w16⟩
    maxSizeOfVal := Size.ofBytes 32767 } (base 3 16384) 2) =
    some .pointerArithOverflow := by decide
example : outcome (projectIndex { cx with
    target := ⟨.little, .w16⟩
    maxSizeOfVal := Size.ofBytes 32768 } (base 3 16384) 2) =
    some (.obligation "field") := by decide
example : (Size.ofBytes 16384).checkedMul 2 (⟨.little, .w16⟩ : TargetDataLayout) = none := by decide
