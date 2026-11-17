import duplicate_prefix.ScalarOperations
import duplicate_prefix.ScalarPointers
import Miri.Interpreter.PointerMachineBindings

/-! Scalar/type checks of the production pointer Offset arm. The remaining
effect is the actual pointer-bounds operation; it is not replaced by a stub. -/

namespace DuplicatePrefix.PointerDispatch
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def pointerImmediate (target : TargetDataLayout) (pointer : Pointer Provenance)
    (layout : LocalLayout) : RvalueImmTy Provenance :=
  ⟨.scalar (.fromPointer target pointer), layout⟩

open Lean Elab Tactic in
elab "simp_pointer_dispatch" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".PointerMachine.liftResult" : String) then some name else none
  let [name] := found | throwError "expected exact pointer lift implementation"
  let name := mkIdent name
  evalTactic (← `(tactic| simp_all [PointerMachine.binary, pointerImmediate,
    Immediate.toScalar, Immediate.toScalarPair, ScalarOperations.usizeImmediate,
    bind, EStateM.bind, pure, EStateM.pure, Except.mapError, $name:ident]))

theorem offset_reduction
    (pointers : PointerMachine.Hooks K User)
    (target : TargetDataLayout)
    (ops : ScalarOpsHooks Provenance (PointerMachine.State K User) Choice)
    (isRaw : Choice → TyId → PointerMachine.M K User Bool)
    (usize : Choice → PointerMachine.M K User LocalLayout)
    (pointee : Choice → TyId → PointerMachine.M K User LocalLayout)
    (choice : Choice) (pointer : Pointer Provenance)
    (pointerLayout countLayout elementLayout overflowLayout : LocalLayout) (count : UInt64)
    (pointeeQuery : pointee choice pointerLayout.ty = pure elementLayout)
    (sized : elementLayout.layout.isSized = true)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (countSize : countLayout.layout.size = Size.ofBytes 8)
    (pointerSize : pointers.arithmetic.pointerSize = Size.ofBytes 8)
    (classification : ops.classify choice countLayout.ty = pure (.integer .usize))
    (overflowQuery : ops.overflowLayout choice countLayout = pure overflowLayout)
    (unsigned : countLayout.layout.backendRepr.isSigned = .ok false)
    (fits : count.toNat < 2 ^ 63) :
    PointerMachine.binary pointers target ops isRaw usize pointee choice .Offset
      (pointerImmediate target pointer pointerLayout)
      (ScalarOperations.usizeImmediate count countLayout) =
      (do
        let next ← PointerMachine.offsetInbounds pointers pointer.withOptionalProvenance
          (Int64.ofInt (Int.ofNat count.toNat))
        match Scalar.fromMaybePointer target next with
        | .error error => throw (ScalarOps.scalarError error)
        | .ok scalar => pure ⟨.scalar scalar, pointerLayout⟩) := by
  have product := ScalarOperations.usize_mul_one ops choice countLayout overflowLayout count
    classification overflowQuery countSize
  have roundtrip := ScalarPointers.pointer_roundtrip target pointer
  have signed := ScalarPointers.scalar_uint64_to_isize (Prov := Provenance) count fits
  have offsetValue : (Int64.ofInt (Int.ofNat count.toNat)).toInt = Int.ofNat count.toNat := by
    exact Int64.toInt_ofInt_of_le
      (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr fits)
  have stride := ScalarPointers.scalar_int_one (Prov := Provenance)
  have overflowFalse := ScalarPointers.scalar_false_bool (Prov := Provenance)
  have strideBytes : (Size.ofBytes 1).bytes.toNat = 1 := rfl
  funext state
  simp_pointer_dispatch
  have nonnegative : ¬ (count.toNat : Int) < 0 := by omega
  simp only [nonnegative, ↓reduceIte]
  cases offsetResult : PointerMachine.offsetInbounds pointers pointer.withOptionalProvenance
      (Int64.ofInt (count.toNat : Int)) state with
  | error error finalState => simp [EStateM.bind, offsetResult]
  | ok next finalState =>
    simp only [EStateM.bind, offsetResult]
    cases scalarResult : Scalar.fromMaybePointer target next <;>
      simp [scalarResult, EStateM.bind, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end DuplicatePrefix.PointerDispatch
