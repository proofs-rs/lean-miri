import duplicate_prefix.ScalarArithmetic
import Miri.Interpreter.ScalarOps

/-! Checked scalar dispatch for usize guards. Compiler classification/result
layout equalities are static-query premises; no memory or scalar-operation
success is assumed. -/

namespace DuplicatePrefix.ScalarOperations
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def usizeImmediate (value : UInt64) (layout : LocalLayout) : RvalueImmTy Prov :=
  ⟨.scalar (.fromScalarInt (.ofUInt64 value)), layout⟩

open Lean Elab Tactic in
elab "simp_scalar_dispatch" : tactic => do
  let env ← getEnv
  let suffixes := [".ScalarOps.toInteger", ".ScalarOps.toScalar", ".ScalarOps.liftResult",
    ".ScalarOps.finish", ".ScalarOps.assertSameType", ".ScalarOps.isShift"]
  let names ← suffixes.mapM fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    match found with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected one source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [ScalarOps.binary, usizeImmediate,
    Immediate.toScalar, Scalar.fromScalarInt, Scalar.toScalarInt, Scalar.tryToScalarInt,
    ScalarInt.toBits, ScalarInt.size, ScalarInt.ofUInt64,
    bind, EStateM.bind, pure, EStateM.pure, Except.pure, Except.bind, Except.mapError,
    $[$names:ident],*]))

theorem usize_eq [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout boolLayout : LocalLayout) (left right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.boolLayout choice = pure boolLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .Eq (usizeImmediate left layout) (usizeImmediate right layout) =
      pure (⟨.scalar (.fromBool (left == right)), boolLayout⟩ : RvalueImmTy Prov) := by
  have operation := ScalarArithmetic.usize_eq left right
  simp only [ScalarArithmetic.usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem usize_gt [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout boolLayout : LocalLayout) (left right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.boolLayout choice = pure boolLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .Gt (usizeImmediate left layout) (usizeImmediate right layout) =
      pure (⟨.scalar (.fromBool (left > right)), boolLayout⟩ : RvalueImmTy Prov) := by
  have operation := ScalarArithmetic.usize_gt left right
  simp only [ScalarArithmetic.usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem usize_div_two [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout : LocalLayout) (value : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .Div (usizeImmediate value layout) (usizeImmediate 2 layout) =
      pure (usizeImmediate (value / 2) layout : RvalueImmTy Prov) := by
  have operation := ScalarArithmetic.usize_div_two value
  simp only [ScalarArithmetic.usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem usize_mul_one [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout overflowLayout : LocalLayout) (value : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.overflowLayout choice layout = pure overflowLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .MulWithOverflow (usizeImmediate value layout) (usizeImmediate 1 layout) =
      pure (⟨.scalarPair (.fromScalarInt (.ofUInt64 value)) (.fromBool false),
        overflowLayout⟩ : RvalueImmTy Prov) := by
  have operation := ScalarArithmetic.usize_mul_one value
  simp only [ScalarArithmetic.usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

def boolImmediate (value : Bool) (layout : LocalLayout) : RvalueImmTy Prov :=
  ⟨.scalar (.fromBool value),layout⟩

theorem bool_scalar_roundtrip [PointerProvenance Prov] (value : Bool) :
    (Scalar.fromBool (Prov := Prov) value).toBool = .ok value := by
  cases value <;> rfl

theorem bool_eq [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout : LocalLayout) (left right : Bool)
    (classification : hooks.classify choice layout.ty = pure .boolean)
    (resultLayout : hooks.boolLayout choice = pure layout) :
    ScalarOps.binary hooks choice .Eq (boolImmediate left layout) (boolImmediate right layout) =
      pure (boolImmediate (left == right) layout) := by
  have leftBool := bool_scalar_roundtrip (Prov := Prov) left
  have rightBool := bool_scalar_roundtrip (Prov := Prov) right
  have operation : IntegerOps.binaryBool .Eq left right = .ok (.boolean (left == right)) := rfl
  funext state
  unfold boolImmediate
  simp_scalar_dispatch

#print axioms bool_eq

end DuplicatePrefix.ScalarOperations
