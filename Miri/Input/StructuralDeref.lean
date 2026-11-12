import Miri.Input.Model.Types

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`compiler/rustc_middle/src/ty/sty.rs`: `Ty::boxed_ty` and `Ty::builtin_deref`.
The Box flag is definition identity supplied by the compiler, never a name test.
No normalization is performed: these operations inspect the input TyKind. -/
namespace Miri.Input.StructuralDeref

def boxedType (shape : TypeShape) (isBox : Bool) : Except String (Option TypeId) := do
  if !isBox then return none
  let .adt data := shape | throw "Box definition identity on non-ADT type"
  match data.args[0]? with
  | some (Miri.MIR.GenericArg.Type ty) => return some ty
  | _ => throw "Box type has no first type argument"

def builtinDeref (shape : TypeShape) (isBox : Bool) (explicit : Bool) :
    Except String (Option TypeId) := do
  if let some ty ← boxedType shape isBox then return some ty
  match shape with
  | .reference ty .. => return some ty
  | .rawPointer ty _ => return if explicit then some ty else none
  | _ => return none

end Miri.Input.StructuralDeref
