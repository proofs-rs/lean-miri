import Miri.Input.TypeArenaWorld

/-! Pinned mir/consts.rs::Const::{eval,ty} and const_eval/valtrees.rs's direct
scalar/FnDef branches. Ty values flow through their raw ValTree; they never borrow
an evaluated MIR-constant row. Aggregate/reference allocation and Unevaluated
evaluation require the separate CTFE machine and remain explicit unavailable
domains here. -/
namespace Miri.Input.WorldMirConstant
open Miri.MIR TypeArena

inductive Error where
  | tooGeneric (span : SpanRef)
  | invalidMaterial (message : String)
  | unavailable (message : String)
  deriving Repr

private def lift (value : Except String α) : Except Error α :=
  value.mapError .invalidMaterial

private def scalarWidth (pointerBytes : Nat) : Constructor → Except Error Nat
  | .bool => pure 1
  | .char => pure 4
  | .integer true .i8 | .integer false .u8 => pure 1
  | .integer true .i16 | .integer false .u16 => pure 2
  | .integer true .i32 | .integer false .u32 => pure 4
  | .integer true .i64 | .integer false .u64 => pure 8
  | .integer true .i128 | .integer false .u128 => pure 16
  | .integer true .isize | .integer false .usize => pure pointerBytes
  | .float .f16 => pure 2
  | .float .f32 => pure 4
  | .float .f64 => pure 8
  | .float .f128 => pure 16
  | _ => throw (.unavailable "ValTree conversion needs the CTFE allocation/type provider")

private def key (world : World) (id : TyId) : Except Error Constructor := do
  match ← lift (world.lookupType id) with
  | .constructed value => pure value
  | .material source =>
    let some value ← lift (world.materialKey source)
      | throw (.unavailable "ValTree type constructor is not yet represented in the execution World")
    pure value

/-- No layout, normalization, allocation or result catalog is read by these
direct source branches. ScalarInt owns its exact width and low-bit encoding. -/
def fromValue (world : World) (ty : TyId) (tree : ValTree) :
    Except Error ConstValue := do
  let constructor ← key world ty
  let some root := tree.nodes[tree.root]?
    | throw (.invalidMaterial "ValTree root is absent")
  unless tree.nodes.size == 1 && tree.root == 0 do
    throw (.invalidMaterial "direct ValTree branch has a noncanonical node domain")
  match constructor with
  | .functionDefinition _ arguments variables =>
    unless arguments.isEmpty && variables.isEmpty do
      throw (.unavailable "generic/bound FnDef ValTree requires full type-flag evaluation")
    let .Branch fields := root | throw (.invalidMaterial "FnDef ValTree is not zero-sized")
    unless fields.isEmpty do throw (.invalidMaterial "FnDef ValTree has children")
    pure .ZeroSized
  | _ =>
    let expected ← scalarWidth world.pointerBytes constructor
    let .Leaf bits bytes := root | throw (.invalidMaterial "primitive ValTree is not a scalar leaf")
    unless bytes == expected && bytes > 0 && bytes <= 16 && bits < 2^(8 * bytes) do
      throw (.invalidMaterial "ValTree ScalarInt width/bits disagree with its source primitive")
    pure (.Scalar (.Int bits bytes))

/-- `Const::ty` uses the Value's type rather than the outer Ty annotation.
This remains true after frame substitution, and prevents interpreting a
constant using a stale advertised type. -/
def evaluate (world : World) (span : SpanRef) : MirConst →
    Except Error (TyId × ConstValue)
  | .Val value ty => pure (ty,value)
  | .Ty _ id => do
    let constant ← lift (world.lookupConstant id)
    match constant with
    | .Value ty tree => return (ty, ← fromValue world ty tree)
    | .Param .. | .Placeholder .. => throw (.tooGeneric span)
    | _ => throw (.unavailable "MIR Ty constant is not a normalized ValTree value")
  | .Unevaluated .. => throw (.unavailable "MIR Unevaluated requires the CTFE query machine")

end Miri.Input.WorldMirConstant
