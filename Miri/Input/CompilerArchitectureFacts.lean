import Miri.Interpreter.IntrinsicSimd
import Miri.Input.CompilerFacts
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.RuntimeArrayQueries

/-! Exact compiler-owned identities used by architecture intrinsic helpers.
Source helpers.rs::get_twice_wide_int_ty and project_to_simd. -/
namespace Miri.Input.CompilerArchitectureFacts
open Lean Miri.ABI Miri.MIR Miri.Interpreter

def integerLayout (runtime : RuntimeMetadata) (bits : Nat) (signed : Bool) : Except String LocalLayout := do
  unless [8,16,32,64,128].contains bits do throw "architecture integer constructor has unsupported width"
  CompilerPrimitiveFacts.primitiveLayout runtime s!"{if signed then "i" else "u"}{bits}"

def integerLayoutContext (context : CompilerFacts.Context) (bits : Nat) (signed : Bool) :
    Except String LocalLayout := do
  unless [8,16,32,64,128].contains bits do throw "architecture integer constructor has unsupported width"
  context.primitiveLayout s!"{if signed then "i" else "u"}{bits}"

private def twiceWidth (node : TypeNode) : Except String (Nat × Bool) := do
  unless node.shapeStatus == .supported do throw "missing integer type shape for twice-wide constructor"
  let (kind,signed) ← match node.shapeKind with
    | .int => pure (node.shapeMetadata.signedKind,true)
    | .uint => pure (node.shapeMetadata.unsignedKind,false)
    | _ => throw "twice-wide source helper requires fixed integer type"
  let some (.known kind) := kind | throw "twice-wide integer kind absent"
  let bits ← match kind with
    | .u8 | .i8 => pure 16 | .u16 | .i16 => pure 32
    | .u32 | .i32 => pure 64 | .u64 | .i64 => pure 128
    | _ => throw "twice-wide source helper rejects this integer kind"
  return (bits,signed)

def twiceWideLayout (runtime : RuntimeMetadata) (id : TyId) : Except String LocalLayout := do
  let (bits,signed) ← twiceWidth (← runtime.node id |>.mapError toString)
  integerLayout runtime bits signed

def twiceWideLayoutContext (context : CompilerFacts.Context) (id : TyId) : Except String LocalLayout := do
  let (bits,signed) ← twiceWidth (← context.runtime.node id |>.mapError toString)
  integerLayoutContext context bits signed

def isSimd (context : CompilerFacts.Context) (id : TyId) : Except String Bool :=
  CompilerFacts.boolean context id "is_simd"

/-- Query payload contains actual compiler lane count and element identity;
backend vector size does not establish either source property. -/
def simdSizeAndType (context : CompilerFacts.Context) (id : TyId) : Except String (UInt64 × TyId) := do
  unless ← isSimd context id do throw "simd_size_and_type requested for non-SIMD compiler type"
  let node ← context.runtime.node id |>.mapError toString
  let some facts := node.compilerFacts | throw "missing SIMD compiler facts"
  let some (count,element) ← facts.simdSizeAndType | throw "SIMD lane compiler query has no value"
  unless count < 2^64 do throw "SIMD lane count exceeds source u64"
  let _ ← context.runtime.lookup element |>.mapError toString
  pure (UInt64.ofNat count,element)

private def liftQuery (query : Except String A) : EStateM StepError S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

def simdHooks (context : CompilerFacts.Context) (base : IntrinsicSimdHooks P S C V) :
    IntrinsicSimdHooks P S C V :=
  {base with
    isSimd := fun _ id => liftQuery (isSimd context id)
    simdSizeAndType := fun _ id => liftQuery (simdSizeAndType context id)}

end Miri.Input.CompilerArchitectureFacts
