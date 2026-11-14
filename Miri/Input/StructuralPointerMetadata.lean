import Miri.Input.StructuralTail

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_middle/src/ty/sty.rs::ptr_metadata_ty_or_tail` (1772–1827).
Metadata is selected from the normalized structural tail, never inferred from a
physical pointer/layout width. Dynamic metadata needs the exact DynMetadata<T>
ADT constructor; unresolved aliases return their tail instead of a type answer.
Unsafe binders retain upstream's explicit unimplemented boundary. -/
namespace Miri.Input.StructuralPointerMetadata

inductive Choice where
  | unit
  | usize
  | dynamic (tail : TypeId)
  | unresolved (tail : TypeId)
  deriving Repr, DecidableEq

/-- Source TyKind match after `struct_tail_raw`. An ADT returned by that walk is
an enum, union or empty struct; a returned tuple is the empty tuple. -/
def classify (tail : TypeId) (shape : TypeShape) : Except String Choice :=
  match shape with
  | .bool | .char | .int _ | .uint _ | .float _ | .functionDefinition ..
  | .functionPointer .. | .rawPointer .. | .reference .. | .coroutine ..
  | .array .. | .closure .. | .coroutineClosure .. | .never | .foreign ..
  | .adt .. | .tuple .. => .ok .unit
  | .str | .slice _ => .ok .usize
  | .dynamicTraitObject .. => .ok (.dynamic tail)
  | .alias .. => .ok (.unresolved tail)
  | .unsafeBinder .. => .error "pointer metadata for unsafe binder is unimplemented upstream"
  | .patternType .. => .error "pointer metadata encountered an unexpected pattern tail"

def query (lookup : TypeId → Except String TypeShape)
    (normalize : TypeId → Except String TypeId) (fuel : Nat) (id : TypeId) :
    Except String Choice := do
  let root ← normalize id
  let tail ← StructuralTail.tail lookup normalize fuel root
  classify tail (← lookup tail)

end Miri.Input.StructuralPointerMetadata
