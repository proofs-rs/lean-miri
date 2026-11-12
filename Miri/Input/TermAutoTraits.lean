import Miri.Input.GenericSubstitution

/-! The pinned is_trivially_freeze/is_trivially_unpin fast path over canonical
source expressions. False means that the actual trait engine is required; it
is never evidence of a negative implementation. No runtime type universe is
consulted, and pointer/reference pointees are deliberately not traversed. -/
namespace Miri.Input.TermAutoTraits
open GenericSubstitution

mutual
def trivial : Nat → Term → Except String Bool
  | 0, _ => .error "term auto-trait traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .atom .type tag _ =>
      pure (#["int", "uint", "float", "bool", "char", "str", "never"].contains tag)
    | .definition .type "function_definition" .. => pure true
    | .node .type "raw_pointer" .. | .node .type "reference" ..
    | .node .type "function_pointer" .. => pure true
    | .node .type "tuple" _ children => all fuel children
    | .node .type "array" _ (.cons child _)
    | .node .type "slice" _ (.cons child .nil)
    | .node .type "pattern" _ (.cons child _) => trivial fuel child
    | _ => pure false
private def all : Nat → Terms → Except String Bool
  | 0, _ => .error "term auto-trait field traversal exhausted"
  | _ + 1, .nil => pure true
  | fuel + 1, .cons head tail => do
    unless ← trivial fuel head do return false
    all fuel tail
end

end Miri.Input.TermAutoTraits
