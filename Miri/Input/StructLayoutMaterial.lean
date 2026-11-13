import Miri.Input.GenericSubstitution

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_middle/src/ty/sty.rs::has_trivial_sizedness`. This bounded raw-declaration
classifier establishes only the positive, environment-independent cases.
Unknown parameters, aliases and nominal types require the declaration solver;
absence of a Sized predicate never establishes unsizedness. -/
namespace Miri.Input.StructLayoutMaterial
open GenericSubstitution

private def last? : Terms → Option Term
  | .nil => none
  | .cons head .nil => some head
  | .cons _ tail => last? tail

/- Executable raw syntax node count; independent of derived SizeOf instances. -/
mutual
  def termFuel : Term → Nat
    | .node _ _ _ children | .definition _ _ _ children => termsFuel children + 1
    | .binder _ value => termFuel value + 1
    | _ => 1
  def termsFuel : Terms → Nat
    | .nil => 0
    | .cons head tail => termFuel head + termsFuel tail
end

/-- Returns true only for source constructors whose sizedness is independent
of generic arguments and ParamEnv. Fuel exhaustion is an explicit residual. -/
def guaranteedSized : Nat → Term → Bool
  | 0, _ => false
  | fuel + 1, expression => match expression with
    | .atom .type tag _ => ["bool", "char", "never", "int", "uint", "float"].contains tag
    | .node .type "tuple" _ children =>
      match last? children with | none => true | some tail => guaranteedSized fuel tail
    | .node .type "pattern" _ (.cons base (.cons _ .nil)) => guaranteedSized fuel base
    | .node .type tag _ _ =>
      ["array", "raw_pointer", "reference", "function_pointer", "unsafe_binder"].contains tag
    | .definition .type tag _ _ =>
      ["function_definition", "closure", "coroutine_closure", "coroutine", "coroutine_witness"].contains tag
    | _ => false

end Miri.Input.StructLayoutMaterial
