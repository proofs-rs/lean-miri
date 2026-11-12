import Miri.Input.StructuralDeref

open Miri.Input Miri.Input.StructuralDeref

private def adt (args : Array Miri.MIR.GenericArg) : TypeShape := .adt {
  definition := 0, kind := .structKind, args, variants := #[], representation := {
    integer := none, alignBytes := none, packBytes := none, flagsBits := 0,
    scalableElement := none, fieldShuffleSeed := 0 } }

-- These kernel checks exercise the pinned rule, including the explicit-only
-- raw-pointer case and malformed identity seeds. They are not a rustc comparison.
example : builtinDeref (.rawPointer 7 .Mut) false true = .ok (some 7) := rfl
example : builtinDeref (.rawPointer 7 .Mut) false false = .ok none := rfl
example : builtinDeref (.reference 8 .Not .Erased) false false = .ok (some 8) := rfl
example : builtinDeref (.tuple #[3, 4]) false true = .ok none := rfl
example : boxedType (.rawPointer 7 .Mut) true =
    .error "Box definition identity on non-ADT type" := rfl
example : builtinDeref (adt #[.Type 12, .Type 13]) true false = .ok (some 12) := rfl
example : builtinDeref (adt #[.Type 12]) false true = .ok none := rfl
example : boxedType (adt #[.Lifetime .Erased]) true =
    .error "Box type has no first type argument" := rfl
