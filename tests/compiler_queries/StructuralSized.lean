import Miri.Input.StructuralSized

open Miri.Input Miri.Input.StructuralSized

private def adt (kind : AdtKind) (fields : Array Nat) : TypeShape :=
  .adt {
    definition := 0
    kind := kind
    representation := ⟨none, none, none, 0, none, 0⟩
    args := #[]
    variants := #[⟨0, "variant", fields.mapIdx fun index ty => ⟨index, "field", ty⟩⟩] }

private def shape (ty : Nat) : Except String TypeShape :=
  match ty with
  | 0 => .ok .bool
  | 1 => .ok .str
  | 2 => .ok (.slice 0)
  | 3 => .ok (.dynamicTraitObject #[] none .Erased)
  | 4 => .ok (.foreign 0)
  | 5 => .ok (.tuple #[])
  | 6 => .ok (.tuple #[0, 1])
  | 7 => .ok (adt .structKind #[0, 2])
  | 8 => .ok (adt .structKind #[])
  | 9 => .ok (adt .unionKind #[1])
  | 10 => .ok (adt .enumKind #[1])
  | 11 => .ok (.unsafeBinder 1 #[])
  | 12 => .ok (.patternType 1 .notNull)
  | 13 => .ok (.array 999 0 ⟨1, true⟩)
  | 14 => .ok (.rawPointer 1 .Mut)
  | 15 => .ok (adt .structKind #[15])
  | 16 => .ok (.alias .opaque 0 #[])
  | _ => .error "absent Sized material"

example : query shape 10 0 = .ok (some true) := by decide
example : query shape 10 1 = .ok (some false) := by decide
example : query shape 10 2 = .ok (some false) := by decide
example : query shape 10 3 = .ok (some false) := by decide
example : query shape 10 4 = .ok (some false) := by decide
example : query shape 10 5 = .ok (some true) := by decide
example : query shape 10 6 = .ok (some false) := by decide
example : query shape 10 7 = .ok (some false) := by decide
example : query shape 10 8 = .ok (some true) := by decide
example : query shape 10 9 = .ok (some true) := by decide
example : query shape 10 10 = .ok (some true) := by decide
-- Exact public-query fast paths: do not inspect or recurse into inner types.
example : query shape 10 11 = .ok (some true) := by decide
example : query shape 10 12 = .ok (some true) := by decide
example : query shape 10 13 = .ok (some true) := by decide
example : query shape 10 14 = .ok (some true) := by decide
example : query shape 3 15 = .error "structural Sized recursion exhausted" := by decide
example : query shape 10 16 = .ok none := by decide
example : query shape 10 999 = .error "absent Sized material" := by decide
