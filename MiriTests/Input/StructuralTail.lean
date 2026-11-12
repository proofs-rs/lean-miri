import Miri.Input.StructuralTail

open Miri.Input

private def shape : Nat → Except String TypeShape
  | 0 => .ok (.tuple #[1, 2])
  | 1 => .ok .bool
  | 2 => .ok (.tuple #[3])
  | 3 => .ok .str
  | 4 => .ok (.tuple #[])
  | 5 => .ok (.tuple #[5])
  | _ => .error "missing material"

example : StructuralTail.tail shape (.ok ·) 5 0 = .ok 3 := rfl
example : StructuralTail.tail shape (.ok ·) 5 4 = .ok 4 := rfl
example : StructuralTail.tail shape (.ok ·) 5 5 =
    .error "structural type tail recursion exhausted" := rfl
example : StructuralTail.tail shape (.ok ·) 5 6 = .error "missing material" := rfl
