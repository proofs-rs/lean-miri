import Miri.Input.StructuralAutoTraits

open Miri.Input Miri.Input.StructuralAutoTraits

private def shapes (ty : TypeId) : Except String TypeShape :=
  match ty with
  | 0 => .ok .bool
  | 1 => .ok (.tuple #[0, 2])
  | 2 => .ok (.slice 0)
  | 3 => .ok (.reference 999 .Mut .Erased)
  | 4 => .ok (.tuple #[0, 5])
  | 5 => .ok (.foreign 0)
  | 6 => .ok (.slice 6)
  | _ => .error "absent material type"

example : trivial shapes 4 0 = .ok true := by decide
example : trivial shapes 4 1 = .ok true := by decide
example : trivial shapes 4 3 = .ok true := by decide
example : trivial shapes 4 4 = .ok false := by decide
example : trivial shapes 4 5 = .ok false := by decide
example : trivial shapes 4 6 = .error "structural auto-trait recursion exhausted" := by decide
example : trivial shapes 4 999 = .error "absent material type" := by decide
example : trivial shapes 0 0 = .error "structural auto-trait recursion exhausted" := by decide
