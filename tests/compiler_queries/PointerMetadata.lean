import Miri.Input.StructuralPointerMetadata

open Miri.Input
private def adt (kind : AdtKind) (fields : Array AdtField) : TypeShape :=
  .adt {
    definition := 0, kind := kind,
    representation := {
      integer := none, alignBytes := none, packBytes := none,
      flagsBits := 0, scalableElement := none, fieldShuffleSeed := 0 },
    args := #[], variants := #[⟨0, "variant", fields⟩] }
private def shape : Nat → Except String TypeShape
  | 0 => .ok .bool
  | 1 => .ok .str
  | 2 => .ok (.slice 0)
  | 3 => .ok (.foreign 0)
  | 4 => .ok (.rawPointer 1 .Mut)
  | 5 => .ok (.tuple #[0, 1])
  | 6 => .ok (.dynamicTraitObject #[] none .Erased)
  | 7 => .ok (.alias .projection false 0 #[])
  | 8 => .ok (.unsafeBinder 0 #[])
  | 9 => .ok (.patternType 2 .notNull)
  | 10 => .ok (adt .structKind #[])
  | 11 => .ok (adt .structKind #[⟨0,"first",0⟩, ⟨1,"tail",1⟩])
  | 12 => .ok (adt .enumKind #[⟨0,"ignored",1⟩])
  | 13 => .ok (.tuple #[13])
  | _ => .error "missing material"

example : StructuralPointerMetadata.query shape (.ok ·) 5 0 = .ok .unit := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 1 = .ok .usize := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 2 = .ok .usize := by cbv
-- Extern types are unsized but have unit metadata; layout inference is wrong here.
example : StructuralPointerMetadata.query shape (.ok ·) 5 3 = .ok .unit := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 4 = .ok .unit := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 5 = .ok .usize := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 6 = .ok (.dynamic 6) := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 7 = .ok (.unresolved 7) := by cbv
example : StructuralPointerMetadata.query shape (fun id => .ok (if id == 7 then 1 else id)) 5 7 =
    .ok .usize := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 8 =
    .error "pointer metadata for unsafe binder is unimplemented upstream" := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 9 = .ok .usize := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 10 = .ok .unit := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 11 = .ok .usize := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 12 = .ok .unit := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 13 =
    .error "structural type tail recursion exhausted" := by cbv
example : StructuralPointerMetadata.query shape (.ok ·) 5 14 = .error "missing material" := by cbv
example : StructuralPointerMetadata.query shape (fun _ => .error "normalization failed") 5 0 =
    .error "normalization failed" := by cbv
