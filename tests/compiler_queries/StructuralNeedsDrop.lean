import Miri.Input.StructuralNeedsDrop

open Miri.Input Miri.Input.StructuralNeedsDrop

private def adt (definition : Nat) (kind : AdtKind) (fields : Array Nat) : TypeShape :=
  .adt {
    definition := definition
    kind := kind
    representation := ⟨none, none, none, 0, none, 0⟩
    args := #[]
    variants := #[⟨0, "variant", fields.mapIdx fun index ty => ⟨index, "field", ty⟩⟩] }

private def shape (ty : Nat) : Except String TypeShape :=
  match ty with
  | 0 => .ok .bool
  | 1 => .ok (.dynamicTraitObject #[] none .Erased)
  | 2 => .ok (adt 0 .structKind #[1])
  | 3 => .ok (adt 1 .structKind #[1])
  | 4 => .ok (adt 2 .structKind #[0])
  | 5 => .ok (adt 2 .unionKind #[1])
  | 6 => .ok (.array 1 0 ⟨0, true⟩)
  | 7 => .ok (.array 1 0 ⟨1, true⟩)
  | 8 => .ok (.tuple #[0, 2])
  | 9 => .ok (.rawPointer 1 .Mut)
  | 10 => .ok (.slice 10)
  | 11 => .ok (.unsafeBinder 0 #[])
  | 12 => .ok (.tuple #[0, 11])
  | 13 => .ok (.tuple #[1, 11])
  | 14 => .ok (.closure 0 #[.Type 0, .Type 0, .Type 8] 2)
  | 15 => .ok (.closure 0 #[.Type 0, .Type 0, .Type 0] 0)
  | 16 => .ok (.coroutineClosure 0 #[.Type 0, .Type 0, .Type 8, .Type 0])
  | 17 => .ok (.coroutine 0 #[])
  | _ => .error "absent shape material"

private def material (definition : Nat) : Except String AdtMaterial :=
  match definition with
  | 0 => .ok ⟨false, none⟩
  | 1 => .ok ⟨true, none⟩
  | 2 => .ok ⟨false, some 3⟩
  | _ => .error "absent ADT material"

example : query shape material 10 0 = .ok (some false) := by decide
example : query shape material 10 1 = .ok (some true) := by decide
example : query shape material 10 2 = .ok (some true) := by decide
example : query shape material 10 3 = .ok (some false) := by decide
example : query shape material 10 4 = .ok (some true) := by decide
-- A union with a destructor still has drop: check destructor before union.
example : query shape material 10 5 = .ok (some true) := by decide
example : query shape (fun _ => .ok ⟨false, none⟩) 10 5 = .ok (some false) := by decide
example : query shape material 10 6 = .ok (some false) := by decide
example : query shape material 10 7 = .ok (some true) := by decide
example : query shape material 10 8 = .ok (some true) := by decide
example : query shape material 10 9 = .ok (some false) := by decide
example : query shape material 3 10 = .error "structural needs_drop recursion exhausted" := by decide
example : query shape material 10 11 = .ok none := by decide
example : query shape material 10 12 = .ok none := by decide
example : query shape material 10 13 = .ok (some true) := by decide
example : query shape material 10 999 = .error "absent shape material" := by decide
example : query shape (fun _ => .error "absent ADT material") 10 2 =
    .error "absent ADT material" := by decide

example : query shape material 10 14 = .ok (some true) := by decide
example : query shape material 10 15 = .error "closure upvar material is not a tuple" := by decide
example : query shape material 10 16 = .ok (some true) := by decide
example : query shape material 10 17 = .ok (some true) := by decide

-- A shared type graph has only 41 distinct nodes; recursively expanding both
-- tuple edges without demand-local memoization would visit over 2^40 leaves.
private def sharedGraph (id : Nat) : Except String TypeShape :=
  if id == 0 then .ok .bool else .ok (.tuple #[id - 1, id - 1])

#eval (do
  let result := query sharedGraph (fun _ => .error "unexpected ADT demand") 42 40
  unless result == (Except.ok (some false) : Except String (Option Bool)) do
    throw (IO.userError "shared needs_drop graph did not resolve to no drop")
  : IO Unit)

-- Exact source-kind rule, independent of function argument/signature binders.
example : StructuralNeedsDrop.knownKindResult .functionDefinition = some false := by decide +kernel
example : StructuralNeedsDrop.knownKindResult .functionPointer = some false := by decide +kernel
example : StructuralNeedsDrop.knownKindResult .adt = none := by decide +kernel
