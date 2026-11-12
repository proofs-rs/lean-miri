import Miri.Input.TypeArena

open Miri.Input
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  { id, shape, display := "arena test", layoutId := 0 }
private def material := #[node 0 .bool]
private def arrayId := TypeArena.arrayId material.size 0 4
private def pointerId := TypeArena.constructedId material.size arrayId false
private def referenceId := TypeArena.constructedId material.size pointerId true

example : TypeArena.internArray material 0 4 = .ok arrayId := by cbv
example : TypeArena.intern material arrayId false = .ok pointerId := by cbv
example : TypeArena.intern material pointerId true = .ok referenceId := by cbv
example : (TypeArena.node material arrayId 10).map (fun n => match n.shape with
    | .array child length constructor => some (child, length, constructor.count)
    | _ => none) = .ok (some (0, 14, 4)) := by cbv
example : (TypeArena.node material pointerId).map (fun n => match n.shape with
    | .rawPointer child .Mut => some child | _ => none) = .ok (some arrayId) := by cbv
example : (TypeArena.node material referenceId).map (fun n => match n.shape with
    | .reference child .Mut .Erased => some child | _ => none) = .ok (some pointerId) := by cbv
-- Pointer/reference and array constructors occupy disjoint tags.
example : pointerId != arrayId := by cbv
example : TypeArena.internArray material 0 4 = TypeArena.internArray material 0 4 := rfl
example : (TypeArena.node #[node 1 .bool] 1).map (·.id) = .error "material type ID/index mismatch" := by cbv
example : (TypeArena.node #[node 0 .bool, node 0 .bool] 2).map (·.id) =
    .error "material type ID/index mismatch" := by cbv
example : TypeArena.internArray material (TypeArena.constructedId 1 0 false) 3 =
    .ok (TypeArena.arrayId 1 (TypeArena.constructedId 1 0 false) 3) := by cbv
