import Miri.Input.StructuralDiscriminantType
open Miri.Input StructuralDiscriminantType
private def representation : ReprOptions := ⟨none,none,none,0,none,0⟩
example : enumKey {representation with integer := some (.fixed (.known .i8) 16 true)} =
    .error "enum discriminant repr integer width mismatch" := by cbv
example : enumKey {representation with integer := some (.fixed (.known .isize) 64 true)} =
    .error "enum discriminant repr integer width mismatch" := by cbv
private def hooks : Hooks := {
  shape := fun id => match id with
    | 0 => pure .bool
    | 1 => pure (.coroutine 0 #[])
    | 2 => pure (.patternType 1 .notNull)
    | 3 => pure (.unsafeBinder 0 #[])
    | 4 => pure (.alias .free false 0 #[])
    | _ => throw "type absent",
  primitive := fun key => if key == "u8" then pure 8 else if key == "u32" then pure 32
    else throw "primitive absent",
  normalizeAlias := fun _ _ => pure 2,
  eraseUnsafeBinder := fun _ => throw "residual binder erasure absent" }
example : query hooks 8 2 = .ok 32 := by cbv
example : query hooks 8 4 = .ok 32 := by cbv
example : query hooks 8 3 = .error "residual binder erasure absent" := by cbv
example : query {hooks with normalizeAlias := fun _ id => pure id} 8 4 =
    .error "discriminant type alias remained unresolved" := by cbv
example : query {hooks with eraseUnsafeBinder := fun _ => pure 0} 8 3 = .ok 8 := by cbv
example : query hooks 0 2 = .error "discriminant type traversal exhausted" := by cbv
example : query hooks 8 99 = .error "type absent" := by cbv
