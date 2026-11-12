import Miri.Input.CompilerRuntimeQueries

open Miri.Input Miri.Input.CompilerRuntimeQueries
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  { id, shape, display := "constructor test", layoutId := 0 }
private def nodes := #[node 0 .bool, node 1 (.rawPointer 0 .Mut),
  node 2 (.reference 0 .Mut .Erased)]

example : internConstructor nodes 0 false = .ok 1 := by cbv
example : internConstructor nodes 0 true = .ok 2 := by cbv
-- The reference to a reference is genuinely new: no material result node exists.
example : internConstructor nodes 2 true = .ok 10 := by cbv
example : (TypeArena.node nodes 10).map (fun n => match n.shape with
    | .reference child .Mut .Erased => some child | _ => none) = .ok (some 2) := by cbv
example : internConstructor #[node 0 .bool, node 1 (.rawPointer 0 .Not)] 0 false =
    .ok 2 := by cbv
example : internConstructor #[node 0 .bool, node 1 (.reference 0 .Mut .Static)] 0 true =
    .ok 3 := by cbv
example : internConstructor #[] 3 false =
    .error "lazy type arena requires a material universe" := by cbv
example : internConstructor #[node 0 .bool, node 1 (.rawPointer 0 .Mut),
    node 2 (.rawPointer 0 .Mut)] 0 false =
    .error "ambiguous material type constructor identity" := by cbv
