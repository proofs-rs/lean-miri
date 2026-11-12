import Miri.Input.StructuralNormalization

open Miri.Input Miri.Input.StructuralNormalization
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  { id, shape, display := "normalization test", layoutId := 0 }
private def nodes := #[node 0 .bool, node 1 (.rawPointer 0 .Mut),
  node 2 (.reference 1 .Not .Erased), node 3 (.tuple #[0, 2]),
  node 4 (.reference 0 .Not .Static), node 5 (.alias .projection 0 #[])]
example : identityReady nodes 5 3 = .ok true := by cbv
example : identityReady nodes 5 4 = .ok false := by cbv
example : identityReady nodes 5 5 = .ok false := by cbv
example : identityReady nodes 1 3 = .error "structural normalization traversal exhausted" := by cbv
example : identityReady nodes 5 6 = .error "structural normalization type is absent" := by cbv
example : identityReady #[node 0 (.rawPointer 0 .Mut)] 3 0 =
    .error "structural normalization traversal exhausted" := by cbv
