import Miri.Input.StructuralConstructedFacts

open Miri.Input
private def shape : Nat → Except String TypeShape
  | 0 => .ok .bool
  | 1 => .ok .never
  | 2 => .ok (.rawPointer 1 .Mut)
  | 3 => .ok (.reference 1 .Mut .Erased)
  | 4 => .ok (.array 3 0 ⟨0,true⟩)
  | 5 => .ok (.array 3 0 ⟨2,true⟩)
  | 6 => .ok (.reference 2 .Mut .Erased)
  | 7 => .ok (.rawPointer 7 .Mut)
  | 8 => .ok (.array 1 0 ⟨0,false⟩)
  | _ => .error "missing constructed shape"
private def material (id : Nat) (key : String) : Except String Bool :=
  if key == "opsem_inhabited" then pure (id == 0)
  else if key == "is_monomorphic_enough" then pure true
  else .error "unknown material query"
private def query (key : String) := StructuralConstructedFacts.query shape material 2 key 10

example : query "opsem_inhabited" 2 = .ok (some true) := by cbv
example : query "opsem_inhabited" 3 = .ok (some false) := by cbv
example : query "opsem_inhabited" 4 = .ok (some true) := by cbv
example : query "opsem_inhabited" 5 = .ok (some false) := by cbv
example : query "opsem_inhabited" 6 = .ok (some true) := by cbv
example : query "is_monomorphic_enough" 5 = .ok (some true) := by cbv
example : StructuralConstructedFacts.query shape (fun _ _ => .ok false) 2
    "is_monomorphic_enough" 10 6 = .ok (some false) := by cbv
example : query "is_monomorphic_enough" 7 =
    .error "constructed compiler fact recursion exhausted" := by cbv
example : query "opsem_inhabited" 8 =
    .error "constructed array lacks canonical value-length material" := by cbv
example : query "opsem_inhabited" 9 = .error "missing constructed shape" := by cbv
example : query "unknown" 2 = .ok none := by cbv
