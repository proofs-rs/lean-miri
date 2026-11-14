import Miri.Input.TermAutoTraits
open Miri.Input.GenericSubstitution Miri.Input.TermAutoTraits
private def byteTy : Term := .atom .type "uint" "u8"
private def adtTy : Term := .definition .type "adt" ⟨0,1⟩ .nil
example : trivial 10 (.node .type "raw_pointer" "mutable" (.cons adtTy .nil)) = .ok true := by cbv
example : trivial 10 (.node .type "reference" "immutable"
    (.cons (.atom .region "erased" "") (.cons adtTy .nil))) = .ok true := by cbv
example : trivial 10 (.node .type "tuple" "" (.cons byteTy (.cons adtTy .nil))) = .ok false := by cbv
example : trivial 10 (.node .type "tuple" "" (.cons byteTy (.cons byteTy .nil))) = .ok true := by cbv
example : trivial 10 (.node .type "slice" "" (.cons adtTy .nil)) = .ok false := by cbv
example : trivial 10 (.node .type "array" "" (.cons byteTy (.cons (.atom .constant "value" "") .nil))) =
    .ok true := by cbv
example : trivial 10 adtTy = .ok false := by cbv
example : trivial 0 byteTy = .error "term auto-trait traversal exhausted" := by cbv
