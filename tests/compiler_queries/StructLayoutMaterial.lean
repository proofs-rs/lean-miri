import Miri.Input.StructLayoutMaterial

open Miri.Input.GenericSubstitution Miri.Input.StructLayoutMaterial

example : guaranteedSized 4 (.node .type "array" "" (.cons (.parameter .type 0) .nil)) = true := rfl
example : guaranteedSized 4 (.node .type "reference" "" (.cons (.parameter .type 0) .nil)) = true := rfl
example : guaranteedSized 4 (.node .type "tuple" "" .nil) = true := rfl
example : guaranteedSized 4 (.node .type "tuple" "" (.cons (.parameter .type 0)
    (.cons (.atom .type "uint" "u32") .nil))) = true := rfl
example : guaranteedSized 4 (.parameter .type 0) = false := rfl
example : guaranteedSized 4 (.node .type "tuple" "" (.cons (.parameter .type 0) .nil)) = false := rfl
example : guaranteedSized 4 (.node .type "slice" "" (.cons (.atom .type "uint" "u8") .nil)) = false := rfl
example : guaranteedSized 0 (.atom .type "bool" "") = false := rfl
