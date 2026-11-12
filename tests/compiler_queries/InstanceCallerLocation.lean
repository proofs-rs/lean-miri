import Miri.Input.CompilerRuntimeQueries

open Miri.Input Miri.Input.CompilerRuntimeQueries Miri.Interpreter

private def definitions : Array DefinitionId :=
  #[⟨0, 3, some true⟩, ⟨0, 4, some false⟩, ⟨0, 5, none⟩]

example : instanceRequiresCallerLocation definitions (.Item 0) = .ok true := by decide
example : instanceRequiresCallerLocation definitions (.Virtual 1 27) = .ok false := by decide
example : instanceRequiresCallerLocation definitions (.Shim (.VTable 0)) = .ok true := by decide
-- ClosureOnce's flag belongs to the shim, not either definition's attributes.
example : instanceRequiresCallerLocation definitions (.Shim (.ClosureOnce 1 1 true)) =
    .ok true := by decide
example : instanceRequiresCallerLocation definitions (.Shim (.ClosureOnce 0 0 false)) =
    .ok false := by decide
example : instanceRequiresCallerLocation definitions (.Intrinsic 0) = .ok false := by decide
example : instanceRequiresCallerLocation definitions (.LlvmIntrinsic 0) = .ok false := by decide
example : instanceRequiresCallerLocation definitions (.Shim (.Reify 0 none)) = .ok false := by decide
example : instanceRequiresCallerLocation definitions (.Shim (.DropGlue 0 (some 8))) =
    .ok false := by decide
example : instanceRequiresCallerLocation definitions (.Item 2) =
    .error "caller-location body codegen attribute material absent" := by decide
example : instanceRequiresCallerLocation definitions (.Item 3) =
    .error "caller-location definition material absent" := by decide
