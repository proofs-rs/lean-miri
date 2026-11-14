import Miri.Input.GenericRebase

open Miri.Input.GenericRebase Miri.MIR

-- Rebasing preserves lifetime and const arguments verbatim, including bound
-- indices. It changes the argument prefix, not occurrences within types.
example : onto #[.Type 1, .Lifetime .Erased, .Const 4] 2 #[.Type 9] =
    .ok #[.Type 9, .Const 4] := rfl
example : virtualSelf #[.Type 1, .Lifetime .Erased, .Const 4, .Type 5] 3 9 =
    .ok #[.Type 9, .Lifetime .Erased, .Const 4, .Type 5] := rfl
example : virtualSelf #[.Type 1] 1 9 = .ok #[.Type 9] := rfl
example : virtualSelf #[] 0 9 =
    .error "virtual trait generic material lacks Self or exceeds argument count" := rfl
example : virtualSelf #[.Lifetime .Erased] 1 9 =
    .error "virtual trait Self argument is not a type" := rfl
example : onto #[.Type 1] 2 #[] =
    .error "generic ancestor exceeds source argument count" := rfl
