import Miri.MIR.Syntax

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd:
rustc_middle/ty/generic_args.rs::rebase_onto and rustc_type_ir/predicate.rs
TraitRef::from_assoc, ExistentialTraitRef::{erase_self_ty,with_self_ty}.
This is argument-list rebasing; it does not substitute into types or binders. -/
namespace Miri.Input.GenericRebase
open Miri.MIR

def onto (args : Array GenericArg) (ancestorCount : Nat) (target : Array GenericArg) :
    Except String (Array GenericArg) := do
  unless ancestorCount ≤ args.size do throw "generic ancestor exceeds source argument count"
  return target ++ args.extract ancestorCount args.size

def virtualSelf (args : Array GenericArg) (parentCount : Nat) (concrete : TyId) :
    Except String (Array GenericArg) := do
  unless parentCount > 0 && parentCount ≤ args.size do
    throw "virtual trait generic material lacks Self or exceeds argument count"
  match args[0]? with
  | some (GenericArg.Type _) => pure ()
  | _ => throw "virtual trait Self argument is not a type"
  let target := #[GenericArg.Type concrete] ++ args.extract 1 parentCount
  onto args parentCount target

end Miri.Input.GenericRebase
