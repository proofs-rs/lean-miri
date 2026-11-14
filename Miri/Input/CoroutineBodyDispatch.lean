import Miri.Input.GenericSubstitution

namespace Miri.Input.CoroutineBodyDispatch
open GenericSubstitution

/-- Pinned rustc_middle/src/ty/mod.rs ordinary_coroutine_layout. This dispatch
only chooses a raw MIR owner; it neither supplies nor verifies its saved fields.
Async-drop shims are a different source provider and remain rejected. -/
inductive Kind where
  | regular | fnShared | fnMut | fnOnce
  deriving BEq, Repr

/-- Pinned `Ty::to_opt_closure_kind`: unresolved generic/inference kind types
have no physical body choice in this source-only provider. -/
def kindOfTerm : Term → Except String Kind
  | .node .type "tuple" "" .nil => .ok .regular
  | .atom .type "int" "i8" => .ok .fnShared
  | .atom .type "int" "i16" => .ok .fnMut
  | .atom .type "int" "i32" => .ok .fnOnce
  | _ => .error "coroutine kind source term unresolved or malformed"

inductive Family where
  | ordinary | asyncDrop
  deriving BEq, Repr

structure Source where
  owner : DefinitionIdentity
  identityKind : Kind
  byMoveOwner : Option DefinitionIdentity
  family : Family

def select (source : Source) (requested : Kind) : Except String DefinitionIdentity := do
  unless source.family == .ordinary do
    throw "async-drop coroutine requires shim/empty-proxy source provider"
  if requested == .regular || requested == source.identityKind then
    pure source.owner
  else
    unless requested == .fnOnce &&
        (source.identityKind == .fnShared || source.identityKind == .fnMut) do
      throw "coroutine kind differs outside pinned by-move transition"
    let some owner := source.byMoveOwner |
      throw "coroutine by-move raw body owner missing"
    unless owner != source.owner do
      throw "coroutine by-move raw body owner aliases ordinary owner"
    pure owner

end Miri.Input.CoroutineBodyDispatch
