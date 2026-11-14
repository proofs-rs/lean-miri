import Miri.Input.TermSized
open Miri.Input GenericSubstitution TermSized
private def sourceTemplate : DefinitionTemplate := {
  parameters := #[.type], typeExpression := .parameter .type 0,
  signatureExpression := none,
  fields := #[⟨0,0,.atom .type "uint" "u8"⟩,⟨0,1,.parameter .type 0⟩] }
private def hooks : Hooks := {
  sourceAdt := fun identity =>
    if identity.index == 1 then pure (.structKind,sourceTemplate)
    else if identity.index == 2 then pure (.enumKind,sourceTemplate)
    else throw "source ADT absent",
  normalizeAlias := fun _ _ => pure (.atom .type "str" "") }
private def adt (index : Nat) (argument : Term) : Term :=
  .definition .type "adt" ⟨0,index⟩ (.cons argument .nil)
private def strTy : Term := .atom .type "str" ""
private def byteTy : Term := .atom .type "uint" "u8"
example : query hooks .sized 20 (adt 1 strTy) = .ok false := by cbv
example : query hooks .metaSized 20 (adt 1 strTy) = .ok true := by cbv
example : query hooks .sized 20 (adt 1 byteTy) = .ok true := by cbv
example : query hooks .sized 20 (adt 1 (adt 1 strTy)) = .ok false := by cbv
example : query hooks .sized 20 (adt 2 strTy) = .ok true := by cbv
example : query hooks .sized 20 (.node .type "tuple" "" (.cons byteTy (.cons strTy .nil))) =
    .ok false := by cbv
example : query hooks .metaSized 20 (.node .type "slice" "" (.cons byteTy .nil)) =
    .ok true := by cbv
example : query hooks .sized 20 (.node .type "raw_pointer" "mutable" (.cons strTy .nil)) =
    .ok true := by cbv
example : query hooks .metaSized 20 (.definition .type "foreign" ⟨0,99⟩ .nil) =
    .ok false := by cbv
example : query hooks .sized 20 (.node .type "unsafe_binder" "" (.cons strTy .nil)) =
    .error "term Sized trait candidate requires unsafe-binder relation semantics" := by cbv
example : query hooks .sized 20 (adt 3 strTy) = .error "source ADT absent" := by cbv
example : query hooks .sized 20 (.parameter .type 0) =
    .error "term Sized requires a concrete type expression" := by cbv
example : query hooks .sized 0 byteTy = .error "term Sized recursion exhausted" := by cbv
example : query {hooks with sourceAdt := fun _ => pure (.structKind,
    {sourceTemplate with fields := #[⟨0,1,.parameter .type 0⟩]})} .sized 20 (adt 1 strTy) =
    .error "struct Sized source field domain is not dense" := by cbv
