import Miri.Input.TraitSelection.Match

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error a, .error b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok _, .error _ => .isFalse (by intro same; cases same)
  | .error _, .ok _ => .isFalse (by intro same; cases same)

private def traitId : DefinitionIdentity := ⟨1, 9⟩
private def u32 : Term := .atom .type "uint" "u32"
private def u64 : Term := .atom .type "uint" "u64"
private def pair (a b : Term) : Term := .node .type "tuple" "" (.ofArray #[a,b])
private def declaration (parameters : Array ArgSort) (arguments : Array Term) : Impl := {
  definition := ⟨1, 20⟩, parameters, traitRef := ⟨traitId, arguments⟩,
  polarity := .positive, isDefault := false, predicates := #[], associatedValues := #[] }
private def repeated : Impl := declaration #[.type] #[pair (.parameter .type 0) (.parameter .type 0)]

example : Match.head 30 repeated ⟨traitId, #[pair u32 u32]⟩ = .ok (some #[some u32]) := by decide +kernel
example : Match.head 30 repeated ⟨traitId, #[pair u32 u64]⟩ = .ok none := by decide +kernel
example : Match.head 30 repeated ⟨⟨2,9⟩, #[pair u32 u32]⟩ = .ok none := by decide +kernel
example : Match.head 30 (declaration #[.type] #[.parameter .type 1]) ⟨traitId, #[u32]⟩ =
    .error "impl parameter index out of bounds" := by decide +kernel
example : Match.head 30 (declaration #[.constant] #[.parameter .type 0]) ⟨traitId, #[u32]⟩ =
    .error "impl parameter sort disagrees with declaration" := by decide +kernel
example : Match.head 30 repeated ⟨traitId, #[pair (.inference .type 0) u32]⟩ =
    .error "trait matching requires a ground query" := by decide +kernel
example : Match.head 30 (declaration #[] #[.inference .type 0]) ⟨traitId, #[u32]⟩ =
    .error "inference variable in raw impl declaration" := by decide +kernel
example : Match.head 30 (declaration #[.type] #[.parameter .type 0])
    ⟨traitId, #[.binder #[] u32]⟩ = .error "trait matching requires a ground query" := by decide +kernel
example : Match.head 30 (declaration #[] #[.binder #[] u32]) ⟨traitId, #[u32]⟩ =
    .error "higher-ranked impl-head relation requires universe checking" := by decide +kernel
example : Match.head 30 (declaration #[.type] #[.parameter .type 0])
    ⟨traitId, #[.definition .type "alias_projection_not_rigid" ⟨0,5⟩ .nil]⟩ =
    .error "trait matching requires normalized aliases" := by decide +kernel
example : Match.head 30 (declaration #[] #[.definition .type "alias_projection_not_rigid" ⟨0,5⟩ .nil])
    ⟨traitId, #[u32]⟩ = .error "impl projection requires deferred normalization" := by decide +kernel
example : Match.head 30 (declaration #[] #[.atom .region "static" ""])
    ⟨traitId, #[.atom .region "erased" ""]⟩ = .ok none := by decide +kernel
example : Match.head 30 (declaration #[] #[.atom .region "static" ""])
    ⟨traitId, #[.atom .region "erased" ""]⟩ true = .ok (some #[]) := by decide +kernel
example : Match.complete #[.type] true #[none] =
    .error "impl parameter remains unconstrained" := by decide +kernel
example : Match.complete #[.region] false #[none] =
    .error "impl parameter remains unconstrained" := by decide +kernel
example : Match.complete #[.region] true #[none] =
    .ok #[.atom .region "erased" ""] := by decide +kernel

private def item (argument : Term) (variables : Array BoundVariable := #[]) : Term :=
  .definition .type "function_definition" ⟨1,44⟩ (.ofArray #[
    .binder variables (.node .aggregate "arguments" "" (.ofArray #[argument]))])
example : Match.head 50 (declaration #[.type] #[item (.parameter .type 0)])
    ⟨traitId, #[item u32]⟩ = .ok (some #[some u32]) := by decide +kernel
example : Match.head 50 (declaration #[] #[item u32])
    ⟨traitId, #[item u64]⟩ = .ok none := by decide +kernel
example : Match.head 50 (declaration #[] #[item u32])
    ⟨traitId, #[item u32 #[.region .anonymous]]⟩ =
    .error "trait matching requires a ground query" := by decide +kernel
