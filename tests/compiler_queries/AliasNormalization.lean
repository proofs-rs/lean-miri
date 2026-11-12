import Miri.Input.AliasNormalization

open Miri.Input.GenericSubstitution Miri.Input.AliasNormalization
open Miri.Input.TraitSelection (Clause Predicate)
private def ident (index : Nat) : DefinitionIdentity := ⟨0,index⟩
private def boolean : Term := .atom .type "bool" ""
private def unsigned : Term := .atom .type "uint" "u32"
private def alias (kind : String) (id : Nat) (args : Array Term := #[]) : Term :=
  .definition .type kind (ident id) (Terms.ofArray args)
private def rule (id : Nat) (parameters : Array ArgSort) (body : Term)
    (predicates : Array Clause := #[]) : Rule :=
  {definition := ident id,
   template := {parameters, typeExpression := body, signatureExpression := none, fields := #[]},
   ownPredicates := predicates}
private def rules : Array Rule := #[
  rule 1 #[.type] (.node .type "slice" "" (.cons (.parameter .type 0) .nil)),
  rule 2 #[.type] boolean,
  rule 3 #[] (alias "alias_free_not_rigid" 3)]
private def associatedRule : Rule := rule 11 #[.type,.type] (.node .type "tuple" ""
  (.cons (.parameter .type 0) (.cons (.parameter .type 1) .nil)))
private def associated : AssociatedValue := {
  traitDefinition := ident 10, rule := some associatedRule, requiresHiddenTypeInference := false, materialRetained := true }
private def program : Program := {
  freeRules := rules,
  associatedDeclarations := #[⟨ident 10, ident 100, 1, #[]⟩] }
private def isUnsigned : Term → Bool
  | .atom .type "uint" "u32" => true
  | _ => false
private def isRequirement (value : Clause) : Bool :=
  value.variables.isEmpty && match value.predicate with
    | .wellFormed (.atom .type "uint" "u32") => true
    | _ => false
private def hooks : Hooks := {
  select := fun _ _ kind parent args =>
    if kind == .projection && parent == ident 100 && args.size == 1 && args[0]?.any isUnsigned then
      .ok ⟨ident 200, #[unsigned], #[associated]⟩
    else .error "no implementation",
  fulfill := fun _ _ predicates =>
    if predicates.isEmpty then .ok () else .error "unproved own clauses" }

-- Finite component checks use explicit fixture selection, not a trait solver.
example : normalize program hooks 20 #[] (alias "alias_free_not_rigid" 1 #[unsigned]) =
    .ok (.node .type "slice" "" (.cons unsigned .nil)) := by cbv
-- rustc does not normalize unused free-alias arguments before substituting RHS.
example : normalize program hooks 20 #[]
    (alias "alias_free_not_rigid" 2 #[alias "alias_free_not_rigid" 3]) = .ok boolean := by cbv
example : normalize program hooks 20 #[] (alias "alias_free_not_rigid" 3) =
    .error "alias normalization cycle" := by cbv
example : normalize program hooks 20 #[] (alias "alias_projection_not_rigid" 10 #[unsigned,boolean]) =
    .ok (.node .type "tuple" "" (.cons unsigned (.cons boolean .nil))) := by cbv
example : normalize program {hooks with select := fun _ _ _ _ _ => .error "ambiguous implementation"}
    20 #[] (alias "alias_projection_not_rigid" 10 #[unsigned,boolean]) =
    .error "ambiguous implementation" := by cbv
example : normalize program hooks 0 #[] boolean =
    .error "alias normalization recursion exhausted" := by cbv
example : normalize program hooks 20 #[] (alias "alias_projection_rigid" 10 #[unsigned]) =
    .error "rigid or unknown alias requires its solver mode and environment" := by cbv
example : normalize program hooks 20 #[] (alias "alias_opaque_not_rigid" 10 #[unsigned]) =
    .error "opaque normalization requires hidden-type constraint inference" := by cbv
example : normalize program hooks 20 #[] (alias "alias_free_not_rigid" 1 #[]) =
    .error "generic template argument count mismatch" := by cbv
example : normalize program hooks 20 #[] (alias "alias_free_not_rigid" 1 #[.atom .region "erased" ""]) =
    .error "generic template argument sort mismatch" := by cbv
private def requirement : Clause := ⟨#[], .wellFormed unsigned⟩
private def ownProgram : Program := {
  program with freeRules := #[rule 1 #[] boolean #[requirement]] }
example : normalize ownProgram hooks 20 #[] (alias "alias_free_not_rigid" 1) =
    .error "unproved own clauses" := by cbv
example : normalize ownProgram {hooks with fulfill := fun _ _ predicates =>
    if predicates.size == 1 && predicates[0]?.any isRequirement then .ok () else .error "wrong clauses"}
    20 #[] (alias "alias_free_not_rigid" 1) = .ok boolean := by cbv
example : normalize program hooks 20 #[] (.inference .type 0) =
    .error "alias normalization received unresolved inference material" := by cbv

private def sourceImpl : Miri.Input.TraitSelection.Impl := {
  definition := ident 200, parameters := #[.type],
  traitRef := ⟨ident 100, #[.parameter .type 0]⟩,
  polarity := .positive, isDefault := false, predicates := #[],
  associatedValues := #[{
    traitAssociatedDefinition := ident 10, implementationDefinition := ident 11,
    expression := some associatedRule.template, requiresHiddenTypeInference := false, materialRetained := true,
    ownPredicates := #[]}] }
example : (fromTraitSelection sourceImpl ⟨ident 200, #[unsigned]⟩).map
    (fun selected => selected.associatedValues.size) = .ok 1 := by cbv
example : (fromTraitSelection sourceImpl ⟨ident 201, #[unsigned]⟩).map
    (fun selected => selected.associatedValues.size) =
    .error "associated selection does not identify its raw implementation" := by cbv
example : (fromTraitSelection {sourceImpl with polarity := .negative}
    ⟨ident 200, #[unsigned]⟩).map (fun selected => selected.associatedValues.size) =
    .error "associated selection is not a positive implementation" := by cbv
example : (fromTraitSelection sourceImpl ⟨ident 200, #[]⟩).map
    (fun selected => selected.associatedValues.size) =
    .error "associated selection substitution count mismatch" := by cbv
example : (fromTraitSelection sourceImpl ⟨ident 200, #[.atom .region "erased" ""]⟩).map
    (fun selected => selected.associatedValues.size) =
    .error "associated selection substitution sort mismatch" := by cbv
private def hiddenValue : AssociatedValue := {
  traitDefinition := ident 10, rule := none, requiresHiddenTypeInference := true, materialRetained := true }
private def hiddenSelection : SelectedImpl := ⟨ident 200, #[unsigned], #[hiddenValue]⟩
example : normalize program {hooks with select := fun _ _ _ _ _ => .ok hiddenSelection}
    20 #[] (alias "alias_projection_not_rigid" 10 #[unsigned,boolean]) =
    .error "associated RHS requires hidden-type constraint inference" := by cbv

private def sliceUnsigned : Term := .node .type "slice" "" (.cons unsigned .nil)
private def projectionClauses : Program := {
  program with associatedDeclarations := #[⟨ident 10, ident 100, 1,
    #[⟨#[], .wellFormed (.parameter .type 0)⟩]⟩] }
private def isSliceUnsigned : Term → Bool
  | .node .type "slice" "" (.cons (.atom .type "uint" "u32") .nil) => true
  | _ => false
private def projectionHooks : Hooks := {
  select := fun _ _ _ parent args =>
    if parent == ident 100 && args.size == 1 && args[0]?.any isSliceUnsigned then
      .ok ⟨ident 200, #[unsigned], #[associated]⟩
    else .error "wrong trait arguments",
  fulfill := fun _ _ predicates =>
    if predicates.size == 1 && (predicates[0]?.any fun clause => match clause.predicate with
      | .wellFormed value => isSliceUnsigned value | _ => false)
    then .ok () else .error "trait own clauses used impl substitutions" }
-- Trait Self=[T] differs from impl T. Own GAT clauses use the projection args;
-- the selected RHS uses impl T plus GAT arguments. These are separate folds.
example : normalize projectionClauses projectionHooks 30 #[]
    (alias "alias_projection_not_rigid" 10 #[sliceUnsigned,boolean]) =
    .ok (.node .type "tuple" "" (.cons unsigned (.cons boolean .nil))) := by cbv

-- A zero-variable metadata Binder does not require placeholder conversion;
-- source own-clause obligations still reach the query-boundary fulfiller.
example : normalize ownProgram {hooks with fulfill := fun _ _ predicates =>
    if predicates.size == 1 && predicates[0]?.any isRequirement then .ok () else .error "wrong clauses"}
    20 #[] (.binder #[] (alias "alias_free_not_rigid" 1)) =
    .ok (.binder #[] boolean) := by cbv
