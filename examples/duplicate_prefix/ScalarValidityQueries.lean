import duplicate_prefix.RootMetadataQueries
import duplicate_prefix.CopyCompilerFacts
import Miri.Input.CompilerFactAdapters

namespace DuplicatePrefix.ScalarValidityQueries
open Miri Miri.Input Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

open Lean Elab Tactic in
elab "unfold_validity_query_helpers" : tactic => do
  let names ← ([".CompilerFactAdapters.shape", ".CompilerFactAdapters.source"] : List String).mapM fun (suffix : String) => do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| unfold $[$names:ident]*))

theorem usize_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 5 = .ok .integer := by
  unfold CompilerFactAdapters.validityKind
  unfold_validity_query_helpers
  dsimp only
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 5 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 5 :=
    RootMetadataQueries.context_node 5
  simp only [node]
  with_unfolding_all rfl

theorem bool_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 0 = .ok .boolean := by
  unfold CompilerFactAdapters.validityKind
  unfold_validity_query_helpers
  dsimp only
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 0 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 0 :=
    RootMetadataQueries.context_node 0
  simp only [node]
  with_unfolding_all rfl

theorem hooks_usize_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 5 = pure .integer := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [usize_kind]
  with_unfolding_all rfl

theorem hooks_bool_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 0 = pure .boolean := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [bool_kind]
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "unfold_validity_source" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".CompilerFactAdapters.source" : String) then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected exact source type node helper"

theorem hooks_usize_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 5 = pure "usize" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 5 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 5 :=
    RootMetadataQueries.context_node 5
  rw [node]
  with_unfolding_all rfl

theorem hooks_bool_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 0 = pure "bool" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 0 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 0 :=
    RootMetadataQueries.context_node 0
  rw [node]
  with_unfolding_all rfl

theorem byte_sized : CompilerFacts.boolean
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 1 "is_sized" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 1 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 1 :=
    RootMetadataQueries.context_node 1
  simp only [node]
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "unfold_raw_validity_helpers" : tactic => do
  let names ← ([".CompilerFactAdapters.shape", ".CompilerFactAdapters.typeRef", ".CompilerFactAdapters.source"] : List String).mapM fun (suffix : String) => do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| unfold $[$names:ident]*))

theorem mut_pointer_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 8 = .ok (.rawPointer 1 true) := by
  unfold CompilerFactAdapters.validityKind
  unfold_raw_validity_helpers
  dsimp only
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  change (do
    let sized ← CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 1 "is_sized"
    pure (ValidityVisitor.TypeKind.rawPointer 1 sized)) = .ok (ValidityVisitor.TypeKind.rawPointer 1 true)
  rw [byte_sized]
  rfl

theorem const_pointer_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 9 = .ok (.rawPointer 1 true) := by
  unfold CompilerFactAdapters.validityKind
  unfold_raw_validity_helpers
  dsimp only
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  change (do
    let sized ← CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 1 "is_sized"
    pure (ValidityVisitor.TypeKind.rawPointer 1 sized)) = .ok (ValidityVisitor.TypeKind.rawPointer 1 true)
  rw [byte_sized]
  rfl

theorem hooks_mut_pointer_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 8 = pure (.rawPointer 1 true) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [mut_pointer_kind]
  with_unfolding_all rfl

theorem hooks_mut_pointer_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 8 = pure "*mut u8" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 8 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 8 :=
    RootMetadataQueries.context_node 8
  rw [node]
  with_unfolding_all rfl

theorem hooks_const_pointer_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 9 = pure (.rawPointer 1 true) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [const_pointer_kind]
  with_unfolding_all rfl

theorem hooks_const_pointer_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 9 = pure "*const u8" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 9 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 9 :=
    RootMetadataQueries.context_node 9
  rw [node]
  with_unfolding_all rfl

#print axioms byte_sized
#print axioms mut_pointer_kind
#print axioms const_pointer_kind

#print axioms hooks_usize_name
#print axioms hooks_bool_name
open Lean Elab Command in
run_cmd do
  for declaration in [``hooks_mut_pointer_kind, ``hooks_mut_pointer_name, ``hooks_const_pointer_kind, ``hooks_const_pointer_name, ``byte_sized, ``mut_pointer_kind, ``const_pointer_kind, ``usize_kind, ``bool_kind, ``hooks_usize_kind, ``hooks_bool_kind,
      ``hooks_usize_name, ``hooks_bool_name] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

#print axioms usize_kind
#print axioms bool_kind
end DuplicatePrefix.ScalarValidityQueries
