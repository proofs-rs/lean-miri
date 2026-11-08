import Miri.Input.CompilerRuntimeQueries

open Lean Miri.Input.CompilerVirtualCandidates

private def source : Json := Json.mkObj [
  ("schema_version", toJson (1 : Nat)),
  ("by_instance", .arr #[
    toJson (#[0, 2] : Array Nat), .null, .null, .null, .null, .null, .null,
    .str "malformed unused row",
    toJson (#[1, 1] : Array Nat),
    toJson (#[2, 0] : Array Nat),
    toJson (#[3] : Array Nat),
    .arr #[.bool true],
    toJson (#[] : Array Nat)])]


#guard ((ofJson source).lookup 0 13 3).toOption == some #[0, 2]
#guard ((ofJson source).requireMember 0 13 2 3).isOk
#guard !((ofJson source).requireMember 0 13 1 3).isOk
#guard !((ofJson source).lookup 1 13 3).isOk
#guard !((ofJson source).lookup 7 13 3).isOk
#guard !((ofJson source).lookup 8 13 3).isOk
#guard !((ofJson source).lookup 9 13 3).isOk
#guard !((ofJson source).lookup 10 13 3).isOk
#guard !((ofJson source).lookup 11 13 3).isOk
#guard ((ofJson source).lookup 12 13 3).toOption == some #[]
#guard !((ofJson source).requireMember 12 13 0 3).isOk
#guard !((ofJson .null).lookup 0 13 3).isOk


private def query (id input : Nat) (predicates : Array Nat) : Json :=
  Json.mkObj [("query_id", toJson id),
    ("input_type", Json.mkObj [("type_id", toJson input)]),
    ("input_predicates", .arr (predicates.map fun id => Json.mkObj [("predicate_id", toJson id)]))]

private def queries : Array Json := #[query 0 7 #[2], .str "unused malformed query", query 2 9 #[]]

#guard ((ofJson source).query 0 13 queries (query 0 7 #[2])).isOk
#guard ((ofJson source).query 0 13 queries (query 2 9 #[])).isOk
#guard !((ofJson source).query 0 13 queries (query 0 7 #[3])).isOk
#guard !((ofJson source).query 0 13 queries (query 0 8 #[2])).isOk
#guard !((ofJson source).query 0 13 queries (Json.mkObj [("query_id", toJson (0 : Nat))])).isOk
#guard !((ofJson source).query 0 13 queries (query 1 7 #[2])).isOk
#guard !((ofJson source).query 0 13 (queries.set! 0 (query 1 7 #[2])) (query 0 7 #[2])).isOk
#guard !((ofJson source).query 0 13 (queries.set! 0 (Json.mkObj [("query_id", toJson (0 : Nat))])) (query 0 7 #[2])).isOk


open Miri.Input Miri.Interpreter

private def document (raw : Json) : ImportDocumentCore := {
  producer := ⟨"miri", "rustc", "version", "target"⟩
  types := #[], allocations := #[]
  instances := (Array.range 13).map fun id => {
    id := id, kind := .virtualDispatchTarget
    defPath := none, definitionId := none, bodyInstantiation := none
    bodyTemplateIsPolymorphic := none, instanceArgsAreMonomorphic := none
    body := none, promotedBodies := #[], payload := .null }
  selectedScope := none, functionAbis := #[], bodies := #[]
  raw := raw }

private def callee : CallInstance := ⟨.Item 99, #[]⟩
private def virtualEntry : CompilerRuntimeQueries.VirtualEntry := {
  original := ⟨.Virtual 17 0, #[]⟩
  methodDefinition := 17, parentTrait := 12, concreteType := 7
  rebasedArgs := #[], resolved := .ok callee
  sourceInstanceId := 0, queryReference := query 0 7 #[2] }

private def prepared (index : Json := source) (entries := #[virtualEntry]) :
    CompilerRuntimeQueries.Prepared := {
  program := ⟨⟨#[], #[], #[], #[]⟩, #[], #[], #[], document (Json.mkObj [
    ("compiler_virtual_candidates", index), ("compiler_vtable_queries", .arr queries)])⟩
  types := #[], callerLocation := #[], virtualQueries := entries }

#guard (CompilerRuntimeQueries.parentTrait prepared 17).toOption == some 12
#guard (CompilerRuntimeQueries.rebaseVirtualArgs prepared #[] 12 7).toOption == some #[]
#guard (CompilerRuntimeQueries.expectResolveForVTable prepared 17 #[]).toOption == some callee
#guard !(CompilerRuntimeQueries.parentTrait (prepared .null) 17).isOk
#guard !(CompilerRuntimeQueries.rebaseVirtualArgs (prepared .null) #[] 12 7).isOk
#guard !(CompilerRuntimeQueries.expectResolveForVTable (prepared .null) 17 #[]).isOk
#guard !(CompilerRuntimeQueries.parentTrait (prepared source #[{virtualEntry with concreteType := 8}]) 17).isOk

-- An unrelated virtual instance's malformed candidate row is not demanded.
#guard (CompilerRuntimeQueries.expectResolveForVTable (prepared source #[virtualEntry,
  {virtualEntry with sourceInstanceId := 7, methodDefinition := 18}]) 17 #[]).toOption == some callee

#guard !((ofJson source).lookup 0 12 3).isOk
#guard !((ofJson source).lookup 13 13 3).isOk

private def permutedInstances : CompilerRuntimeQueries.Prepared :=
  let value := prepared
  { value with program := { value.program with input := { value.program.input with
      instances := value.program.input.instances.reverse } } }

#guard (CompilerRuntimeQueries.expectResolveForVTable permutedInstances 17 #[]).toOption == some callee
#guard !(CompilerRuntimeQueries.expectResolveForVTable
  (prepared source #[{virtualEntry with sourceInstanceId := 13}]) 17 #[]).isOk
