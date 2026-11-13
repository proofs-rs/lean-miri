import Miri.Input.TypeArenaPredicateWorld

open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def rejects (value : Except String A) (message : String) : IO Unit :=
  if value.isOk then throw (IO.userError message) else pure ()
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  {id,shape,display := "predicate arena control",layoutId := 0}
private def raw : VtablePredicate :=
  {kind := .trait,definitionId := 0,definitionPath := none,genericArgs := #[],boundVariables := #[],projectionTerm := none}
private def principal : DynamicPredicate.Predicate := ⟨#[],.trait ⟨0,8⟩ #[]⟩

def main : IO Unit := do
  let definitions : Array DefinitionId := #[{crateIndex := 0,index := 8},{crateIndex := 0,index := 9}]
  let material ← must (World.ofMaterial #[node 0 (.uint (.known .u8))] #[] definitions #[raw] 8)
  let (id,reused) ← must ((World.internExistential principal).run material)
  check (id == 0 && reused.constructedPredicates.isEmpty && reused.materialPredicates == material.materialPredicates)
    "material predicate identity or immutable prefix was changed"
  let empty ← must (World.ofMaterial #[] #[] definitions #[] 8)
  let (first,world) ← must ((World.internExistential principal).run empty)
  check (first == 0 && world.predicateCount == 1 && world.materialPredicates.isEmpty &&
    world.typeCount == 0 && world.constantCount == 0) "fresh predicate suffix is not dense and execution owned"
  let (same,world) ← must ((World.internExistential principal).run world)
  check (same == first && world.predicateCount == 1 && (← must (world.existential first)) == principal)
    "complete repeated predicate identity did not reuse the dense suffix"
  rejects (world.existential 1) "absent predicate handle was accepted"
  rejects (world.materialKey (node 0 (.dynamicTraitObject #[first] (some first) .Erased)))
    "constructed predicate handle masqueraded as a material predicate index"
  let (byte,world) ← must ((World.internType (.integer false .u8)).run world)
  let (constant,world) ← must ((World.internConstant
    (.Value byte ⟨#[.Leaf 42 1],0⟩)).run world)
  let typeProjection : DynamicPredicate.Predicate := ⟨#[],.projection ⟨0,9⟩ #[] (.type byte)⟩
  let constProjection : DynamicPredicate.Predicate := ⟨#[],.projection ⟨0,9⟩ #[] (.constant constant)⟩
  let (typeId,world) ← must ((World.internExistential typeProjection).run world)
  let (constId,world) ← must ((World.internExistential constProjection).run world)
  check (typeId != constId && (← must (world.existential typeId)) == typeProjection &&
    (← must (world.existential constId)) == constProjection) "Type/Const projection domains were merged"
  let bound : DynamicPredicate.Predicate := ⟨#[.region .anonymous],.trait ⟨0,8⟩
    #[.Lifetime (.Bound (.Bound 0) 0 .Anon)]⟩
  let (_,world) ← must ((World.internExistential bound).run world)
  let (reference,world) ← must ((World.internType (.reference byte .Not (.Bound (.Bound 0) 0 .Anon))).run world)
  let nested : DynamicPredicate.Predicate := ⟨#[.region .anonymous],.trait ⟨0,8⟩ #[.Type reference]⟩
  let (_,world) ← must ((World.internExistential nested).run world)
  let (pointer,world) ← must ((World.internType (.functionPointer {
    variables := #[.region .anonymous],abiPacked := Miri.ABI.ExternAbi.asPacked .Rust,
    safe := true,cVariadic := false,splatted := none,inputs := #[reference],output := byte})).run world)
  let nestedBinder : DynamicPredicate.Predicate := ⟨#[],.trait ⟨0,8⟩ #[.Type pointer]⟩
  let (_,world) ← must ((World.internExistential nestedBinder).run world)
  rejects ((World.internExistential {principal with body := .trait ⟨0,99⟩ #[]}).run world)
    "missing predicate physical owner was accepted"
  rejects ((World.internExistential {principal with body := .trait ⟨0,8⟩ #[.Type world.typeCount]}).run world)
    "dangling predicate type argument was accepted"
  rejects ((World.internExistential {principal with body := .trait ⟨0,8⟩ #[.Const world.constantCount]}).run world)
    "dangling predicate constant argument was accepted"
  rejects ((World.internExistential {bound with body := (.trait ⟨0,8⟩ #[.Lifetime (.Bound (.Bound 0) 1 .Anon)])}).run world) "out-of-bounds local predicate binder was accepted"
  rejects ((World.internExistential {principal with body := (.trait ⟨0,8⟩ #[.Lifetime (.Bound (.Bound 0) 0 .Anon)])}).run world) "escaping predicate region was accepted"
  rejects ((World.internExistential {principal with variables := #[.type .anonymous]}).run world)
    "unsupported type predicate binder created a handle"
  rejects ((World.internExistential {principal with variables := #[.constant]}).run world)
    "unsupported constant predicate binder created a handle"
  let mismatch : DynamicPredicate.Predicate := ⟨#[.region (.named ⟨0,8⟩)],.trait ⟨0,8⟩
    #[.Lifetime (.Bound (.Bound 0) 0 (.Named 1))]⟩
  rejects ((World.internExistential mismatch).run world) "predicate binder physical identity mismatch was accepted"
  rejects ((World.internExistential principal 0).run world) "predicate validation ignored exhausted fuel"
  let (same,syntaxReused) ← must ((World.internExistentialSyntax principal).run world)
  check (same == first && syntaxReused.predicateCount == world.predicateCount)
    "core-checked syntax insertion created a duplicate suffix identity"
  rejects (World.ofMaterial #[] #[] definitions #[raw,raw] 8)
    "duplicate material predicate source entered the immutable prefix"
  check (world.materialPredicates.isEmpty) "constructed predicate tests acquired material predicate rows"
  IO.println "PASS execution-owned predicate suffix, exact prefix/repeat reuse, distinct Type/Const projections, nested binder ownership and malformed/missing/domain/fuel/duplicate controls"
