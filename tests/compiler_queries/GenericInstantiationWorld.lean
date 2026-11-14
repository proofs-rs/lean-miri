import Miri.Input.GenericInstantiationWorld

/-! Constructor tests use deliberately small raw declarations, not compiled
layout/trait answers. Deep DAG reification/construction must share syntax within
one traversal and preserve the same execution-owned universe. -/
open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def adtTemplate : DefinitionTemplate := {
  parameters := #[.type], typeExpression := .definition .type "adt" ⟨1,7⟩ (.cons (.parameter .type 0) .nil),
  signatureExpression := none, fields := #[⟨0,0,.node .type "raw_pointer" "mutable"
    (.cons (.definition .type "adt" ⟨1,7⟩ (.cons (.parameter .type 0) .nil)) .nil)⟩] }
private def fnTemplate : DefinitionTemplate := {
  parameters := #[.type], typeExpression := .definition .type "function_definition" ⟨1,8⟩
    (.cons (.binder #[] (.node .aggregate "arguments" "" (.cons (.parameter .type 0) .nil))) .nil),
  signatureExpression := none, fields := #[] }
private def types : Array TypeNode := #[
  {id := 0, display := "same", layoutId := 0, shape := .uint (.known .u32)},
  {id := 1, display := "same", layoutId := 0, shape := .uint (.known .u8)},
  {id := 2, display := "same", layoutId := 0, shape := .uint (.known .usize)}]

def main : IO Unit := do
  let initial ← must (World.ofMaterial types #[] #[
    {crateIndex := 1,index := 7,genericTemplate := some adtTemplate},
    {crateIndex := 1,index := 8,genericTemplate := some fnTemplate}] #[] 8)
  let u8 := Term.atom .type "uint" "u8"
  let pair := Term.node .type "tuple" "" (.cons u8 (.cons u8 .nil))
  let nominal := Term.definition .type "adt" ⟨1,7⟩ (.cons pair .nil)
  let (adt,world) ← must ((GenericInstantiationWorld.resolveType 1024 nominal).run initial)
  unless adt == 4 && world.constructedTypes.size == 2 do
    throw (IO.userError "novel tuple/ADT did not share exact dense constructor IDs")
  let rawField ← must (GenericInstantiationWorld.instantiateFieldTerm world 1024 ⟨1,7⟩ #[.Type 3] 0 0)
  let (pointer,world) ← must ((GenericInstantiationWorld.resolveType 1024 rawField).run world)
  let .constructed (.rawPointer child .Mut) ← must (world.lookupType pointer)
    | throw (IO.userError "raw recursive field constructor was lost")
  unless child == adt do throw (IO.userError "recursive ADT field made a second nominal identity")
  let function := Term.definition .type "function_definition" ⟨1,8⟩
    (.cons (.binder #[] (.node .aggregate "arguments" "" (.cons pair .nil))) .nil)
  let (fnId,world) ← must ((GenericInstantiationWorld.resolveType 1024 function).run world)
  unless (← must (GenericInstantiationWorld.ofType world 1024 fnId)) == function do
    throw (IO.userError "novel FnDef lost raw definition/complete type arguments")
  let mut world := world
  let mut root := fnId
  for _ in [:64] do
    let (next,updated) ← must ((World.internType (.tuple #[root,root])).run world)
    root := next
    world := updated
  let raw ← must (GenericInstantiationWorld.ofType world 1024 root)
  let (again,retained) ← must ((GenericInstantiationWorld.resolveType 1024 raw).run world)
  unless again == root && retained.constructedTypes.size == world.constructedTypes.size do
    throw (IO.userError "64-level AST DAG roundtrip expanded or changed canonical identity")
  let array := Term.node .type "array" "" (.cons pair (.cons
    (.node .constant "value" "" (.cons (.atom .type "uint" "usize")
      (.cons (.atom .aggregate "scalar" "{\"bytes\":8,\"bits\":3}") .nil))) .nil))
  let (arrayId,retained) ← must ((GenericInstantiationWorld.resolveType 1024 array).run retained)
  unless (← must (GenericInstantiationWorld.ofType retained 1024 arrayId)) == array do
    throw (IO.userError "novel array raw constant/value identity failed to roundtrip")
  unless retained.constructedConstants.size == 1 do throw (IO.userError "raw constant syntax was not interned once")
  IO.println s!"PASS World generic tuple/ADT/FnDef/array synthesis and 64-level shared AST roundtrip; nodes={retained.constructedTypes.size}; max_id={arrayId}"
