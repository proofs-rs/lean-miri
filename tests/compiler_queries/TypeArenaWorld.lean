import Miri.Input.TypeArenaWorld

/-! Execution-owned constructor storage controls, not compiler-layout or trait
solver correspondence. Repeated children and recursive declarations never grow
identity payloads or eagerly expand fields. -/
open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def representation : ReprOptions := {
  integer := none, alignBytes := none, packBytes := none,
  flagsBits := 0, scalableElement := none, fieldShuffleSeed := 0 }
private def template : DefinitionTemplate := {
  parameters := #[.type], typeExpression := .definition .type "adt" ⟨1,7⟩ (.cons (.parameter .type 0) .nil),
  signatureExpression := none,
  fields := #[⟨0,0,.node .type "raw_pointer" "mutable"
    (.cons (.definition .type "adt" ⟨1,7⟩ (.cons (.parameter .type 0) .nil)) .nil)⟩] }
private def sourceTypes : Array TypeNode := #[
  {id := 0, display := "same", layoutId := 0, shape := .uint (.known .u32)},
  {id := 1, display := "same", layoutId := 0, shape := .uint (.known .u8)},
  {id := 2, display := "same", layoutId := 0, shape := .tuple #[0,1]},
  {id := 3, display := "same", layoutId := 0, shape := .adt {
    definition := 0, kind := .structKind, args := #[.Type 0], variants := #[], representation }}]
private def rejected (result : Except String α) : Bool :=
  match result with | .error _ => true | .ok _ => false

def main : IO Unit := do
  let initial ← must (World.ofMaterial sourceTypes #[] #[{crateIndex := 1,index := 7,genericTemplate := some template}] #[] 8)
  let (material,unchanged) ← must ((World.internType (.tuple #[0,1])).run initial)
  unless material == 2 && unchanged.constructedTypes.isEmpty do
    throw (IO.userError "material tuple was not reused exactly")
  let (adt,world) ← must ((World.internType (.adt ⟨1,7⟩ #[.Type 1])).run unchanged)
  unless adt == sourceTypes.size do throw (IO.userError "novel ADT did not receive next dense ID")
  unless rejected (initial.lookupType adt) do throw (IO.userError "initial world leaked a future type")
  let (pointer,world) ← must ((World.internType (.rawPointer adt .Mut)).run world)
  let (.constructed (.rawPointer child .Mut)) ← must (world.lookupType pointer)
    | throw (IO.userError "recursive ADT field pointer lost its constructor")
  unless child == adt && world.constructedTypes.size == 2 do
    throw (IO.userError "recursive ADT identity expanded its field declaration")
  let (again,persistent) ← must ((World.internType (.adt ⟨1,7⟩ #[.Type 1])).run world)
  unless again == adt && persistent.constructedTypes.size == world.constructedTypes.size do
    throw (IO.userError "repeat construction changed canonical identity")
  let mut world := persistent
  let mut root := pointer
  for _ in [:64] do
    let (next,updated) ← must ((World.internType (.tuple #[root,root])).run world)
    root := next
    world := updated
  unless world.constructedTypes.size == 66 && root < 100 do
    throw (IO.userError "repeated-child DAG grew identity payloads or duplicated constructor nodes")
  let edges := world.constructedTypes.foldl (fun total constructor => total + constructor.typeChildren.size) 0
  unless edges == 130 do throw (IO.userError "constructor graph storage is not linear in unique edges")
  unless rejected ((World.internType (.tuple #[world.typeCount])).run world) do
    throw (IO.userError "absent child ID was accepted as an old algebraic encoding")
  let (_,constantWorld) ← must ((World.internConstant (.Value 0 ⟨#[.Leaf 7 4],0⟩)).run world)
  unless constantWorld.constructedConstants.size == 1 && world.constructedConstants.isEmpty do
    throw (IO.userError "constant construction did not preserve persistent state")
  unless rejected ((World.internConstant (.Value world.typeCount ⟨#[.Leaf 7 4],0⟩)).run world) do
    throw (IO.userError "constant with absent type was accepted")
  IO.println s!"PASS dense persistent type universe, exact material reuse, recursive ADT identity and 64-level shared DAG; nodes={world.constructedTypes.size}; edges={edges}; max_id={root}"
