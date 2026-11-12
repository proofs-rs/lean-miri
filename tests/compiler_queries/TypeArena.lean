import Miri.Input.TypeArenaWorld

open Miri.Input Miri.Input.TypeArena
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  {id,shape,display := "arena test",layoutId := 0}
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main : IO Unit := do
  let initial ← must (World.ofMaterial #[node 0 .bool,node 1 (.uint (.known .usize))] #[] #[] 8)
  let (length,world) ← must ((World.internConstant (.Value 1 ⟨#[.Leaf 4 8],0⟩)).run initial)
  let (array,world) ← must ((World.internType (.array 0 length)).run world)
  let (pointer,world) ← must ((World.internType (.rawPointer array .Mut)).run world)
  let (reference,world) ← must ((World.internType (.reference pointer .Mut .Erased)).run world)
  unless array == 2 && pointer == 3 && reference == 4 do
    throw (IO.userError "constructors did not receive disjoint dense appended IDs")
  let .constructed (.array child constant) ← must (world.lookupType array)
    | throw (IO.userError "array constructor was lost")
  unless child == 0 && constant == length do throw (IO.userError "array child/constant identity changed")
  let .constructed (.reference child .Mut .Erased) ← must (world.lookupType reference)
    | throw (IO.userError "reference constructor was lost")
  unless child == pointer do throw (IO.userError "nested child identity changed")
  let (again,retained) ← must ((World.internType (.array 0 length)).run world)
  unless again == array && retained.constructedTypes.size == 3 do
    throw (IO.userError "repeat construction duplicated canonical syntax")
  if (initial.lookupType array).isOk then throw (IO.userError "initial prefix leaked appended type")
  if (World.ofMaterial #[node 1 .bool] #[] #[] 8).isOk then throw (IO.userError "bad dense prefix accepted")
  if ((World.internType (.tuple #[world.typeCount])).run world).isOk then
    throw (IO.userError "out-of-range ID was interpreted as an old implicit encoding")
  IO.println "PASS dense persistent array/pointer/reference identities and strict source bounds"
