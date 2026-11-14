import Miri.Input.TypeArenaWorld

open Miri.Input Miri.Input.TypeArena
private def node (id : Nat) (shape : TypeShape) : TypeNode :=
  {id,shape,display := "constructor test",layoutId := 0}
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main : IO Unit := do
  let initial ← must (World.ofMaterial #[node 0 .bool,node 1 (.rawPointer 0 .Mut),
    node 2 (.reference 0 .Mut .Erased)] #[] #[] #[] 8)
  let (pointer,world) ← must ((World.internType (.rawPointer 0 .Mut)).run initial)
  let (reference,world) ← must ((World.internType (.reference 0 .Mut .Erased)).run world)
  unless pointer == 1 && reference == 2 && world.constructedTypes.isEmpty do
    throw (IO.userError "exact material constructors were not reused")
  let (nested,world) ← must ((World.internType (.reference reference .Mut .Erased)).run world)
  unless nested == 3 do throw (IO.userError "nested reference was not allocated densely")
  let (immutable,world) ← must ((World.internType (.rawPointer 0 .Not)).run world)
  let (staticRef,world) ← must ((World.internType (.reference 0 .Mut .Static)).run world)
  unless immutable != pointer && staticRef != reference do
    throw (IO.userError "constructor mutability or lifetime identity was erased")
  let ambiguous ← must (World.ofMaterial #[node 0 .bool,node 1 (.rawPointer 0 .Mut),
    node 2 (.rawPointer 0 .Mut)] #[] #[] #[] 8)
  match (World.internType (.rawPointer 0 .Mut)).run ambiguous with
  | .error "ambiguous canonical type universe material identity" => pure ()
  | _ => throw (IO.userError "duplicate material identity was accepted")
  unless world.constructedTypes.size == 3 do throw (IO.userError "constructor state was not retained")
  IO.println "PASS exact material reuse, nested construction, mutability/lifetimes and ambiguity guard"
