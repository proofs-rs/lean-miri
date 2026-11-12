import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error reason => throw (IO.userError reason)
private def check (value : Bool) (reason : String) : IO Unit :=
  unless value do throw (IO.userError reason)

/-- Synthetic constructor demands after a real document import. Shared children
must not be expanded exponentially, and overflow must be an actual result. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh material document")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source prefix absent")
  let initial := TypeArena.World.ofCheckedMaterial checked
  for depth in #[16,64] do
    let (top,world) ← must ((do
      let mut current := decoded.document.queries.primitives.bool
      for _ in [:depth] do current ← TypeArena.World.internType (.tuple #[current,current])
      pure current) initial)
    let start ← IO.monoNanosNow
    let result := (runtime.layoutInWorld top).run world
    match result with
    | .ok (actual,after) =>
      check (2^depth < runtime.target.base.objSizeBound.toNat && actual.layout.size.bytes.toNat == 2^depth)
        "shared tuple DAG returned an incorrect successful size"
      check (after.constructedTypes == world.constructedTypes && after.constructedConstants == world.constructedConstants)
        "layout answers escaped into the constructor universe"
      let (repeated,again) ← must ((runtime.layoutInWorld top).run world)
      check (repeated == actual && again.constructedTypes == world.constructedTypes)
        "independent repeated layout query changed answer or constructor identities"
    | .error reason =>
      check (2^depth >= runtime.target.base.objSizeBound.toNat && reason.contains "object-size")
        s!"shared tuple DAG failed for an unrelated reason: {reason}"
    let stop ← IO.monoNanosNow
    IO.println s!"PASS shared tuple DAG depth={depth}; constructor_nodes={world.constructedTypes.size}; query_ms={(stop-start)/1000000}; actual size/object-bound result"
