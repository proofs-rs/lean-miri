import Miri.Input.AllocationImage

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def node (id : Nat) (payload : Json := .null) : AllocationNode := {
  id, status := .supported, kind := .typeId,
  memory := none, data := some (.typeId id), payload }

private def malformed : Json := Id.run do
  let emptyTree : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) := .leaf
  let duplicate := Std.DTreeMap.Internal.Impl.inner 1 "status" (.str "different") emptyTree emptyTree
  let root := Std.DTreeMap.Internal.Impl.inner 2 "status" (.str "first") emptyTree duplicate
  return .obj ⟨⟨root⟩⟩

def main : IO Unit := do
  let ordinary := node 1 (Json.mkObj [("test", .str "value")])
  let hidden := { node 2 with status := .unsupported }
  let bad := node 3 malformed
  check (!(malformed == malformed)) "malformed control unexpectedly compares equal to itself"
  let owners : Array (Array AllocationNode) := #[#[], #[ordinary], #[ordinary, hidden],
    #[hidden, ordinary, ordinary], #[bad], #[ordinary, bad]]
  for owner in owners do
    let source := owner.filter (·.status == .supported)
    let binding := AllocationImage.SupportedSourceBinding.prepare source owner rfl
    let cached := AllocationImage.Imported.withSourceIndex source #[] (some binding)
    let plain := AllocationImage.Imported.ofSource source #[]
    for candidate in owners.push (owner.map fun value => { value with id := value.id + 10 }) do
      check (cached.matchesSupportedSource candidate == plain.matchesSupportedSource candidate)
        "cached image ownership changed the historical full comparison"
    let independent := owner.map fun value =>
      { value with payload := (Json.parse value.payload.compress).toOption.getD value.payload }
    check (cached.matchesSupportedSource independent == plain.matchesSupportedSource independent)
      "independently reconstructed values changed the full comparison"
  IO.println "supported allocation binding: owners, foreign/mutated arrays, duplicates and nonreflexive JSON PASS"
