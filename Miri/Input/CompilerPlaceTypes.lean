import Miri.Input.CompilerFrameContext

/-! Exact debug-only place/operand type checks, place.rs:626–643 and
operand.rs:805–830. The resolved executable body supplies each expected
place type. Runtime projection/layouts never substitute for that query. -/
namespace Miri.Input.CompilerPlaceTypes
open Lean Miri.ABI Miri.Interpreter Miri.Memory

def expectedLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.Place) : TypeArena.WorldM LocalLayout := do
  let body ← CompilerFrameContext.bodyOfFrame p frame
  -- rustc Place::ty begins with the source local declaration. No compiler
  -- query-result row is needed for a place with no projection elements.
  if requested.projection.isEmpty then
    let some id := body.body.locals[requested.localId]?
      | throw "place local is absent from its executable body"
    return ← RuntimeMetadata.layoutInWorld p.runtime id
  let mut ids := #[]
  for block in body.input.nodeFacts do
    for node in block do
      for place in node.places do
        if place.place == requested then ids := ids.push place.typeId
  let some id := ids[0]? | throw "place has no compiler type in its executable body"
  unless ids.all (· == id) do throw "same place has conflicting compiler types"
  RuntimeMetadata.layoutInWorld p.runtime id

def check (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (requested : MIR.Place) (actual : LocalLayout) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← RuntimeArrayQueries.perform types
    (expectedLayout p (← MachineHooks.currentFrame) requested)
  let related ← if expected.ty == actual.ty then pure true else relateCovariantly expected actual
  unless related do throw (.invalidProgram "MIR place compiler type differs from evaluated place type")
  unless expected.layout == actual.layout do
    throw (.invalidProgram "MIR covariant assignment has different compiler layouts")

def operand (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : OpTy Provenance) : MachineHooks.M K U Unit :=
  check p types debugAssertions relateCovariantly requested value.layout

def place (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : RuntimePlace Provenance) : MachineHooks.M K U Unit :=
  check p types debugAssertions relateCovariantly requested value.layout
end Miri.Input.CompilerPlaceTypes
