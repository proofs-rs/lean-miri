import Miri.Input.CompilerFrameContext

/-! Exact debug-only place/operand type checks, place.rs:626–643 and
operand.rs:805–830. The compiler's instantiated body supplies each expected
place type. Runtime projection/layouts never substitute for that query. -/
namespace Miri.Input.CompilerPlaceTypes
open Lean Miri.ABI Miri.Interpreter Miri.Memory

def expectedLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.Place) : Except String LocalLayout := do
  let source ← CompilerFrameContext.bodyOfFrame p frame
  let normalized ← CompilerFrameContext.normalizedBody p frame
  let mut ids := #[]
  for (block, blockIndex) in source.input.nodeFacts.toList.zipIdx do
    let some actualBlock := normalized.nodeFacts[blockIndex]? | throw "normalized block is absent"
    for (node, instructionIndex) in block.toList.zipIdx do
      let some actualNode := actualBlock[instructionIndex]? | throw "normalized instruction is absent"
      for place in node.places do
        if place.place == requested then
          let some actual := actualNode.places.find? (·.path == place.path)
            | throw "normalized place site is absent"
          ids := ids.push actual.typeId
  let some id := ids[0]? | throw "place has no exact compiler normalization evidence in canonical body"
  unless ids.all (· == id) do throw "same source place has conflicting normalized compiler types"
  p.runtime.lookup id |>.mapError toString

def check (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (requested : MIR.Place) (actual : LocalLayout) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← match expectedLayout p (← MachineHooks.currentFrame) requested with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler place type query: {reason}")
  let related ← if expected.ty == actual.ty then pure true else relateCovariantly expected actual
  unless related do throw (.invalidProgram "MIR place compiler type differs from evaluated place type")
  unless expected.layout == actual.layout do
    throw (.invalidProgram "MIR covariant assignment has different compiler layouts")

def operand (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : OpTy Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout

def place (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : RuntimePlace Provenance) : MachineHooks.M K U Unit :=
  check p debugAssertions relateCovariantly requested value.layout
end Miri.Input.CompilerPlaceTypes
