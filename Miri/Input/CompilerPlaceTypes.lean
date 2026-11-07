import Miri.Input.CompilerFrameContext

namespace Miri.Input.CompilerPlaceTypes
open Miri.ABI Miri.Interpreter Miri.Memory

def expectedLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.PlaceId) : Except String LocalLayout := do
  let _ ← CompilerFrameContext.bodyOfFrame p frame
  let some types := p.program.input.mirTables.normalization[frame.bodyIdentity.index]?
    | throw "canonical body place types absent"
  let id ← (← types).places.lookup requested.index |>.mapError (fun id => s!"place {id} has no compiler normalization evidence in this body")
  p.runtime.lookup id |>.mapError toString

private def localLayout (p : CompilerProviders.Prepared) (frame : CompilerFrameContext.ActualFrame)
    (requested : MIR.Place) : Except String LocalLayout := do
  let mut ty ← CompilerFrameContext.normalizedLocalType p frame requested.localId
  for projection in requested.projection do
    ty ← match projection with
      | .Field _ fieldType | .OpaqueCast fieldType | .UnwrapUnsafeBinder fieldType => pure fieldType
      | .Deref | .Index _ | .ConstantIndex .. => do
        let some node := p.program.input.types[ty]? | throw "local projection type absent"
        let next := if projection == .Deref then node.relations.pointee else node.relations.element
        let some next := next | throw "local projection compiler type absent"
        pure next
      | .Downcast .. => pure ty
      | .Subslice .. | .PhantomDeref => throw "unsupported synthetic local projection"
  p.runtime.lookup ty |>.mapError toString

private def checkLayout (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (expected actual : LocalLayout) : MachineHooks.M K U Unit := do
  let related ← if expected.ty == actual.ty then pure true else relateCovariantly expected actual
  unless related do throw (.invalidProgram "MIR place compiler type differs from evaluated place type")
  unless expected.layout == actual.layout do
    throw (.invalidProgram "MIR covariant assignment has different compiler layouts")

def operand (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.PlaceId) (actual : LocalLayout) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← match expectedLayout p (← MachineHooks.currentFrame) requested with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler place type query: {reason}")
  checkLayout relateCovariantly expected actual

-- Argument initialization constructs local places rather than referencing MIR nodes.
def dynamicPlace (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (relateCovariantly : LocalLayout → LocalLayout → MachineHooks.M K U Bool)
    (_ : C) (requested : MIR.Place) (value : RuntimePlace Provenance) : MachineHooks.M K U Unit := do
  if !debugAssertions then return
  let expected ← match localLayout p (← MachineHooks.currentFrame) requested with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler local place type query: {reason}")
  checkLayout relateCovariantly expected value.layout

end Miri.Input.CompilerPlaceTypes
