import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceFunctionTypes
import Miri.Input.SourceSignatureTypes
import Miri.Input.Decoder
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unsupported FnDef material accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "usage: source schema12")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile sourcePath))))
  let seed ← checked (compilerEntrySeed document)
  let some source := seed.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some abi := source.abi | throw (IO.userError "source headers absent")
  let oracle := (← checked (Input.decodeJson (← IO.FS.readFile oraclePath))).document
  let mut world ← checked (SourceCompilerWorld.create {oracle with sourceMaterial := some source})
  let mut count := 0
  for node in oracle.types do
    if let .functionDefinition definition args signature bound := node.shape then
      if args.isEmpty then
        let some raw := oracle.definitions[definition]? | throw (IO.userError "oracle definition absent")
        if let some header := abi.functions.find? (·.definition == raw) then
          unless header.signature.inputs.size == signature.inputs.size do throw (IO.userError "signature input count")
          for (reference,expected) in header.signature.inputs.zip signature.inputs do
            let (updated,actual) ← checked (SourceSignatureTypes.intern world #[] #[] header.signature.boundVariables reference)
            world := updated
            unless actual == expected do throw (IO.userError s!"original bound signature input identity differs {actual}/{expected}")
          let (updated,actual) ← checked (SourceSignatureTypes.intern world #[] #[] header.signature.boundVariables header.signature.output)
          world := updated
          unless actual == signature.output do throw (IO.userError "original signature output identity differs")
          let (updated,actualBound) ← checked (SourceSignatureTypes.boundVariables world header.signature.boundVariables)
          world := updated
          unless bound == actualBound do throw (IO.userError "original binder identity")
          let some physical := source.physical | throw (IO.userError "source types absent")
          let sourceRef := physical.types.findIdx? fun (expression : SourceTypes.Expr) => match expression with
            | .functionDefinition definition arguments =>
              arguments.isEmpty && (physical.definitions[definition]?.map (·.raw)) == some raw
            | _ => false
          let some sourceRef := sourceRef | throw (IO.userError "source FnDef type absent")
          let (updated,actual) ← checked (SourceFunctionTypes.internSource world sourceRef #[] #[])
          world := updated
          unless actual == node.id do throw (IO.userError "complete original FnDef type/layout identity differs")
          let (same,again) ← checked (SourceFunctionTypes.internSource world sourceRef #[] #[])
          unless again == actual && same.canonical.types.size == world.canonical.types.size do
            throw (IO.userError "FnDef demand is not idempotent")
          rejects (SourceFunctionTypes.internSource
            {world with canonical := {world.canonical with sourceMaterial := some {source with abi := none}}}
            sourceRef #[] #[])
          if !header.signature.boundVariables.isEmpty then
            let some input := header.signature.inputs[0]? | throw (IO.userError "bound input absent")
            rejects (SourceSignatureTypes.intern world #[] #[] #[] input)
          count := count + 1
  unless count > 0 do throw (IO.userError "no matching genuine FnDef signature")
  unless world.canonical.instances.size == oracle.instances.size && world.canonical.bodies.size == oracle.bodies.size &&
      world.canonical.allocations.size == oracle.allocations.size do throw (IO.userError "FnDef type demand manufactured capabilities")
  IO.println s!"PASS {count} genuine original signature child identities and full erased layouts"
