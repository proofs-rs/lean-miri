import Miri.Input.Decoder
import Miri.Input.CompilerCopy
import Miri.Input.CompilerDiscriminantFacts

/-! Real fresh source-MIR types exercise stateful scalar consumers. The final
padding controls intentionally corrupt physical sizes to distinguish declared
pointer kind from an identical physical ScalarPair description. -/
open Miri.Input Miri.Interpreter Miri.ABI
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def arrayMust (result : Except RuntimeArrayTypes.Error α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError (reprStr error))
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ value => value⟩
private def run (action : EStateM StepError RuntimeArrayTypes.World α)
    (world : RuntimeArrayTypes.World) : IO (α × RuntimeArrayTypes.World) := do
  match action world with
  | .ok result world => pure (result,world)
  | .error error _ => throw (IO.userError (reprStr error))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh novel tuple/ADT input")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let program ← must (lowerProgram document)
  let context : CompilerFacts.Context := {runtime,program}
  let initial ← arrayMust (RuntimeArrayTypes.create runtime)
  let some index := document.bodies.findIdx? (fun seed => match seed with
    | .copyTemplate reference => match document.mirTemplates[reference.templateId]? with
      | some source => source.defPath.endsWith "local_types"
      | none => false
    | _ => false) | throw (IO.userError "source template missing")
  let (body,world) ← arrayMust (RuntimeArrayTypes.perform initial (SourceMir.resolveBody document index))
  let some tuple := body.mir.locals.find? (fun ty => ty >= document.types.size &&
    (world.arena.shapeKind ty).toOption == some .tuple) | throw (IO.userError "novel tuple missing")
  let some adt := body.mir.locals.find? (fun ty => ty >= document.types.size &&
    (world.arena.shapeKind ty).toOption == some .adt) | throw (IO.userError "novel ADT missing")
  let ((),world) ← arrayMust (RuntimeArrayTypes.perform world do
    for ty in #[tuple,adt] do
      unless (← CompilerDiscriminantFacts.discriminantValue context ty 0).isNone do
        throw "ordinary constructed type received a fabricated discriminant"
      let layout ← CompilerDiscriminantFacts.discriminantLayout context ty
      unless layout.ty == document.queries.primitives.u8 do throw "ordinary discriminant type is not exact u8"
    unless (← CompilerDiscriminantFacts.adtVariantCount context adt) == 1 do
      throw "constructed struct lost raw variant count")
  let (tupleLayout,world) ← arrayMust (RuntimeArrayTypes.lookup world tuple)
  let (padding,world) ← run (CompilerCopy.hasPadding runtime access true tupleLayout) world
  unless !padding do throw (IO.userError "actual pair-of-u32 tuple unexpectedly has padding")
  let (pointerLayout,world) ← arrayMust (RuntimeArrayTypes.perform world do
    let element := document.queries.primitives.u32
    let slice ← TypeArena.World.internType (.slice element)
    let pointer ← TypeArena.World.internType (.rawPointer slice .Mut)
    RuntimeMetadata.layoutInWorld runtime pointer)
  let corrupt := {pointerLayout with layout := {pointerLayout.layout with size := Size.ofBytes 32}}
  match CompilerCopy.hasPadding runtime access true corrupt world with
  | .error (.invalidProgram "wide pointer scalar sizes disagree with layout") _ => pure ()
  | _ => throw (IO.userError "declared wide pointer lost its debug invariant check")
  let tuplePhysical := {corrupt with ty := tuple}
  let (padding,_) ← run (CompilerCopy.hasPadding runtime access true tuplePhysical) world
  unless padding do throw (IO.userError "physical pointer-shaped data overrode declared tuple identity")
  IO.println "PASS new tuple/ADT discriminants, retained World effects and exact-kind padding controls"
