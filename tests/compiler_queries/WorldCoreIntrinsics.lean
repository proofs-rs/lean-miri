import Miri.Input.Decoder
import Miri.Input.CompilerCoreIntrinsic
import Miri.Input.EvalProjectionMachine

open Lean Miri.Input Miri.Interpreter TypeArena
private def must [ToString ε] (value : Except ε A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def count (p : CompilerProviders.Prepared) (world : World) (ty : TypeId) : IO Nat :=
  must ((CompilerCoreIntrinsic.variantCountInWorld p world ty).mapError reprStr)
private def invalid (value : Except StepError Nat) (expected : String) : IO Unit :=
  match value with
  | .error (.invalidProgram message) => check (message == expected) "wrong variant_count source error"
  | _ => throw (IO.userError "variant_count did not preserve invalidProgram")
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ next => next⟩

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current sealed source")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let prepared ← must (CompilerProviders.prepare (← must (lowerProgram document)))
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let empty ← must (World.ofMaterial #[] #[] document.definitions #[] initial.arena.pointerBytes)
  -- No layout catalogue or closed type prefix is available to the count query.
  let noResults := {runtime with source := {document with types := #[],typeConstants := #[],predicates := #[],layouts := #[]},checkedMaterial := none,denseTypes := none}
  let prepared := {prepared with runtime := noResults}
  let mut novel := empty
  let mut adts := 0
  for node in document.types do
    if let .adt declaration := node.shape then
      let expected := declaration.variants.size
      check ((← count prepared initial.arena node.id) == expected) "material variant count differs"
      let term ← must (GenericInstantiationWorld.ofType initial.arena 16384 node.id)
      let (fresh,next) ← must ((GenericInstantiationWorld.resolveType 16384 term).run novel)
      novel := next
      check ((← count prepared novel fresh) == expected) "constructed variant count differs"
      let (pattern,next) ← must ((World.internType (.patternType fresh .notNull)).run novel)
      novel := next
      check ((← count prepared novel pattern) == expected) "one Pat did not preserve raw variant count"
      let (nested,next) ← must ((World.internType (.patternType pattern .notNull)).run novel)
      novel := next
      invalid (CompilerCoreIntrinsic.variantCountInWorld prepared novel nested)
        "source invariant: invalid nested pattern/bound type in variant_count"
      adts := adts + 1
  check (adts > 0) "no actual ADT declarations exercised"
  let (byte,next) ← must ((World.internType (.integer false .u8)).run novel)
  novel := next
  let (pointer,next) ← must ((World.internType (.rawPointer byte .Mut)).run novel)
  novel := next
  check ((← count prepared novel pointer) == 0) "raw pointer variant count was not zero"
  let state := {initial with arena := novel}
  let projectionFacts := prepared.lifecycle.calls.symbols.facts
  let (slice,withSlice) ← must ((World.internType (.slice byte)).run novel)
  match EvalProjectionMachine.dynamicKind projectionFacts {state with arena := withSlice} slice with
  | .ok .slice => pure ()
  | _ => throw (IO.userError "actual dynamic projection classifier lost constructed slice")
  let some dynamicOwner := document.definitions[0]? | throw (IO.userError "no dynamic owner")
  let predicate : DynamicPredicate.Predicate := ⟨#[],.autoTrait ⟨dynamicOwner.crateIndex,dynamicOwner.index⟩⟩
  let (dynamic,withDynamic) ← must ((World.internType (.dynamic ⟨#[predicate],.Erased⟩)).run withSlice)
  match EvalProjectionMachine.dynamicKind projectionFacts {state with arena := withDynamic} dynamic with
  | .error (.obligation "dynamic predicate trait source missing or ambiguous") => pure ()
  | _ => throw (IO.userError "constructed dynamic predicate boundary changed")
  let facts := prepared.lifecycle.calls.symbols.facts.context
  match CompilerExecutionProviders.worldInteger access facts byte state with
  | .ok kind after =>
    check (kind == .u8 && after.arena.typeCount == novel.typeCount && after.arena.constantCount == novel.constantCount) "actual integer runtime provider changed identity"
  | .error error _ => throw (IO.userError (reprStr error))
  let some definition := document.definitions[0]? | throw (IO.userError "no physical definition")
  let (alias,next) ← must ((World.internType (.alias .projection false
    ⟨definition.crateIndex,definition.index⟩ #[])).run novel)
  novel := next
  invalid (CompilerCoreIntrinsic.variantCountInWorld prepared novel alias) "TooGeneric in variant_count"
  check (novel.materialTypes.isEmpty && novel.materialConstants.isEmpty && novel.materialPredicates.isEmpty)
    "queries acquired closed source prefixes"
  IO.println s!"PASS {adts} material and {adts} empty-prefix constructed ADT counts; {adts} one-Pat counts and nested-Pat errors; pointer zero, alias invalidProgram, actual World integer provider and slice projection; explicit malformed dynamic source rejection; no layout catalogue"
