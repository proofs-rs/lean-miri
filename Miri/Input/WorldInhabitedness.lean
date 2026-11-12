import Miri.Input.RuntimeMetadata
import Miri.Input.WorldNormalization

/-! Pinned inhabitedness/mod.rs::OpsemInhabitedCtx, including the definition
seen-set and stop-at-reference cycle rule. This query-local memo is discarded
on return; only genuine constructor interning effects remain in World. -/
namespace Miri.Input.WorldInhabitedness
open TypeArena
private abbrev Key := TypeId × List DefinitionRef × Bool
private abbrev QueryM := StateT (Std.HashMap Key Bool) WorldM
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def capture (args : Array MIR.GenericArg) (synthetics offset : Nat) : Except String TypeId := do
  unless args.size >= synthetics do throw "inhabitedness capture arguments absent"
  unless (args.toList.drop (args.size - synthetics)).all
      (fun arg => match arg with | .Type _ => true | _ => false) do
    throw "inhabitedness synthetic capture argument is not a type"
  let some (.Type id) := args[args.size - offset]? | throw "inhabitedness capture tuple absent"
  pure id

private def visit (metadata : RuntimeMetadata) (seen : List DefinitionRef) (stopAtRef : Bool) :
    Nat → TypeId → QueryM Bool
  | 0, _ => throw "world inhabitedness traversal exhausted"
  | fuel + 1, input => do
    if let some result := (← get)[(input,seen,stopAtRef)]? then return result
    let result ← do
      let id ← liftM (WorldNormalization.normalizeType metadata.normalizationContext 10000 (fuel + 1) input)
      let world ← liftM (get : WorldM World)
      let view ← lift (world.lookupType id)
      if seen.isEmpty && !stopAtRef then
        if let .material source := view then
          if let some facts := source.compilerFacts then
            unless facts.typingEnvironment == "fully_monomorphized" do throw "inhabitedness material environment mismatch"
            if let some (_,result) := facts.booleanQueries.find? (·.1 == "opsem_inhabited") then return result
      let recurse := visit metadata seen stopAtRef fuel
      let kind ← lift (world.shapeKind id)
      match kind with
      | .never => return false
      | .int | .uint | .float | .bool | .char | .str | .foreign | .rawPointer
      | .functionPointer | .functionDefinition | .dynamicTraitObject | .slice => return true
      | _ => pure ()
      if let .material source := view then
        match source.shape with
        | .patternType base _ => return ← recurse base
        | .unsafeBinder .. =>
          let some facts := source.compilerFacts | throw "inhabitedness binder erasure material absent"
          let some (_,some inner) := facts.typeQueries.find? (·.1 == "unsafe_binder_erased")
            | throw "inhabitedness residual binder erasure absent"
          return ← recurse inner
        | _ => pure ()
      let constructor ← match view with
        | .constructed constructor => pure constructor
        | .material source => do
          let some constructor ← lift (world.materialKey source)
            | throw "inhabitedness source constructor unavailable"
          pure constructor
      match constructor with
      | .reference child .. => if stopAtRef then pure true else recurse child
      | .tuple children =>
        for child in children do unless ← recurse child do return false
        pure true
      | .array child _ =>
        let count ← liftM (RuntimeMetadata.arrayCountInWorld metadata id)
        if count == 0 then pure true else recurse child
      | .closure _ args => recurse (← lift (capture args 3 1))
      | .coroutineClosure _ args => recurse (← lift (capture args 4 2))
      | .coroutine .. => throw "constructed coroutine inhabitedness requires its exact source upvar decomposition"
      | .adt identity _ =>
        let declaration ← liftM (RuntimeMetadata.adtDeclarationInWorld metadata id)
        if declaration.kind == .unionKind then return true
        let definition ← lift (world.definitionRef identity)
        let already := seen.contains definition
        let seen := if already then seen else definition :: seen
        let stop := stopAtRef || already
        for variant in [:declaration.variantCount] do
          let count := (declaration.fields.filter (·.variantIndex == variant)).size
          let mut inhabited := true
          for field in [:count] do
            let child ← liftM (RuntimeMetadata.fieldTypeInWorld metadata id variant field)
            unless ← visit metadata seen stop fuel child do
              inhabited := false
              break
          if inhabited then return true
        pure false
      | .alias .. => throw "inhabitedness alias remained unresolved"
      | _ => throw "world inhabitedness constructor projection incomplete"
    modify fun memo => memo.insert (input,seen,stopAtRef) result
    pure result

def query (metadata : RuntimeMetadata) (fuel : Nat) (id : TypeId) : WorldM Bool := do
  let (result,_) ← (visit metadata [] false fuel id).run {}
  pure result

end Miri.Input.WorldInhabitedness
