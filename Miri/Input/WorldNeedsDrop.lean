import Miri.Input.RuntimeMetadata
import Miri.Input.WorldNormalization
import Miri.Input.StructuralNeedsDrop

namespace Miri.Input.WorldNeedsDrop
open TypeArena
private abbrev QueryM := StateT (Std.HashMap TypeId Bool) WorldM
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error
private def capture (args : Array MIR.GenericArg) (synthetics offset : Nat) : Except String TypeId := do
  unless args.size >= synthetics do throw "needs_drop capture arguments absent"
  unless (args.toList.drop (args.size - synthetics)).all
      (fun arg => match arg with | .Type _ => true | _ => false) do
    throw "needs_drop synthetic capture argument is not a type"
  let some (.Type id) := args[args.size - offset]? | throw "needs_drop capture tuple absent"
  pure id

/-- Source synchronous drop components. The memo belongs to one query, rather
than to the execution universe or another execution's compiler state. -/
private def visit (metadata : RuntimeMetadata) : Nat → TypeId → QueryM Bool
  | 0, _ => throw "world needs_drop traversal exhausted"
  | fuel + 1, input => do
    if let some result := (← get)[input]? then return result
    let result ← do
      let id ← liftM (WorldNormalization.normalizeType metadata.normalizationContext 10000 (fuel + 1) input)
      let world ← liftM (get : WorldM World)
      let view ← lift (world.lookupType id)
      if let .material source := view then
        if let some facts := source.compilerFacts then
          unless facts.typingEnvironment == "fully_monomorphized" do throw "needs_drop material environment mismatch"
          if let some (_,result) := facts.booleanQueries.find? (·.1 == "needs_drop") then return result
      let kind ← lift (world.shapeKind id)
      if let some result := StructuralNeedsDrop.knownKindResult kind then return result
      if kind == .dynamicTraitObject || kind == .coroutine then return true
      let recurse := visit metadata fuel
      if let .material source := view then
        match source.shape with
        | .patternType child _ | .slice child => return ← recurse child
        | .unsafeBinder .. =>
          let some facts := source.compilerFacts | throw "needs_drop binder erasure material absent"
          let some (_,some inner) := facts.typeQueries.find? (·.1 == "unsafe_binder_erased")
            | throw "needs_drop residual binder erasure absent"
          return ← recurse inner
        | _ => pure ()
      let constructor ← match view with
        | .constructed constructor => pure constructor
        | .material source => do
          let some constructor ← lift (world.materialKey source)
            | throw "needs_drop source constructor unavailable"
          pure constructor
      match constructor with
      | .tuple children =>
        for child in children do if ← recurse child then return true
        pure false
      | .slice child => recurse child
      | .array child _ =>
        if (← liftM (RuntimeMetadata.arrayCountInWorld metadata id)) == 0 then return false
        recurse child
      | .closure _ args => recurse (← lift (capture args 3 1))
      | .coroutineClosure _ args => recurse (← lift (capture args 4 2))
      | .adt identity _ =>
        let declaration ← liftM (RuntimeMetadata.adtDeclarationInWorld metadata id)
        if declaration.langItem == some "manually_drop" then return false
        let definition ← lift (world.definitionRef identity)
        let some source := world.definitions[definition]? | throw "needs_drop ADT definition absent"
        let some drop := source.adtDrop | throw "needs_drop raw destructor declaration absent"
        if let some destructor := drop.destructor then
          unless destructor < world.definitions.size do throw "needs_drop destructor identity absent"
          return true
        if declaration.kind == .unionKind then return false
        for variant in [:declaration.variantCount] do
          let count := (declaration.fields.filter (·.variantIndex == variant)).size
          for field in [:count] do
            let child ← liftM (RuntimeMetadata.fieldTypeInWorld metadata id variant field)
            if ← recurse child then return true
        pure false
      | .alias .. => throw "needs_drop alias remained unresolved"
      | _ => throw "world needs_drop constructor projection incomplete"
    modify fun memo => memo.insert input result
    pure result

def query (metadata : RuntimeMetadata) (fuel : Nat) (id : TypeId) : WorldM Bool := do
  let (result,_) ← (visit metadata fuel id).run {}
  pure result

end Miri.Input.WorldNeedsDrop
