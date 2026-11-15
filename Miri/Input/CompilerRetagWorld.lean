import Miri.Interpreter.ValidityMachine
import Miri.Input.CompilerValidityWorld
import Miri.Input.SourceCompilerAutoTraits
import Miri.Input.SourceCompilerCasts
import Miri.Interpreter.TypedRetag

/-! Retag compiler leaves over the shared current World. Shape tests are exact
constructor tests; ADT/Box/lang-item roles and nontrivial trait selection remain
unsupported without source evidence. Auto traits use the shared source solver,
including its pinned structural fast paths and checked closure evidence. -/
namespace Miri.Input.CompilerRetagWorld
open Miri.Interpreter Miri.TreeBorrows
abbrev World := SourceCompilerWorld.World
private def node (world : World) (id : Nat) : Except String TypeNode := do
  let some value := world.canonical.types[id]? | throw "Invalid source retag type handle"
  unless value.id == id do throw "Invalid source retag type/index identity"
  return value

def typeShape (world : World) (id : Nat) : Except String RetagPipeline.RetagTypeShape := do
  match (← node world id).shape with
  | .reference .. => pure ⟨false,true,false,false⟩
  | .rawPointer .. => pure ⟨false,false,true,false⟩
  | .adt _ | .alias .. => throw "Unsupported source retag ADT/Box role"
  | _ => pure ⟨false,false,false,false⟩

def referencePointee (world : World) (id : Nat) : Except String (Nat × MIR.Mutability) := do
  let .reference pointee mutable _ := (← node world id).shape
    | throw "Invalid source reference-pointee query on non-reference"
  let _ ← node world pointee
  return (pointee,mutable)

def builtinDeref (world : World) (id : Nat) : Except String Nat := do
  let some pointee ← SourceCompilerCasts.builtinDeref world id true
    | throw "Invalid source retag builtin-deref query on non-pointer"
  return pointee

private def source (access : SourceCompilerWorld.Access (ValidityMachine.State K U))
    (operation : World → Except String A) : ValidityMachine.M K U A := do
  let some world := access.get (← get) | throw (.unsupported "source retag World unavailable")
  let some _ := world.canonical.sourceMaterial | throw (.unsupported "source retag material unavailable")
  match operation world with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"source retag query: {reason}")

def dynamicPredicates (prepared : CompilerFactAdapters.Prepared)
    (access : SourceCompilerWorld.Access (ValidityMachine.State K U)) (id : Nat) :
    ValidityMachine.M K U PredicateList := do
  if prepared.context.runtime.source.sourceMaterial.isSome then
    source access fun world => do
      let .dynamicTraitObject predicates .. := (← node world id).shape
        | throw "Invalid source freeze dyn-unpack type"
      pure predicates
  else
    match CompilerFactAdapters.validityKind prepared id with
    | .ok (.dynamic predicates) => pure predicates
    | .ok _ => throw (.invalidProgram "freeze dyn unpack on non-dynamic compiler type")
    | .error reason => throw (.unsupported reason)

def hooks (prepared : CompilerFactAdapters.Prepared)
    (access : SourceCompilerWorld.Access (ValidityMachine.State K U))
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U)) :
    TypedRetag.Hooks K (ValidityMachine.UserState U) :=
  if !prepared.context.runtime.source.sourceMaterial.isSome then base else
  {base with
    instanceDefinition := fun id => source access fun world => do
      let value ← SourceCompilerWorld.node world id
      let definition := value.instanceKind.defId
      let some _ := world.canonical.definitions[definition]? | throw "Invalid source retag instance DefId"
      return definition
    typeShape := fun id => source access (typeShape · id)
    referencePointee := fun id => source access (referencePointee · id)
    builtinDeref := fun id => source access (builtinDeref · id)
    isUnpin := fun id => source access (SourceCompilerAutoTraits.check · .unpin id)
    isUnsafeUnpin := fun id => source access (SourceCompilerAutoTraits.check · .unsafeUnpin id)
    typeIsFreeze := fun id => source access (SourceCompilerAutoTraits.check · .freeze id)
    rustcNoWritable := fun _ => throw (.unsupported "source rustc_no_writable declaration attribute unavailable")
    freeze := {base.freeze with
      isUnsafeCell := fun id => source access fun world => do
        match (← node world id).shape with
        | .adt _ | .alias .. => throw "Unsupported source UnsafeCell lang-item role"
        | _ => pure false
      typeIsFreeze := fun id => source access (SourceCompilerAutoTraits.check · .freeze id)
      isDynamic := fun id => source access fun world => return (← node world id).shapeKind == .dynamicTraitObject
      isBox := fun id => source access fun world => do
        match (← node world id).shape with
        | .adt _ | .alias .. => throw "Unsupported source Box lang-item role"
        | _ => pure false
      isTooGeneric := fun id => source access fun world => do
        -- Pinned visitor kind test (Param/Alias/Bound/Placeholder/Infer/Error),
        -- not a recursive monomorphization query. Only Alias has a canonical
        -- constructor in this input type model; unsupported syntax cannot intern.
        match (← node world id).shape with
        | .alias .. => pure true
        | _ => pure false } }
/-- Source-mode Freeze reads the actual World and preserves machine state.
The premise is the pure trait computation on that World, never a successful
retag/memory operation or a result borrowed from a prepared dictionary. -/
theorem typeIsFreeze_at (prepared : CompilerFactAdapters.Prepared)
    (access : SourceCompilerWorld.Access (ValidityMachine.State K U))
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (state : ValidityMachine.State K U) (world : World) (material : SourceMaterial)
    (id : Nat) (value : Bool)
    (mode : prepared.context.runtime.source.sourceMaterial.isSome = true)
    (present : access.get state = some world)
    (materialAt : world.canonical.sourceMaterial = some material)
    (computed : SourceCompilerAutoTraits.check world .freeze id = .ok value) :
    (hooks prepared access base).typeIsFreeze id state = .ok value state := by
  simp [hooks, mode, source, present, materialAt, computed, get, getThe,
    MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

end Miri.Input.CompilerRetagWorld
