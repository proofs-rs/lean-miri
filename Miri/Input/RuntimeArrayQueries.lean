import Miri.Input.SourceCompilerArrays
import Miri.Interpreter.OsStrings
import Miri.Interpreter.ValidityVisitor

/-! Stateful consumers of canonical runtime array constructors. The accessors
must refer to one persistent interpreter World; reconstruction per call loses
canonical allocation of type identities. Memory/host actions remain unchanged.
-/
namespace Miri.Input.RuntimeArrayQueries
open Miri.ABI Miri.Interpreter
structure Access (S : Type) where
  get : S → RuntimeArrayTypes.World
  set : S → RuntimeArrayTypes.World → S
  sourceCompiler : Option (SourceCompilerWorld.Access S) := none
private def failure : RuntimeArrayTypes.Error → StepError
  | .metadata reason => .unsupported s!"runtime array compiler metadata: {reason}"
  | .missingRuntimeType id => .unsupported s!"missing canonical runtime array type {id}"
  | error => .invalidProgram s!"runtime array constructor/layout: {reprStr error}"
private def lift (value : Except RuntimeArrayTypes.Error A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (failure error)

/-- Refresh a checked array view from the same canonical World. Existing IDs
are verified before any snapshot is replaced. -/
def current (access : Access S) : EStateM StepError S RuntimeArrayTypes.World := do
  let state ← get
  if let some source := access.sourceCompiler then
    let some compiler := source.get state | throw (.unsupported "canonical array World unavailable")
    let arrays ← match SourceCompilerArrays.view (access.get state) compiler with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"canonical array view: {reason}")
    set (access.set state arrays)
    return arrays
  return access.get state

/-- Canonical constructor provider for EntryArguments and other runtime-sized
arrays, using the actual supplied element type identity and persistent World. -/
def arrayLayout (access : Access S) (element : MIR.TyId) (count : UInt64) :
    EStateM StepError S LocalLayout := do
  let state ← get
  if let some source := access.sourceCompiler then
    let some compiler := source.get state | throw (.unsupported "canonical array World unavailable")
    let (layout,arrays,compiler) ← match SourceCompilerArrays.internCached (access.get state) compiler element count with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"canonical array demand: {reason}")
    set (source.put (access.set state arrays) compiler)
    return layout
  let (layout,world) ← lift (RuntimeArrayTypes.internElement (access.get state) element count)
  set (access.set state world)
  pure layout

/-- OS-string constructors use the same canonical element IDs as other arrays. -/
def osStringArray (access : Access S) (wide : Bool) (count : UInt64) :
    EStateM StepError S LocalLayout := do
  let arrays := access.get (← get)
  arrayLayout access (if wide then arrays.wideLayout.ty else arrays.byteLayout.ty) count

def osStringsHooks (access : Access S) (base : OsStrings.Hooks P S Os Kind) :
    OsStrings.Hooks P S Os Kind :=
  { base with arrayLayout := fun wide count => do
      osStringArray access wide count }

def layoutOf (access : Access S) (id : MIR.TyId) : EStateM StepError S LocalLayout := do
  let world ← current access
  lift (RuntimeArrayTypes.lookup world id)

/-- Source array field type is the constructor's element type. This does not
infer an element from a stride, size, memory content or diagnostic spelling. -/
def fieldLayout (access : Access S) (base : LocalLayout → Nat → EStateM StepError S LocalLayout)
    (parent : LocalLayout) (index : Nat) : EStateM StepError S LocalLayout := do
  let world ← current access
  if world.entries.any (·.value.ty == parent.ty) then
    unless (← lift (RuntimeArrayTypes.lookup world parent.ty)) == parent do
      throw (.invalidProgram "canonical runtime array layout/type mismatch")
    lift (RuntimeArrayTypes.fieldLayout world parent.ty index)
  else base parent index

private def triviallyFreeze (world : RuntimeArrayTypes.World) (id : MIR.TyId) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match world.entries.find? (·.value.ty == id) with
    | some entry => match entry.key.element with
      | .u8 | .u16 => true
      | .compiler element => triviallyFreeze world element fuel
    | none => match world.metadata.node id with
      | .error _ => false
      | .ok source => match source.shapeKind with
        | .int | .uint | .float | .bool | .char | .str | .never | .reference
        | .rawPointer | .functionDefinition | .functionPointer => true
        | _ => false

/-- Bind classification for interned arrays; all other compiler leaves remain
mandatory. Portable memory/validation actions still execute in the base hooks. -/
def validityHooks (access : Access S) (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  { base with
    classify := fun choice ty => do
      let world ← current access
      if world.entries.any (·.value.ty == ty) then
        let (_,element) ← lift (RuntimeArrayTypes.arrayInfo world ty)
        pure (.sequence element.ty)
      else base.classify choice ty
    isFreeze := fun choice ty => do
      let world ← current access
      if world.entries.any (·.value.ty == ty) then
        -- Source's trivial-freeze path recurses through constructed arrays
        -- and accepts primitive scalars/references/pointers. Other element
        -- families still require the real compiler Freeze query.
        if triviallyFreeze world ty (world.entries.size + world.metadata.source.types.size + 1) then
          pure true
        else base.isFreeze choice ty
      else base.isFreeze choice ty }
end Miri.Input.RuntimeArrayQueries
